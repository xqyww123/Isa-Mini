"""Generic API driver for IsaMini.AoA.

Owns the agent loop directly, calling LLM chat completion APIs rather than
delegating to an external agent framework. Supports any OpenAI-compatible
endpoint via the Provider abstraction.
"""

from __future__ import annotations

import asyncio
import contextvars
import json
import os
import random
import shutil
import tempfile
from abc import ABC, abstractmethod
from dataclasses import dataclass
from time import time
from typing import Any, Callable

from .model import *
from .language_model_driver import (
    LMDriver, _TransientError, _CorruptedSampleError, _QuotaError, Usage)

from .mcp_http_server import ToolExecutor
from .helper import MyIO


# ============================================================================
# Provider Data Types
# ============================================================================

@dataclass
class ToolCall:
    id: str
    name: str
    arguments: str  # raw JSON string from API


@dataclass
class ProviderResponse:
    content: str | None
    thinking: str | None
    tool_calls: list[ToolCall]
    usage: Usage
    response_id: str | None = None


# ============================================================================
# Message Abstraction
# ============================================================================

@dataclass
class SystemMsg:
    content: str

@dataclass
class UserMsg:
    content: str

@dataclass
class AssistantMsg:
    response: ProviderResponse
    native: Any = None

@dataclass
class ToolResultMsg:
    call_id: str
    name: str
    content: str

Msg = SystemMsg | UserMsg | AssistantMsg | ToolResultMsg


# ============================================================================
# Provider ABC
# ============================================================================

class Provider(ABC):
    """Format-agnostic LLM provider interface.

    Each provider converts ``list[Msg]`` to its native format inside
    ``chat()``.  The driver never inspects message internals.
    """

    # Logging hook for a provider's internal retry loop (Layer 2). The driver injects
    # its ``warn_AoA_opr`` here so transient-error handling is logged;
    # defaults to a no-op for providers used outside a driver, and for providers that
    # never retry internally. ``staticmethod`` so that reading it off an instance does
    # not bind ``self`` as the message argument.
    _log: Callable[[str], None] = staticmethod(lambda _m: None)

    @abstractmethod
    async def chat(self, messages: list[Msg], tools: list[dict],
                   *, previous_response_id: str | None = None,
                   allowed_tools: list[str] | None = None) -> ProviderResponse:
        # Drivers must never call this directly: go through
        # APIDriver._checked_chat, which applies entry validation.
        ...

    @abstractmethod
    def format_tools(self, tool_info: dict[str, dict[str, Any]]) -> list[dict]:
        """Convert {name: {"description": ..., "schema": ...}} to provider-specific tool format."""
        ...

    @abstractmethod
    def format_assistant_msg(self, response: ProviderResponse) -> AssistantMsg:
        """Build an AssistantMsg to append to history."""
        ...

    @property
    @abstractmethod
    def context_window(self) -> int:
        ...

    @property
    @abstractmethod
    def model_name(self) -> str:
        ...

    @abstractmethod
    def pricing(self) -> dict[str, float]:
        """Returns {"input": rate, "cached": rate, "output": rate} per token."""
        ...

    @staticmethod
    def validate_tool_call_json(tool_calls: list[ToolCall]) -> None:
        """Reject a turn whose tool-call ``arguments`` is not parseable JSON.

        A provider can occasionally emit malformed tool-call arguments — e.g.
        two concatenated objects when streaming deltas reuse a tool-call
        ``index`` (decodes as "Extra data"). Raising ``_TransientError`` here
        lets the caller's ``_retry_transient`` re-request the turn rather than
        crashing the run on the downstream ``json.loads`` in
        ``_execute_tool_calls``. The OpenAI Chat and Responses providers call
        this before returning; ``driver_anthropic`` performs the equivalent
        check inline while accumulating ``input_json_delta``.
        """
        for tc in tool_calls:
            try:
                json.loads(tc.arguments)
            except json.JSONDecodeError as e:
                raise _TransientError(
                    f"provider returned malformed tool-call arguments for "
                    f"'{tc.name}': {e}") from e




# ============================================================================
# APIDriver — Generic Agent Loop
# ============================================================================

COMPACTION_PROMPT = """\
You have written a partial proof for the initial proof goal.
Please summarize your idea and the progress into the following sections.
This summary will replace the conversation history above and serve as your \
only context for continuing the proof — anything not included will be lost.

Summary template:
```
## Proof Plan
Your current proof strategy in detail — the overall approach and how the \
remaining subgoals fit into it.

## Attempts
Approaches tried so far: what succeeded, what failed and why. \
Explicitly note any dead ends that should not be retried.

## Key Insights
Important observations about the proof structure, useful lemmas or \
facts discovered, type information, etc.

## Next Steps
What to do next based on current progress.
```"""


class _CompactionFailed(Exception):
    """The compaction summary request failed; ``cause`` carries the real
    error. Purely local control flow: raised by ``_compact`` and caught by
    ``_api_loop``'s two compaction call sites, two frames away with nothing in
    between — so it takes no family base. NOT an ``AoA_Error`` (whole-body
    ``except AoA_Error`` tool handlers would swallow it), and NOT a
    ``Chat_Restart``: that base asserts the context MUST restart, whereas here
    the restart is ``_restart_after``'s decision and on the capped and
    wall-clock legs no restart happens. Local to this driver — compaction is
    an ``APIDriver`` mechanism; ClaudeCode has none."""

    def __init__(self, cause: BaseException):
        super().__init__(str(cause))
        self.cause = cause


class APIDriver(LMDriver):
    """Agent driver that owns the chat loop, calling Provider.chat() directly."""

    COMPACTION_THRESHOLD = 0.80
    COMPACTION_RECENT_ROUNDS = 3
    DEFAULT_MODEL: str = ""
    FORK_CHEAPER_MODEL: str | None = None
    # Opt-in (env AOA_ASSUME_PERFECT_CACHE) "perfect input cache" cost
    # accounting — only the codex stateless full-resend driver enables it.
    # See _cache_assumed_usage.
    _assume_perfect_cache: bool = False
    _prev_prompt_total: int = 0
    _prev_output_tokens: int = 0

    working_dir: str
    YAML_path: str
    _fork_counter: int
    _fork_name: str

    def __str__(self) -> str:
        return f"{self._driver_name}({self._provider.model_name})"

    def __init__(self, *args, provider: Provider,
                 parent: 'APIDriver | None' = None, **kwargs):
        super().__init__(*args, parent=parent, **kwargs)
        self._provider = provider
        # Route the provider's internal-retry logging (Layer 2) to this
        # driver's warning log so transient errors are recorded.
        self._provider._log = self.warn_AoA_opr
        self._messages: list[Msg] = []
        self._interrupted = False
        # _executor is declared by Session.__init__ (shared field, see there);
        # `initialize` builds it.
        self._fork_counter = 0
        self._model_time_start: float | None = None
        self._last_response_id: str | None = None
        self._msgs_sent_through: int = 0

        if parent is not None:
            self.working_dir = parent.working_dir
            self.YAML_path = parent.YAML_path
            self.root = parent.root
            parent._fork_counter += 1
            self._fork_name = f"{parent._fork_name}.fork_{parent._fork_counter}"
        else:
            self.working_dir = tempfile.mkdtemp(prefix="agent_AoA_api_")
            if not os.access(self.working_dir, os.R_OK | os.W_OK):
                raise InternalError(
                    f"Working directory {self.working_dir} is not readable and writable.")
            self.YAML_path = os.path.join(self.working_dir, "proof.yaml")
            self._fork_name = "main"

    @classmethod
    def _make_fork(cls, parent: 'APIDriver', role=None) -> 'APIDriver':
        from .model import _session_var
        try:
            current = _session_var.get()
        except LookupError:
            current = None
        if current is not None:
            raise InternalError(
                "_make_fork must be called in a fresh context")
        return cls(provider=parent._provider, parent=parent, role=role)

    async def initialize(self, root: Root):
        await super().initialize(root)
        self._executor = ToolExecutor(self)
        # Seed proof.yaml. `refresh_YAML` -> `print_proof_scope`, which renders
        # the full `root` for a major (non-worker) and the scoped view for a
        # worker — so a single call covers both. Interaction forks are neither
        # and intentionally write no YAML.
        if self.is_major or self.is_worker:
            self.refresh_YAML()

    async def interrupt(self):
        self._interrupted = True

    async def close(self):
        await super().close()
        if self.is_major and hasattr(self, 'working_dir') and os.path.exists(self.working_dir):
            try:
                shutil.rmtree(self.working_dir)
                self.debug_info(f"[CLEANUP] Removed temporary directory: {self.working_dir}")
            except Exception as e:
                self.debug_info(f"[CLEANUP] Failed to remove {self.working_dir}: {e}")

    def refresh_YAML(self):
        with open(self.YAML_path, 'w', encoding="utf-8") as f:
            self.print_proof_scope(0, MyIO(f), update_line=True, show_warnings=True)

    # ------------------------------------------------------------------
    # Main Agent Loop
    # ------------------------------------------------------------------

    async def _initial_messages(self) -> list[Msg]:
        msgs: list[Msg] = []
        sp = self.system_prompt()
        if sp is not None:
            msgs.append(SystemMsg(sp))
        msgs.append(UserMsg(await self.initial_prompt()))
        return msgs

    async def _run_agent_loop(self):
        await self._with_retry(self._api_loop)

    # --- "assume input cache" notional cost model (env AOA_ASSUME_PERFECT_CACHE) ---
    # codex's ChatGPT-subscription prompt cache is best-effort/intermittent
    # (per-machine routing + eviction); a stateless full-resend turn that re-sends
    # the whole prior transcript often reports cached_tokens=0, inflating cost.
    # When ON, we model a realistic cache instead of trusting the flaky real one.
    _CACHE_MISS_P     = 0.072321   # P(hard miss this turn) -> sim cached = 0
    _CACHE_LT70_P     = 0.18561    # P(turn < 70%); soft band [_CACHE_MISS_P, this) -> U(50,70)% (width 0.073289)
    _CACHE_TRUST_REAL = 0.80       # real rate >= this -> trust real verbatim
    _CACHE_BLEND_REAL = 0.50       # real rate in [this, TRUST) -> 0.3*real + 0.7*sim; below -> 100% sim

    def _cache_assumed_usage(self, usage: Usage, prev_prompt_total: int,
                             prev_output: int) -> tuple[Usage, int]:
        """Rewrite ``usage.cached_tokens`` to a NOTIONAL value modelling input
        caching, returning ``(usage, this_call_prompt_total)`` (caller threads the
        prompt total back as ``prev_prompt_total`` next turn; tracks ``prev_output``
        separately). OFF by default ⇒ usage returned unchanged (byte-identical).

        Pipeline (only when ``self._assume_perfect_cache``):
          1. idealB (perfect prefix, never 100%): the resent prefix
             ``min(prev_prompt_total, cur)`` is credited as cached — but capped at
             ``cur - prev_output`` so this turn's genuinely-new content (>= the
             prior model output, never seen before) stays fresh.
          2. sim: degrade idealB by the measured random drop pattern — hard miss
             (cached 0) w.p. _CACHE_MISS_P; soft (50-70% of cur) in the nested band;
             else idealB. Fully random (non-reproducible by design).
          3. tiered blend by this turn's REAL cache rate rp = real/cur:
             rp >= TRUST -> real;  BLEND <= rp < TRUST -> 0.3*real+0.7*sim;
             rp < BLEND -> sim (100% modelled).
        The first turn after any reset (prev_prompt_total == 0: loop start /
        compaction / refresh / restart) has no resent prefix, so it is left genuine.
        The adjusted cached flows through the normal cost pipeline (_compute_cost
        bills cached at the cached rate). NOTE: when ON this overwrites the real
        cache split, so the token ledger reports notional cache counts."""
        prompt_total = (usage.input_tokens + usage.cached_tokens
                        + usage.cache_creation_tokens)
        if not self._assume_perfect_cache or prev_prompt_total <= 0 or prompt_total <= 0:
            return usage, prompt_total
        real = usage.cached_tokens
        # 1. idealB: perfect prefix, keep this turn's new content fresh (never 100%)
        theoretical = min(prev_prompt_total, prompt_total)
        ideal = min(max(real, theoretical), max(0, prompt_total - prev_output))
        # 2. sim: random degradation of idealB
        r = random.random()
        if r < self._CACHE_MISS_P:
            sim = 0
        elif r < self._CACHE_LT70_P:
            sim = int(random.uniform(0.50, 0.70) * prompt_total)
        else:
            sim = ideal
        # 3. tiered blend by real cache rate
        rp = real / prompt_total
        if rp >= self._CACHE_TRUST_REAL:
            effective = real
        elif rp >= self._CACHE_BLEND_REAL:
            effective = round(0.3 * real + 0.7 * sim)
        else:
            effective = sim
        effective = max(0, min(int(effective), prompt_total))  # bound: [0, prompt_total]
        usage = Usage.from_inclusive(
            prompt_tokens=prompt_total,
            output_tokens=usage.output_tokens,
            cached=effective,
            cache_creation=usage.cache_creation_tokens)
        return usage, prompt_total

    # --- Entry validation: the message list must never contain a lone surrogate ---

    def _validate_sample(self, response: ProviderResponse) -> None:
        """Reject a corrupted sample (a response containing a lone UTF-16
        surrogate — typically a surrogate pair split by per-delta streaming
        decode) BEFORE it can enter any message list; once in history it
        crashes every later request client-side (httpx serializes with strict
        UTF-8). Encoding is the ground truth, so probe the three raw string
        fields. The ``arguments`` probe is live only where ``arguments`` is
        the provider's raw wire text (the OpenAI providers); Anthropic and
        Gemini re-serialize with ``ensure_ascii=True``, so there it is ASCII
        by construction and poison survives in the *parsed native* payload
        instead — invisible here; the ``UnicodeEncodeError`` leg of
        ``_api_loop``'s merged arm bounds that residue on the main loop."""
        fields = [("content", response.content), ("thinking", response.thinking)]
        fields += [(f"tool_calls[{i}].arguments", tc.arguments)
                   for i, tc in enumerate(response.tool_calls)]
        for field, s in fields:
            if s is None:
                continue
            try:
                s.encode("utf-8")
            except UnicodeEncodeError as e:
                i = e.start
                split_pair = (i + 1 < len(s)
                              and '\ud800' <= s[i] <= '\udbff'
                              and '\udc00' <= s[i + 1] <= '\udfff')
                shape = "split_pair" if split_pair else "lone_half"
                self._log_meta("CORRUPTED_SAMPLE", field=field, position=i,
                               shape=shape,
                               excerpt=ascii(s[max(0, i - 60):i + 60]))
                raise _CorruptedSampleError(
                    f"corrupted sample: lone surrogate in {field} "
                    f"at position {i} ({shape})") from e

    async def _checked_chat(self, provider: Provider, messages: list[Msg],
                            tools: list[dict], **kwargs) -> ProviderResponse:
        """``Provider.chat`` behind entry validation — every chat seam that
        appends the response to a message list must go through here. Call it
        on the session that should own the ``CORRUPTED_SAMPLE`` meta (the
        fork, not the parent); *provider* is only the transport and may
        differ from that session's own (``_fork_provider``)."""
        response = await provider.chat(messages, tools, **kwargs)
        self._validate_sample(response)
        return response

    def _reset_prompt_cache(self) -> None:
        """The next request is a full prompt-cache miss on a fresh list: no
        response id to continue from, nothing sent through, no prior totals."""
        self._last_response_id = None
        self._msgs_sent_through = 0
        self._prev_prompt_total = 0
        self._prev_output_tokens = 0

    def _budget_left(self) -> float | None:
        """Seconds left on the wall-clock budget, for ``asyncio.timeout``.
        None while the budget clock has not started (no cap); negative once
        overshot (fires immediately)."""
        elapsed = self.elapsed_working_time()
        return None if elapsed is None else self.timeout_seconds - elapsed

    async def _restart_after(self, e: BaseException) -> None:
        """Charge one retry; restart the context unless max_retries (or another
        budget dimension) ended the session instead. Postcondition either way:
        this session is interrupted, so the inner loop cannot run another turn —
        callers decide only where to go, never whether to stop. request_restart
        interrupts on its own; the trailing call covers the CAPPED path: the
        Refresh caller sits in the OUTER loop and would otherwise `continue` into
        `while not self._interrupted` and spend one more turn on a context that
        could not be compacted. Same shape as ToolExecutor.execute's budget gate."""
        self._retry_count += 1
        if not self.check_budget():
            self.warn_AoA_opr(f"{type(e).__name__} on the model turn; "
                              f"restarting context: {e}")
            await self.request_restart()
        await self.interrupt()

    async def _api_loop(self):
        assert self._executor is not None
        if self._budget_start_time is None:
            self._budget_start_time = time()
        self._messages = await self._initial_messages()
        self._reset_prompt_cache()
        tools = self._provider.format_tools(self._executor.tool_schemas())

        while True:
            while not self._interrupted:
                if self._last_response_id is not None:
                    msgs_to_send = self._messages[self._msgs_sent_through:]
                else:
                    msgs_to_send = self._messages

                self._model_time_start = time()
                # Cap this model turn (INCLUDING transient retries) at the
                # remaining wall-clock budget. check_budget() only runs AFTER a
                # turn, so without this a single slow/stalled chat could
                # overshoot the deadline by up to max_stream_time (~1800s). The outer
                # asyncio.timeout injects CancelledError (NOT the TimeoutError
                # that chat() maps to a retriable stall), so it propagates out
                # of _retry_transient and surfaces here as TimeoutError.
                try:
                    async with asyncio.timeout(self._budget_left()):
                        response = await self._retry_transient(
                            lambda: self._checked_chat(
                                self._provider, msgs_to_send, tools,
                                previous_response_id=self._last_response_id))
                except LMUnreachable as e:
                    # Proxy down / creds expired (subscription mode): give up
                    # cleanly via quit_info instead of spinning or letting the
                    # exception escape. Terminal ⇒ the outer loop breaks.
                    self.settle_quit(ResourceUnavailable(detail=str(e)))
                    break
                except TimeoutError:
                    # Wall-clock budget ran out mid model turn. check_budget()
                    # now sees elapsed >= timeout_seconds and sets
                    # quit_info=ResourceExhausted (and logs); the explicit
                    # fallback covers any scheduling/clock-skew corner where it
                    # reads just under. Terminal ⇒ the outer loop breaks.
                    if not self.check_budget():
                        self.settle_quit(ResourceExhausted(
                            detail="model turn exceeded the remaining time budget"))
                    break
                except (_CorruptedSampleError, UnicodeEncodeError) as e:
                    # The merged arm. Two legs: a corrupted sample survived
                    # _retry_transient's re-rolls (in the no-op-override
                    # family it gets none at all); or — the UnicodeEncodeError
                    # leg — poison hidden in a parsed native payload hit the
                    # HTTP client's strict UTF-8 encode. _CorruptedSampleError
                    # must not fall through to _with_retry (unbounded, silently
                    # rebuilds the context); UnicodeEncodeError is no
                    # _TransientError at all — nothing else catches it and it
                    # would kill the whole run. Charge one retry and restart
                    # the context, capped by max_retries; the restart branch
                    # below deliberately does not reset _retry_count.
                    await self._restart_after(e)
                    break

                if response.response_id is not None:
                    self._last_response_id = response.response_id
                    self._msgs_sent_through = len(self._messages) + 1

                if self._model_time_start is not None:
                    self.total_model_time += time() - self._model_time_start
                    self._model_time_start = None
                adj_usage, self._prev_prompt_total = self._cache_assumed_usage(
                    response.usage, self._prev_prompt_total, self._prev_output_tokens)
                self._prev_output_tokens = response.usage.output_tokens
                self._accumulate_usage(adj_usage)

                if response.thinking:
                    self.log_model_thinking(response.thinking)
                if response.content:
                    self.log_model_output(response.content)

                self._messages.append(self._provider.format_assistant_msg(response))

                if response.tool_calls:
                    results = await self._execute_tool_calls(response.tool_calls)
                    for tc, (text, _is_error) in results:
                        self._messages.append(
                            ToolResultMsg(call_id=tc.id, name=tc.name, content=text))
                    if self.quit_info is not None:
                        break
                    if not self.proof_scope_unfinished_nodes():
                        break
                    if self.check_budget():
                        break
                else:
                    unfinished = self.proof_scope_unfinished_nodes()
                    if not unfinished:
                        break
                    self._retry_count += 1
                    if self.check_budget():
                        break
                    retry = self.retry_prompt(unfinished)
                    self._messages.append(UserMsg(retry))
                    self.log_retry(unfinished, retry)

                if self._should_compact(response.usage):
                    try:
                        self._messages = await self._compact(self._messages)
                    except _CompactionFailed as e:
                        await self._restart_after(e.cause)
                        break
                    self._reset_prompt_cache()

            if not isinstance(self.quit_info, (Restart, Refresh)):
                break

            if isinstance(self.quit_info, Refresh):
                refresh_info = self.quit_info
                # Consume the verdict BEFORE the fallible step: check_budget
                # short-circuits on a standing quit_info, blinding the retry cap.
                self._interrupted = False
                self.quit_info = None
                try:
                    self._messages = await self._compact(
                        self._messages,
                        recent_rounds=0,
                        append_briefing=refresh_info.briefing)
                except _CompactionFailed as e:
                    # Nothing below happened: no age bump, no cooldown
                    # consumed, briefing dropped (logged by _compact).
                    await self._restart_after(e.cause)
                    continue
                self.runtime.age += 1
                self._reset_prompt_cache()
                self._total_calls_at_last_refresh = self.total_tool_calls
                self.log_AoA_opr("Context refreshed")
                self._log_meta("REFRESH", briefing=refresh_info.briefing)
                continue

            self._interrupted = False
            self.quit_info = None
            self.refresh_YAML()
            self._messages = await self._initial_messages()
            self._reset_prompt_cache()
            self.log_AoA_opr("Context restarted")
            self._log_meta("CONTEXT_RESTART")

        self._compute_cost()
        self.log_proof()

    # ------------------------------------------------------------------
    # Tool Execution
    # ------------------------------------------------------------------

    async def _execute_tool_calls(self, tool_calls: list[ToolCall]) -> list[tuple[ToolCall, tuple[str, bool]]]:
        assert self._executor is not None
        results: list[tuple[ToolCall, tuple[str, bool]]] = []

        queries = [(tc, json.loads(tc.arguments)) for tc in tool_calls if tc.name == "query"]
        others = [(tc, json.loads(tc.arguments)) for tc in tool_calls if tc.name != "query"]

        if queries:
            query_results = await asyncio.gather(
                *[self._executor.execute(tc.name, args) for tc, args in queries])
            results.extend(zip([tc for tc, _ in queries], query_results))

        for tc, args in others:
            self._model_time_start = None
            r = await self._executor.execute(tc.name, args)
            results.append((tc, r))
            if self._interrupted:
                break

        self.total_tool_calls += len(results)
        return results

    # ------------------------------------------------------------------
    # Compaction
    # ------------------------------------------------------------------

    def _should_compact(self, usage: Usage) -> bool:
        # Full context occupancy = the entire prompt we just sent + the output
        # just generated (which becomes part of the next turn's prompt). The
        # three prompt partitions are mutually disjoint and sum to the real
        # prompt size (input_tokens is UNCACHED-only by the Usage invariant), so
        # cached/cache_creation MUST be added back — cached tokens still occupy
        # the context window even though they're cheap. Counting only uncached
        # input would undercount badly under heavy caching (e.g. DeepSeek) and
        # compact far too late, risking a context-overflow error.
        occupancy = (usage.input_tokens + usage.cached_tokens
                     + usage.cache_creation_tokens + usage.output_tokens)
        return occupancy > self._provider.context_window * self.COMPACTION_THRESHOLD

    async def _find_recent_start(self, messages: list[Msg]) -> int:
        rounds_seen = 0
        for i in range(len(messages) - 1, -1, -1):
            if isinstance(messages[i], AssistantMsg):
                rounds_seen += 1
                if rounds_seen == self.COMPACTION_RECENT_ROUNDS:
                    return i
        return len(await self._initial_messages())

    async def _compact(self, messages: list[Msg], *,
                       recent_rounds: int | None = None,
                       summary_label: str = "Previous progress",
                       append_briefing: str | None = None) -> list[Msg]:
        self.log_AoA_opr(
            f"Compaction triggered: {len(messages)} messages, "
            f"input={self.total_input_tokens} output={self.total_output_tokens}")

        # LearningTask reflection at the compaction seam (mirrors ClaudeCode
        # on_compact): distil experience before the context is summarized away.
        # No-op for a UsualTask / interaction fork; fail-fast (errors propagate).
        await self.maybe_run_memorize_interaction("pre_compact")

        effective_rounds = recent_rounds if recent_rounds is not None else self.COMPACTION_RECENT_ROUNDS
        if effective_rounds == 0:
            recent_messages: list[Msg] = []
        else:
            recent_start = await self._find_recent_start(messages)
            recent_messages = messages[recent_start:]

        # A fresh list, not append/pop: on the capped path the session ends
        # with self._messages as-is, and the session_end survey fork reads it
        # whole — a leftover COMPACTION_PROMPT must be impossible, not undone.
        request = messages + [UserMsg(COMPACTION_PROMPT)]
        # The guarded region is exactly the summary request: everything before
        # (memorize hook, recent-window search) and after propagates as usual.
        try:
            async with asyncio.timeout(self._budget_left()):
                summary_resp = await self._retry_transient(
                    lambda: self._checked_chat(self._provider, request, []))
        except _QuotaError:
            raise  # _with_retry's 20-minute wait, as on the main turn
        except Exception as e:
            # Broad on purpose: providers re-raise non-transient 4xx (e.g.
            # context length exceeded — the request most likely to hit it)
            # as their own types. Classified by which call failed, not by
            # type. CancelledError is a BaseException and passes through.
            # str(e), not repr: UnicodeEncodeError's repr embeds the whole
            # unencodable payload (here: the full serialized prompt).
            self.warn_AoA_opr("Compaction summary request failed "
                              f"({type(e).__name__}): {e}")
            self._log_meta("COMPACTION_FAILED", error=type(e).__name__,
                           detail=str(e),
                           briefing_dropped=append_briefing is not None)
            raise _CompactionFailed(e) from e
        summary = summary_resp.content or ""
        self._accumulate_usage(summary_resp.usage)

        self._reset_view_state()

        self.refresh_YAML()
        new_messages: list[Msg] = []
        sp = self.system_prompt()
        if sp is not None:
            new_messages.append(SystemMsg(sp))
        suffix = f"\n\n{summary_label}:\n" + summary
        if append_briefing is not None:
            suffix += "\n\nAgent's briefing:\n" + append_briefing
        new_messages.append(UserMsg(
            (await self.initial_prompt()) + suffix))
        new_messages.extend(recent_messages)
        est = self.estimate_tokens(new_messages)
        self.log_AoA_opr(f"Compacted to ~{est} tokens ({len(new_messages)} messages). Summary: {summary[:200]}...")
        self._log_meta("COMPACTION", summary=summary)
        return new_messages

    # ------------------------------------------------------------------
    # Forking
    # ------------------------------------------------------------------

    async def _do_fork(self, interaction: 'Interaction',
                       prompt_text: str) -> Any:
        ctx = contextvars.copy_context()
        task = asyncio.get_running_loop().create_task(
            self._run_fork(interaction, prompt_text), context=ctx)
        return await task

    def _fork_provider(self, mode: ForkingMode) -> Provider:
        """Select provider for fork (may use cheaper model)."""
        # Subclasses can override to return a different provider for cheaper forks
        return self._provider

    async def _run_fork(self, interaction: 'Interaction', prompt_text: str) -> Any:
        from .model import _session_var, Fork_Pending, Role_Interaction
        _session_var.set(None)  # type: ignore
        mode = interaction.forking
        fork = self.__class__._make_fork(self, role=Role_Interaction(
            pending=Fork_Pending(interaction, asyncio.get_running_loop().create_future()),
            prompt=prompt_text,
            resume_id=None,
            mode=mode,
        ))
        await fork.initialize(self.root)

        fork_response_id: str | None = None

        answer_tool = self.tool_name(interaction.answer_tool_name)
        if answer_tool not in prompt_text:
            prompt_text += (
                f"\nAnswer the question above by calling "
                f"the `{answer_tool}` tool.")

        fork_messages: list[Msg]
        if mode == ForkingMode.FORKING_WITH_CTXT:
            if self._last_response_id is not None:
                fork_response_id = self._last_response_id
                if (self._messages
                        and isinstance(self._messages[-1], AssistantMsg)
                        and self._messages[-1].response.tool_calls):
                    # Pending function_calls: the API requires a
                    # function_call_output (fco) before
                    # new input.  Embed prompt directly in fco content.
                    pending = self._messages[-1].response.tool_calls
                    fork_messages = [
                        ToolResultMsg(
                            call_id=tc.id, name=tc.name,
                            content=(prompt_text if i == 0
                                     else "Tool execution in progress. "
                                          "Please address the question above."))
                        for i, tc in enumerate(pending)]
                else:
                    # No pending function_calls: send unsent messages
                    # plus prompt as a normal user message.
                    fork_messages = list(
                        self._messages[self._msgs_sent_through:])
                    fork_messages.append(UserMsg(prompt_text))
            else:
                # No stored response — fall back to message copy.
                fork_messages = list(self._messages)
                if (fork_messages
                        and isinstance(fork_messages[-1], AssistantMsg)
                        and fork_messages[-1].response.tool_calls):
                    pending = fork_messages[-1].response.tool_calls
                    for i, tc in enumerate(pending):
                        fork_messages.append(ToolResultMsg(
                            call_id=tc.id, name=tc.name,
                            content=(prompt_text if i == 0
                                     else "Tool execution in progress. "
                                          "Please address the question above.")))
                else:
                    fork_messages.append(UserMsg(prompt_text))
        else:
            fork_messages = []
            sp = self.system_prompt()
            if sp is not None:
                fork_messages.append(SystemMsg(sp))
            fork_messages.append(UserMsg(prompt_text))

        # Use the PARENT's tool schemas so the API request shares the same
        # tools-prefix as the main loop.  This preserves DeepSeek-style automatic
        # prefix caching (tools are serialised before messages in the prompt).
        # The fork's _check_tool_permission already blocks disallowed tools at
        # execution time, so advertising extra tools is safe.
        all_schemas = self._executor.tool_schemas()
        fork_tools = self._provider.format_tools(all_schemas)

        fork_provider = self._fork_provider(mode)
        tag = f"[{fork._fork_name}]"
        fork.log_interaction("fork", f"{tag} prompt:\n{prompt_text}")
        _pre_input = self.total_input_tokens
        _pre_cached = self.total_cache_read_input_tokens
        _pre_creation = self.total_cache_creation_input_tokens
        _pre_output = self.total_output_tokens

        fork_msgs_sent_through: int = 0
        fork_prev_prompt_total: int = 0  # per-fork prev for _cache_assumed_usage
        fork_prev_output: int = 0

        try:
          while True:
            try:
              # Unbounded: the fork runs until it submits an answer or is
              # interrupted. A review fork (e.g. a refutation review) can take
              # several turns, well beyond any fixed turn cap. Matches the
              # ClaudeCode driver, whose fork loop is likewise an
              # answer-or-interrupt `while True`.
              while True:
                if fork._interrupted:
                    break

                if fork_response_id is not None:
                    fork_msgs_to_send = fork_messages[fork_msgs_sent_through:]
                else:
                    fork_msgs_to_send = fork_messages

                assert fork.fork_pending is not None
                _fork_allowed = list(fork.fork_pending.interaction.fork_allowed_tools)

                fork._model_time_start = time()
                resp = await self._retry_transient(
                    lambda: fork._checked_chat(
                        fork_provider, fork_msgs_to_send, fork_tools,
                        previous_response_id=fork_response_id,
                        allowed_tools=_fork_allowed))

                if resp.response_id is not None:
                    fork_response_id = resp.response_id
                    fork_msgs_sent_through = len(fork_messages) + 1

                if fork._model_time_start is not None:
                    fork.total_model_time += time() - fork._model_time_start
                    fork._model_time_start = None
                adj_usage, fork_prev_prompt_total = self._cache_assumed_usage(
                    resp.usage, fork_prev_prompt_total, fork_prev_output)
                fork_prev_output = resp.usage.output_tokens
                self._accumulate_usage(adj_usage)

                if resp.thinking:
                    fork.log_model_thinking(f"{tag} {resp.thinking}")
                if resp.content:
                    fork.log_model_output(f"{tag} {resp.content}")

                fork_messages.append(fork_provider.format_assistant_msg(resp))

                if resp.tool_calls:
                    for tc in resp.tool_calls:
                        args = json.loads(tc.arguments)
                        result, _is_error = await fork._executor.execute(tc.name, args)
                        fork_messages.append(
                            ToolResultMsg(call_id=tc.id, name=tc.name, content=result))
                        fork.total_tool_calls += 1

                assert fork.fork_pending is not None
                if fork.fork_pending.answer.done():
                    fork.log_interaction("fork", f"{tag} completed")
                    self.log_cost(
                        f"{tag} input={self.total_input_tokens - _pre_input} "
                        f"cached={self.total_cache_read_input_tokens - _pre_cached} "
                        f"cache_creation={self.total_cache_creation_input_tokens - _pre_creation} "
                        f"output={self.total_output_tokens - _pre_output}")
                    break

                if not resp.tool_calls:
                    fork_messages.append(UserMsg(
                        f"Call the `{self.tool_name(fork.fork_pending.interaction.answer_tool_name)}` tool to submit your answer."))
                    fork.log_interaction("fork", f"{tag} retrying: no tool calls")
              break
            except _QuotaError as e:
                self.warn_AoA_opr(f"{tag} Quota exhausted, waiting 20min to retry"
                                  + (f" ({e})" if str(e) else ""), to_isabelle=True)
                await self._quota_pause()
            except _TransientError as e:
                # Bound the retry by the RUN-WIDE budget. A fork's _retry_count
                # is never incremented, so this can only trip on the Runtime's
                # wall clock / tool-call count — limits the caller has hit too.
                # NEVER add `fork._retry_count += 1` here: that would end the
                # parent's proof for a fork-local reason. UnicodeEncodeError is
                # deliberately NOT caught on this seam: the fork cannot rebuild
                # its poisoned list, so a retry is futile — fail fast instead.
                if fork.check_budget():
                    break
                self.warn_AoA_opr(f"{tag} Transient API error, retrying in 2s: {e}")
                await asyncio.sleep(2)
        finally:
            self.total_isabelle_time += fork.total_isabelle_time
            self.total_model_time += fork.total_model_time
            self.total_quota_wait_time += fork.total_quota_wait_time
            await fork.close()

        # Guaranteed by construction: a fork leaves this loop either having
        # answered, or with a terminal quit_info — and setting a terminal
        # quit_info settles the slot with a SessionQuit (Session.quit_info's
        # setter), which `.result()` below re-raises. A failure here is a real
        # contract violation, so say what the state actually was.
        assert fork.fork_pending is not None and fork.fork_pending.answer.done(), (
            f"fork {tag} left the loop with no answer and no terminal quit_info: "
            f"quit_info={fork.quit_info!r} _interrupted={fork._interrupted}")
        return fork.fork_pending.answer.result()

    # ------------------------------------------------------------------
    # Cost Tracking
    # ------------------------------------------------------------------

    def estimate_tokens(self, messages: list[Msg]) -> int:
        total = 0
        for m in messages:
            match m:
                case SystemMsg(content=c) | UserMsg(content=c) | ToolResultMsg(content=c):
                    total += len(c)
                case AssistantMsg(response=r):
                    if r.content:
                        total += len(r.content)
                    if r.thinking:
                        total += len(r.thinking)
                    for tc in r.tool_calls:
                        total += len(tc.name) + len(tc.arguments)
        return total // 4

    def _pricing(self) -> dict[str, float]:
        return self._provider.pricing()
