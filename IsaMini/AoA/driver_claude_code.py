from typing import Any, Callable, cast
import json
import asyncio
import contextvars
import os
import re
from pathlib import Path
import tempfile
import shutil
from .model import *
from .language_model_driver import LMDriver, Chat_Restart, _TransientError, _QuotaError, PRICING, pricing_for, Usage
from . import prompts as P
from .mcp_http_server import ProofMCPHTTPServer
from claude_agent_sdk import ClaudeAgentOptions, ClaudeSDKClient, HookMatcher, ResultMessage
try:
    from claude_agent_sdk import RateLimitEvent
except ImportError:
    RateLimitEvent = None

from claude_agent_sdk.types import (
    AssistantMessage,
    HookInput,
    HookContext,
    HookJSONOutput,
    PreToolUseHookInput,
)
import Isabelle_Semantic_Embedding

_COMPACT_HEADROOM = 13_000
_DEFAULT_MODEL = "claude-opus-4-8[1m]"

def _derive_cheaper_model(model: str) -> str:
    m = re.match(r'(claude-)(opus)(-[\d\w.-]+)((?:\[.*\])?)', model)
    if m:
        return f"{m.group(1)}sonnet{m.group(3)}{m.group(4)}"
    return model

def _pricing_key(model: str) -> str:
    return re.sub(r'\[.*\]$', '', model)

def _model_context_window(model: str) -> int:
    m = re.search(r'\[(\d+)([mk])\]', model)
    if m:
        num, unit = int(m.group(1)), m.group(2)
        return num * (1_000_000 if unit == 'm' else 1_000)
    return 200_000

def _auto_compact_window(model: str, threshold_pct: float) -> int:
    ctx = _model_context_window(model)
    return max(100_000, min(1_000_000, int(ctx * threshold_pct) + _COMPACT_HEADROOM))


# The API's rejection of a request whose replayed session history contains a
# lone UTF-16 surrogate (a CLI streaming bug corrupts non-BMP characters in
# tool-call input; upstream issue family anthropics/claude-code#16294 — delete
# this pattern once fixed upstream). Narrow three-condition match:
# 400 + not valid JSON + surrogate ("no high surrogate" is the lone-low
# variant). Matched only inside structurally-gated failure texts (synthetic
# messages / is_error results — see _check_error_text), never against real
# model prose. re.S is free insurance: the incident's notices were all
# single-line, but nothing upstream promises that.
_CORRUPTED_HISTORY_RE = re.compile(
    r"400 .*not valid JSON: no (?:low|high) surrogate", re.S)


class _CorruptedHistoryError(Chat_Restart):
    """The CLI stored a corrupted (lone-surrogate) assistant message in its
    session history; every subsequent request replays it and is rejected by the
    API at the same position, so retrying this session is pure waste — the
    remedy is a deep restart (see ``Session.request_deep_restart``).

    Deliberately local to this driver: the concrete cause is ClaudeCode-
    specific (API drivers own their message list and would clean it in place
    instead); the shared base ``Chat_Restart`` is what the except arms catch.
    """

@agent_driver("ClaudeCode")
class ClaudeCode(LMDriver):
    _NON_PROOF_TOOLS = [
        'Read', 'Grep', 'Write', 'Edit', 'Skill', 'Agent',
        'TaskCreate', 'TaskGet', 'TaskList', 'TaskUpdate',
        'WebFetch', 'WebSearch', 'ExitPlanMode', 'MCPSearch', 'ToolSearch',
    ]
    _TOOL_NAME_MAP: dict[str, str] = {
        "query":  "mcp__proof__query",
        "edit":   "mcp__proof__edit",
        "delete": "mcp__proof__delete",
        "recall": "Read",
        "recall_removed": "mcp__proof__recall_removed",
        "request": "mcp__proof__request",
        "report": "mcp__proof__report",
        "subagent": "mcp__proof__subagent",
        "cancel_subagent": "mcp__proof__cancel_subagent",
        "answer_indexes": "mcp__proof__answer_indexes",
        "answer_index": "mcp__proof__answer_index",
        "answer_indexes_or_name": "mcp__proof__answer_indexes_or_name",
        "answer_indexes_or_spec": "mcp__proof__answer_indexes_or_spec",
        "answer_instantiate": "mcp__proof__answer_instantiate",
        "answer_refutation": "mcp__proof__answer_refutation",
        "answer_struggle_assessment": "mcp__proof__answer_struggle_assessment",
        "answer_missing_lemmas": "mcp__proof__answer_missing_lemmas",
        "answer_constraint_request": "mcp__proof__answer_constraint_request",
        "refresh": "mcp__proof__refresh",
        "write_memory": "mcp__proof__write_memory",
    }
    TOOL_WHITELIST = _NON_PROOF_TOOLS + list(_TOOL_NAME_MAP.values())
    # subagent/cancel_subagent are dispatch tools (the main agent AND workers); only
    # interaction forks lack them. Precompute that non-dispatcher allow-list
    # (TOOL_WHITELIST minus those two) once at class-definition time. (Statements,
    # not a comprehension, so the class-body name _TOOL_NAME_MAP stays in scope.)
    _WORKER_TOOL_WHITELIST = list(TOOL_WHITELIST)
    _WORKER_TOOL_WHITELIST.remove(_TOOL_NAME_MAP["subagent"])
    _WORKER_TOOL_WHITELIST.remove(_TOOL_NAME_MAP["cancel_subagent"])
    COMPACT_THRESHOLD = 0.85
    FORK_COMPACT_THRESHOLD = 0.99

    def _role_allowed_tools(self) -> list[str]:
        """SDK tool allow-list for this session's role. `subagent`/`cancel_subagent`
        are dispatch tools, allowed for the main agent AND workers (nested
        delegation) but hidden from interaction forks and from a session already at
        the maximum nesting depth (a sub-sub-agent cannot delegate further). Gated by
        `_can_offer_dispatch_tools`, mirroring the MCP tool list (`_tool_schemas_for`)."""
        return (self.TOOL_WHITELIST if self._can_offer_dispatch_tools()
                else self._WORKER_TOOL_WHITELIST)

    def tool_name(self, t: str) -> str:
        return self._TOOL_NAME_MAP.get(t, t)

    def __str__(self) -> str:
        if self._model == _DEFAULT_MODEL:
            return self._driver_name
        return f"{self._driver_name}({self._model})"

    working_dir: str
    _fork_counter: int
    _fork_name: str
    _fork_index: int | None

    def __init__(self, *args, parent: 'ClaudeCode | None' = None,
                 argument: str | None = None, **kwargs):
        super().__init__(*args, parent=parent, **kwargs)
        if parent is not None:
            self._model = parent._model
        else:
            self._model = argument or _DEFAULT_MODEL
        if parent is None:
            self.quickview_line_numbers = True
        if parent is not None:
            # Fork mode: share parent's state
            self.working_dir = parent.working_dir
            self.YAML_path = parent.YAML_path
            self.root = parent.root
            self._http_server = parent._http_server
            parent._fork_counter += 1
            self._fork_name = f"{parent._fork_name}.fork_{parent._fork_counter}"
        else:
            # Normal mode: create fresh state
            self.working_dir = tempfile.mkdtemp(prefix="agent_AoA_")
            if not os.access(self.working_dir, os.R_OK | os.W_OK):
                raise InternalError(
                    f"The working directory {self.working_dir} is not readable and writable.")
            self.YAML_path = os.path.join(self.working_dir, "proof.yaml")
            self._http_server: ProofMCPHTTPServer | None = None
            self._fork_name = "main"

        # Common to both modes
        self._model_time_start: float | None = None
        # Highest total_cost_usd seen per CLI session id (that field is a
        # running total within one CLI session, not per-turn) — see
        # _accumulate_cost.
        self._cost_by_session: dict[str, float] = {}
        self._session_id: str | None = None       # constant, set in initialize(), used for HTTP server registration
        self._conversation_id: str | None = None   # mutable, set by Agent SDK hook, used for fork resume
        self._fork_counter = 0
        self._fork_index = None
        self._client: ClaudeSDKClient | None = None
        self._mcp_url: str | None = None
        # Detached interrupt tasks (see `interrupt`). Held so they aren't
        # garbage-collected mid-flight; auto-discarded on completion.
        self._interrupt_tasks: set[asyncio.Task] = set()

    @classmethod
    def _make_fork(cls, parent: 'ClaudeCode', role=None) -> 'ClaudeCode':
        """Create a fork subsession sharing parent's state.
        Must be called from a different contextvars context than the parent."""
        from .model import _session_var
        try:
            current = _session_var.get()
        except LookupError:
            current = None
        if current is not None:
            raise InternalError(
                "_make_fork must be called in a fresh context "
                "(use loop.create_task with context=contextvars.copy_context())")
        return cls(parent=parent, role=role)

    _SKILLS = ["isabelle-fun-definition"]

    def _install_skills(self):
        """Copy skill files from assets/ into the working directory's
        .claude/skills/ so Claude Code can discover them."""
        assets = os.path.join(os.path.dirname(__file__), "assets")
        for skill_name in self._SKILLS:
            src = os.path.join(assets, f"{skill_name}.md")
            dst_dir = os.path.join(self.working_dir, ".claude", "skills", skill_name)
            os.makedirs(dst_dir, exist_ok=True)
            shutil.copy2(src, os.path.join(dst_dir, "SKILL.md"))

    async def initialize(self, root: Root):
        await super().initialize(root)
        if self.is_major:
            self._install_skills()

        # Register with singleton HTTP MCP server
        if self._http_server is None:
            self._http_server = await ProofMCPHTTPServer.get_or_create()
        self._session_id = self._http_server.allocate_session_id()
        self._mcp_url = await self._http_server.register_session(
            self._session_id, self)

        # Seed proof.yaml. `refresh_YAML` -> `print_proof_scope`, which renders
        # the full `root` for a major (non-worker) and the scoped view for a
        # worker — so a single call covers both. Interaction forks are neither
        # and intentionally write no YAML.
        if self.is_major or self.is_worker:
            self.refresh_YAML()

        main_model = self._model
        self.options = ClaudeAgentOptions(
            model=main_model,
            # `display` is required to get thinking TEXT back: Opus 4.7+
            # defaults to "omitted", which returns signature-only blocks whose
            # `.thinking` is empty — so `log_model_thinking` never fired.
            thinking={"type": "adaptive", "display": "summarized"},
            system_prompt=self.system_prompt(),
            cwd=self.working_dir,
            permission_mode="default",
            allowed_tools=self._role_allowed_tools(),
            mcp_servers={"proof": {"type": "http", "url": self._mcp_url}},
            env={"CLAUDE_CODE_ATTRIBUTION_HEADER": "0"},
            settings=json.dumps({"autoCompactWindow":
                _auto_compact_window(main_model, self.COMPACT_THRESHOLD)}),
            extra_args={"exclude-dynamic-system-prompt-sections": None},
            hooks={
                "PreToolUse": [
                    HookMatcher(matcher="*", hooks=[self.permission_control]),
                ],
                "PostToolUse": [
                    HookMatcher(matcher="*", hooks=[self._resume_model_timer]),
                ],
                "PostToolUseFailure": [
                    HookMatcher(matcher="*", hooks=[self._resume_model_timer]),
                ],
                "PreCompact": [
                    HookMatcher(matcher="*", hooks=[self.on_compact]),
                ],
            },
        )

    async def interrupt(self):
        if self._client is not None:
            # Fire-and-forget. The proof loop's exit is driven by the end-of-turn
            # gate, NOT by this interrupt: once `receive_response()` returns, the
            # loop breaks on a terminal `quit_info`, OR an emptied
            # `proof_scope_unfinished_nodes()` (the completion paths, which do NOT
            # set `quit_info`), OR (in a fork) the resolved `answer` future. The
            # interrupt only nudges the in-flight `receive_response()` to end early.
            # We must NOT await the interrupt control request inline here, because
            # `interrupt()` is reached from inside an MCP tool handler while the
            # CLI is still awaiting that very tool call's HTTP result — awaiting
            # the ack would block the handler until the CLI replies, and the two
            # can deadlock until the SDK's 60s control-request timeout fires and
            # escapes as an unhandled "Exception in ASGI application". Detach it
            # and swallow timeouts / connection errors (e.g. the client already
            # closed): correctness is guaranteed by the end-of-turn gate, not the ack.
            task = asyncio.create_task(self._safe_interrupt(self._client))
            self._interrupt_tasks.add(task)
            task.add_done_callback(self._interrupt_tasks.discard)

    async def _safe_interrupt(self, client: 'ClaudeSDKClient'):
        try:
            await client.interrupt()
        except Exception as e:
            self.debug_info(f"[INTERRUPT] control request failed (ignored): {e}")

    async def _deep_restart(self):
        # BEFORE the teardown awaits: `_conversation_id` is written only by
        # the PreToolUse hook, so until the rebuilt chat's first tool call it
        # still names the old poisoned CLI session — an in-flight tool handler
        # spawning an inheriting fork (FORKING_WITH_CTXT) during the teardown
        # would resume the poison. While it is None a fork gets `resume=None`,
        # i.e. an effectively context-free fresh conversation.
        self._conversation_id = None
        await super()._deep_restart()

    async def _run_agent_loop(self):
        await self._with_retry(self._sdk_loop)

    async def close(self):
        """Clean up the session and remove the temporary directory."""
        await super().close()
        # Cancel any still-pending detached interrupt (see `interrupt`) so it
        # cannot outlive the session and fire against a torn-down client. Await
        # the cancellations (suppressing their CancelledError via
        # return_exceptions) so the tasks are finalized rather than GC'd while
        # pending ("Task was destroyed but it is pending"). cancel() unwinds the
        # SDK's 60s ack wait promptly, so this does not block.
        for task in list(self._interrupt_tasks):
            task.cancel()
        if self._interrupt_tasks:
            await asyncio.gather(*self._interrupt_tasks, return_exceptions=True)
        self._interrupt_tasks.clear()
        # Unregister from HTTP server if registered
        if self._http_server is not None and self._session_id is not None:
            await self._http_server.unregister_session(self._session_id)
            self._session_id = None
        # Only the main session owns the working directory; forks share it.
        if self.is_major and hasattr(self, 'working_dir') and os.path.exists(self.working_dir):
            try:
                shutil.rmtree(self.working_dir)
                self.debug_info(f"[CLEANUP] Removed temporary directory: {self.working_dir}")
            except Exception as e:
                self.debug_info(f"[CLEANUP] Failed to remove temporary directory {self.working_dir}: {e}")

    def _get_tool_not_allowed_reason(self, tool: str, tool_input: dict) -> str:
        """Generate detailed rejection reason for tools not in whitelist."""
        reason = P.tool_not_allowed_base(tool)

        if tool == "Edit":
            # Check if editing proof.yaml
            target_file = tool_input.get('file_path', '')
            if target_file.endswith('proof.yaml') or 'proof.yaml' in target_file:
                reason += P.edit_tool_use_mcp_for_proof_yaml()
            else:
                reason += P.edit_tool_only_proof_yaml()
        elif tool == "AskUserQuestion":
            reason += P.ASK_USER_QUESTION_REJECTION
        elif tool == "Bash":
            reason += P.BASH_REJECTION

        return reason

    async def on_compact(
        self,
        hook_input: HookInput,
        tool_use_id: str | None,
        context: HookContext,
    ) -> HookJSONOutput:
        """Clear view caches before context compaction so the agent re-discovers entities."""
        # LearningTask reflection at the compaction seam: distil experience before
        # the working context is summarized away. No-op for a UsualTask / on an
        # interaction fork. NOT best-effort: failures PROPAGATE by design, so a bug in
        # the memory subsystem surfaces loudly instead of hiding behind a warning while
        # the proof still reports success -- which means one CAN abort this PreCompact
        # hook. See ``Session.maybe_run_memorize_interaction`` in model.py.
        await self.maybe_run_memorize_interaction("pre_compact")
        self._reset_view_state()
        self._log_meta("COMPACTION")
        return {}

    async def permission_control(
        self,
        hook_input: HookInput,
        tool_use_id: str | None,
        context: HookContext,
    ) -> HookJSONOutput:
        pre_tool_input = cast(PreToolUseHookInput, hook_input)
        tool = pre_tool_input["tool_name"]
        tool_input = pre_tool_input.get("tool_input") or {}
        cwd = pre_tool_input.get("cwd") or str(self.working_dir)

        # Record conversation_id for forking (Agent SDK assigns this)
        self._conversation_id = pre_tool_input.get("session_id") or self._conversation_id

        # 1. Check if tool is in whitelist
        if tool not in self._role_allowed_tools():
            return {
                "continue_": False,
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "deny",
                    "permissionDecisionReason": self._get_tool_not_allowed_reason(tool, tool_input),
                },
            }

        # 2. Check proof MCP tool interaction state.
        # An answer tool is allowed when THIS session has an interaction awaiting
        # an answer — either a forking one (interaction fork: `fork_pending`) or a
        # non-forking inline one raised mid-edit (`_nf_pending_interaction`, e.g.
        # Interaction_ClassifyInductionVars; answered via the executor's
        # `_handle_nf_answer`). Keying only on `fork_pending` here deadlocked the
        # main agent: a non-forking question blocks mutations (mcp_http_server
        # `_check_tool_permission`) while every answer tool was denied below.
        # (`fork_open` keeps the original `not answer.done()` semantics — a fork
        # whose answer future is already resolved must still be denied; do NOT
        # collapse this to `pending_interaction is not None`, which drops it.)
        is_answer_tool = any(tool == self.tool_name(t) for t in ANSWER_TOOLS)
        fork_open = (self.fork_pending is not None
                     and not self.fork_pending.answer.done())
        nf_open = self._nf_pending_interaction is not None
        if is_answer_tool and not (fork_open or nf_open):
            return {
                "continue_": False,
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "deny",
                    "permissionDecisionReason": f"No question pending. The `{tool}` tool can only be used when there is a question for you to answer.",
                },
            }

        # 3. For file tools, check path restrictions
        if tool in ['Read', 'Grep', 'Write', 'Edit']:
            # Get target file path
            target_path = None
            if tool == 'Read':
                target_path = tool_input.get('file_path')
            elif tool == 'Grep':
                target_path = tool_input.get('path')
            elif tool in ['Write', 'Edit']:
                target_path = tool_input.get('file_path')

            if target_path is None:
                if tool == 'Grep':
                    return {}

            # Normalize paths for comparison
            if target_path:
                import os
                target_path_abs = os.path.abspath(os.path.join(cwd, target_path))
                yaml_path_abs = os.path.abspath(self.YAML_path)

                # Normalize path separator for cross-platform checking
                target_path_normalized = target_path_abs.replace(os.sep, '/')

                is_in_claude_plan = ("/.claude/plans/" in target_path_normalized or
                                    target_path_normalized.endswith("/.claude/plan"))
                is_yaml = (target_path == self.YAML_path or target_path_abs == yaml_path_abs)

                # .claude/plan files take all four file tools; proof.yaml is
                # read-only to them (Read/Grep allowed, Write/Edit denied — the
                # agent changes the proof through the `edit` tool, and
                # `Session.refresh_YAML` regenerates the file); every other path
                # is denied.
                if is_in_claude_plan:
                    pass
                elif is_yaml:
                    if tool in ['Write', 'Edit']:
                        return {
                            "continue_": False,
                            "hookSpecificOutput": {
                                "hookEventName": "PreToolUse",
                                "permissionDecision": "deny",
                                "permissionDecisionReason": f"Cannot use `{tool}` on proof.yaml. Use the `{self.tool_name(TOOL_EDIT)}` tool instead.",
                            },
                        }
                else:
                    return {
                        "continue_": False,
                        "hookSpecificOutput": {
                            "hookEventName": "PreToolUse",
                            "permissionDecision": "deny",
                            "permissionDecisionReason": P.path_access_denied(tool, self.YAML_path, target_path),
                        },
                    }

        # 4. Passed all checks, allow execution
        if self._model_time_start is not None:
            self.total_model_time += time() - self._model_time_start
            self._model_time_start = None
        self.total_tool_calls += 1
        if not self.is_proof_tool(tool) or tool == self.tool_name(TOOL_READ):
            self.log_tool_call(tool, tool_input)

        # Runaway-loop guard for `recall`, which maps to the SDK-native `Read`
        # and so never reaches ToolExecutor.execute (where proof tools are
        # counted). Count identical Reads here and force a restart at the
        # threshold — same gating as execute (main agent, no restart/refresh
        # already pending, no parked non-forking interaction). Only `Read` is
        # counted here, so proof tools (also seen by this hook) are not
        # double-counted. Deny the repeated Read; the restart discards the turn.
        if (tool == self.tool_name(TOOL_READ) and self.is_major
                and self.quit_info is None
                and self._nf_pending_interaction is None):
            sig = f"recall\x00{json.dumps(tool_input, sort_keys=True, default=str)}"
            if self._note_repeat(sig):
                self.log_AoA_opr(
                    f"Loop detected: {LOOP_REPEAT_THRESHOLD} identical recall "
                    f"calls in a row; restarting context")
                self._log_meta("LOOP_RESTART", tool="recall")
                await self.request_restart()
                return {
                    "continue_": False,
                    "hookSpecificOutput": {
                        "hookEventName": "PreToolUse",
                        "permissionDecision": "deny",
                        "permissionDecisionReason": (
                            f"Loop detected: {LOOP_REPEAT_THRESHOLD} identical "
                            f"recall calls; restarting context."),
                    },
                }
        return {}

    async def _resume_model_timer(
        self,
        hook_input: HookInput,
        tool_use_id: str | None,
        context: HookContext,
    ) -> HookJSONOutput:
        self._model_time_start = time()
        return {}

    def _check_error_text(self, text: str) -> None:
        # THE failure-pattern table — the single place a failure text is
        # recognised. Both callers are structurally gated (synthetic
        # AssistantMessages via _classify_message; is_error ResultMessages via
        # _check_result_error), so real model prose never reaches it.
        if text.startswith("You've hit your limit"):
            raise _QuotaError(text)
        if "Rate limit" in text or "Request rejected (429)" in text:
            raise _TransientError(text)
        if _CORRUPTED_HISTORY_RE.search(text):
            raise _CorruptedHistoryError(text)

    def _check_rate_limit_event(self, event) -> None:
        if event.rate_limit_info.status == "rejected":
            # Carry resets_at: the wait that follows is 20 minutes long and silent
            # otherwise, and "until when" is the one thing the user needs to decide
            # whether to keep waiting or drop `by aoa` and prove it by hand.
            resets = getattr(event.rate_limit_info, "resets_at", None)
            raise _QuotaError("Rate limit rejected"
                              + (f", resets at {resets}" if resets else ""))

    def _classify_message(self, message: Any) -> None:
        """AssistantMessage-level failure classification; raises on a match.

        Gate first, patterns second: only a message the CLI itself synthesised
        (top-level ``error`` field set, or ``model == "<synthetic>"`` — each
        covers a CLI code path the other misses) enters text-pattern matching.
        Real model output NEVER gets classified as an error, so the model
        writing "Rate limit" in its prose can no longer trip the quota rail
        (which the old per-text-block ``_check_error_text`` calls did).

        Classified failures, each on its existing rail:
          - ``authentication_failed`` -> ``LMUnreachable`` (give up cleanly;
            retrying cannot authenticate us);
          - everything else delegates PER TEXT BLOCK to ``_check_error_text``
            (quota -> ``_QuotaError``, rate limit -> ``_TransientError``,
            the API's 400 "no low/high surrogate" rejection ->
            ``_CorruptedHistoryError``, whose except arms trigger the deep
            restart).
        Any other synthetic error (e.g. ConnectionRefused) keeps the old
        behaviour: it falls through to the log — an unrecognised signal must
        not become a terminal verdict.

        DELIBERATELY ONLY AssistantMessage: there is no `is_error` fail-safe on
        ResultMessage here, unlike the interpretation pipeline. In AoA an is_error
        ResultMessage is NORMAL — every terminal path ends its turn by calling
        interrupt() from inside an MCP tool handler (proof complete, surrender, refute,
        refresh, budget exhausted), and the CLI answers that with
        ResultMessage(subtype='error_during_execution', is_error=True, result=None).
        Treating those as failures reported successful proofs as TechnicalFailure,
        overwrote Surrender/Refute, and destroyed Refresh so context refresh could never
        happen. ResultMessages stay with _check_result_error -> _check_error_text, which
        keeps quota and rate-limit results on their wait-and-retry rails.
        """
        if not isinstance(message, AssistantMessage):
            return
        err = getattr(message, "error", None)
        # "<synthetic>" is a CLI implementation constant (the model name it
        # stamps on fabricated messages) — a boundary adaptation to a closed
        # upstream, same as the regex above.
        if not err and getattr(message, "model", None) != "<synthetic>":
            return  # real model output — never classify

        if err == "authentication_failed":
            detail = self._model_error_detail(message)
            # Give up cleanly through the existing LMUnreachable -> ResourceUnavailable
            # rail (see ``driver_api._api_loop``), the same one
            # ``driver_openai_api._fail_fast`` uses for a 401.
            raise LMUnreachable(
                "You have not logged Claude-Code. Run `claude '/login'` using your shell, then retry.\n"
                + (f" The CLI reported: {detail!r}" if detail else "")
                + "\nRead https://github.com/xqyww123/Isa-Mini/blob/main/IsaMini/AoA/Readme.md for more information")

        # Per block, not on the joined text: joining could interleave two
        # blocks' characters into a phantom pattern match.
        content = getattr(message, "content", None)
        if isinstance(content, list):
            for block in content:
                text = getattr(block, "text", None)
                if isinstance(text, str) and text:
                    self._check_error_text(text)

    @staticmethod
    def _model_error_detail(message: Any) -> str:
        """The model's own words for the failure. Worth carrying: an API relay that
        signals an exhausted quota with HTTP 403 surfaces as `authentication_failed`,
        where "run /login" would be exactly the wrong advice and only this text says so."""
        content = getattr(message, "content", None)
        texts = ([t for b in content
                  if isinstance(t := getattr(b, "text", None), str) and t.strip()]
                 if isinstance(content, list) else [])
        if not texts and isinstance(message, ResultMessage):
            texts = [message.result] if message.result else []
        return " ".join(texts).strip()

    def _check_result_error(self, message: 'ResultMessage') -> None:
        if message.is_error and message.result:
            self._check_error_text(message.result)

    async def _pump_response(self, client: 'ClaudeSDKClient', sink: 'ClaudeCode',
                             tag: str = "",
                             on_result: Callable[[ResultMessage], None] | None = None,
                             ) -> None:
        """Drain one turn's message stream — the single pump behind both
        ``_sdk_loop`` and ``_run_fork``. Logging and model timing land on
        *sink* (the fork, in the fork case); dollars and tokens accumulate on
        *self* (the parent, in the fork case — as before). *on_result* runs
        after each ResultMessage is accounted (the fork's "completed" log).

        A ``Chat_Restart`` from ``_classify_message`` is DEFERRED: the
        synthetic notice is skipped (never logged as model output), the rest
        of the stream — crucially the trailing ResultMessage, which carries
        the CLI session's whole accounting — is still drained, and the
        exception is raised only after the stream ends, so it reaches the
        callers' arms BEFORE any retry bookkeeping. A later quota/transient
        text in the same stream must not displace it (the wait-and-rebuild it
        asks for is doomed on a poisoned session); other classifications
        (auth/quota/transient) raise immediately as before. No timeout on the
        drain (R24): the loop has never had a per-turn timeout, and a CLI that
        wedges without closing the stream is a pre-existing risk class with
        zero observations."""
        corrupted: Chat_Restart | None = None
        async for message in client.receive_response():
            try:
                if RateLimitEvent is not None and isinstance(message, RateLimitEvent):
                    self._check_rate_limit_event(message)
                    continue
                # Structural check first: a synthetic error message also
                # carries the failure text in its content, which would
                # otherwise be logged as if the model had said it.
                self._classify_message(message)
                content = getattr(message, "content", None)
                if isinstance(content, list):
                    for block in content:
                        text = getattr(block, "text", None)
                        if isinstance(text, str) and text:
                            sink.log_model_output(f"{tag} {text}" if tag else text)
                        thinking = getattr(block, "thinking", None)
                        if isinstance(thinking, str) and thinking:
                            sink.log_model_thinking(
                                f"{tag} {thinking}" if tag else thinking)
                if isinstance(message, ResultMessage):
                    if sink._model_time_start is not None:
                        sink.total_model_time += time() - sink._model_time_start
                        sink._model_time_start = None
                    self._accumulate_cost(message)
                    self._check_result_error(message)
                    if on_result is not None:
                        on_result(message)
            except Chat_Restart as e:
                corrupted = corrupted or e
                continue
            except (_QuotaError, _TransientError):
                # Body-level, not classify-only: the result leg
                # (_check_result_error) and the rate-limit leg can raise
                # these too, and none of them may displace a cached
                # corruption.
                if corrupted is not None:
                    raise corrupted
                raise
        if corrupted is not None:
            raise corrupted

    async def _sdk_loop(self):
        """Run using the Claude Agent SDK (embedded mode)."""
        if self._client is not None:
            raise InternalError("_sdk_loop called while already running")
        # Guarded: _budget_start_time lives on the shared Runtime, so an
        # unconditional write here re-granted the full time budget on every
        # worker spawn and every quota/transient retry (same guard as
        # driver_api._api_loop).
        if self._budget_start_time is None:
            self._budget_start_time = time()
        while True:
            try:
                async with ClaudeSDKClient(options=self.options) as client:
                    self._client = client
                    self.refresh_YAML()
                    prompt = await self.initial_prompt()
                    if self._refresh_summary is not None:
                        prompt += "\n\nAgent's briefing:\n" + self._refresh_summary
                        self._refresh_summary = None
                    await client.query(prompt)
                    self._model_time_start = time()
                    while True:
                        # A deferred Chat_Restart raises out of the pump here,
                        # BEFORE the retry bookkeeping below.
                        await self._pump_response(client, self)
                        if self.check_budget():
                            break
                        unfinished_nodes = self.proof_scope_unfinished_nodes()
                        if unfinished_nodes and self.quit_info is None:
                            self._retry_count += 1
                            if self.check_budget():
                                break
                            retry_prompt = self.retry_prompt(unfinished_nodes)
                            self.log_retry(unfinished_nodes, retry_prompt)
                            await client.query(retry_prompt)
                            self._model_time_start = time()
                        else:
                            break
            except LMUnreachable as e:
                # Unauthenticated CLI: give up cleanly through quit_info rather than
                # spinning to the retry limit, which reported the infrastructure failure
                # as ResourceExhausted -- a proof that ran out of budget. Mirrors
                # the ``except LMUnreachable`` handler in ``driver_api._api_loop``.
                # Terminal => the outer loop breaks. ``settle_quit`` keeps a
                # concurrent terminal verdict and overwrites a non-terminal
                # Restart/Refresh on purpose -- we must stop, not loop again.
                if isinstance(self.quit_info, DeepRestart):
                    # This arm always breaks, so the pending deep restart can
                    # never happen; clear it or settle_quit would refuse the
                    # terminal verdict and the run would end labelled
                    # "deep_restart" (ML: unrecognized reason).
                    self.quit_info = None
                self.settle_quit(ResourceUnavailable(detail=str(e)))
                self.warn_AoA_opr(f"LM unreachable: {e}", to_isabelle=True)
                break
            except Chat_Restart as e:
                # Signal only — the loop-bottom DeepRestart branch is the sole
                # performer (retry charge, budget check, warning, teardown).
                await self.request_deep_restart(
                    detail=str(e), cli_record=str(self._cli_project_dir()))
                # No break, no continue: fall through to the bottom dispatcher.
                #   major:  quit_info is now DeepRestart -> bottom branch runs
                #   worker: own quit_info is terminal TechnicalFailure -> break
                #   major with a standing terminal verdict: settle_quit
                #     refused the signal -> break, verdict kept
            finally:
                self._client = None

            if not isinstance(self.quit_info, (Restart, Refresh, DeepRestart)):
                break

            if isinstance(self.quit_info, DeepRestart):
                # The sole performer of a deep restart. Must sit BEFORE the
                # unlabelled Restart tail below, which clears quit_info without
                # an isinstance test and would swallow the signal. Clear the
                # signal FIRST — check_budget short-circuits on any pending
                # quit_info (the C-F2 fix).
                qi, self.quit_info = self.quit_info, None
                self._retry_count += 1
                if self.check_budget():
                    break
                self.warn_AoA_opr(f"API error, restarting context: {qi.detail}",
                                  to_isabelle=True)
                await self._deep_restart()
                if self.check_budget():
                    break     # a terminal verdict landed during the teardown
                continue

            if isinstance(self.quit_info, Refresh):
                self._refresh_summary = self.quit_info.briefing
                self.quit_info = None
                self._reset_view_state()
                self.runtime.age += 1
                self._total_calls_at_last_refresh = self.total_tool_calls
                self.log_AoA_opr("Context refreshed")
                self._log_meta("REFRESH", briefing=self._refresh_summary)
                continue

            self.quit_info = None
            self.log_AoA_opr("Context restarted")
            self._log_meta("CONTEXT_RESTART")

        self.log_proof()

    def _pricing(self) -> dict[str, float]:
        # `_pricing_key` strips a context-window suffix (e.g. `[1m]`); unknown
        # Claude versions fall back to the opus default. See docs/COST_ACCOUNTING.md.
        return pricing_for(_pricing_key(self._model), PRICING["claude-opus-4-6"])

    def _cli_project_dir(self) -> Path:
        """Where the Claude Code CLI stores this working dir's session JSONLs."""
        return (Path.home() / ".claude" / "projects"
                / re.sub(r'[^a-zA-Z0-9]', '-', self.working_dir))

    def _accumulate_cost(self, message: ResultMessage) -> None:
        """Per-turn accounting from a ResultMessage. Cost is the REMOTE-reported
        ``total_cost_usd`` (authoritative); tokens go through the shared
        ``_accumulate_usage`` (Anthropic-native input already excludes cache).

        ``total_cost_usd`` is a RUNNING TOTAL within one CLI session ("read the
        latest result rather than summing across results" — official SDK docs),
        while ``usage`` on the same message is per-turn. So dollars take the
        per-session increment over the highest value seen; a straight ``+=``
        double-counted earlier turns whenever one session emitted several
        ResultMessages (retry prompts, fork nudges). ``total_cost_usd`` must
        stay an accumulator (+=) because ``_settle_costs`` merges worker costs
        into it — never assign to it wholesale.

        Always called on the session that OWNS the client loop — the parent,
        for fork pumps — so ``_cost_by_session`` sees every CLI session's
        running total on one ledger; a deep restart keeps that dict, and the
        rebuilt chat simply appears under its new CLI session id."""
        self.log_cost(f"session={message.session_id} usage={message.usage} "
                      f"total_cost_usd={message.total_cost_usd}")
        seen = self._cost_by_session.get(message.session_id, 0.0)
        running = message.total_cost_usd or 0.0
        if running > seen:
            self.total_cost_usd += running - seen
            self._cost_by_session[message.session_id] = running
        if message.usage:
            self._accumulate_usage(Usage.from_uncached(
                input_tokens=message.usage.get("input_tokens", 0),
                output_tokens=message.usage.get("output_tokens", 0),
                cache_read=message.usage.get("cache_read_input_tokens", 0),
                cache_creation=message.usage.get("cache_creation_input_tokens", 0)))

    async def _do_fork(self, interaction: Interaction,
                       prompt_text: str) -> Any:
        """Spawn a sub-agent to answer ``interaction`` and return its result.

        Runs a forked ``ClaudeCode`` session whose ``answer`` tool resolves
        the interaction. All fork body work runs in a fresh ``contextvars``
        context so the per-call ``_session_var`` does not leak into the caller.
        """
        loop = asyncio.get_running_loop()
        ctx = contextvars.copy_context()
        task = loop.create_task(self._run_fork(interaction, prompt_text), context=ctx)
        # Live-fork registry: lets a deep restart cancel forks whose host task
        # nothing else owns (e.g. `query` runs inline in an ASGI request task).
        # Done-callback, not a finally in _run_fork: a task cancelled before
        # its first step never runs the body's finally and would leak.
        self.runtime._live_forks.add(task)
        task.add_done_callback(self.runtime._live_forks.discard)
        return await task

    async def _run_fork(self, interaction: Interaction, prompt_text: str) -> Any:
        """Body of a forked interaction, run in its own contextvars context."""
        from .model import _session_var, Fork_Pending, Role_Interaction
        _session_var.set(None)  # type: ignore  # Clear the copied parent session so _make_fork succeeds
        mode = interaction.forking
        fork = ClaudeCode._make_fork(self, role=Role_Interaction(  # type: ignore[attr-defined]
            pending=Fork_Pending(interaction, asyncio.get_running_loop().create_future()),
            prompt=prompt_text,
            resume_id=self._conversation_id if mode == ForkingMode.FORKING_WITH_CTXT else None,
            mode=mode,
        ))

        await fork.initialize(self.root)
        assert fork._mcp_url is not None
        fork_url = fork._mcp_url

        mode = interaction.forking
        if mode == ForkingMode.FORKING_CHEAPER_NO_CTXT:
            model = _derive_cheaper_model(self._model)
        else:
            model = self._model
        if mode == ForkingMode.FORKING_WITH_CTXT:
            resume = self._conversation_id
            fork_session = True
        else:
            resume = None
            fork_session = False

        fork_options = ClaudeAgentOptions(
            model=model,
            # See the main-options note: without `display` the thinking text is
            # omitted on Opus 4.7+ and only a signature comes back.
            thinking={"type": "adaptive", "display": "summarized"},
            system_prompt=self.system_prompt(),
            resume=resume,
            fork_session=fork_session,
            cwd=self.working_dir,
            permission_mode="default",
            # Parent's list ON PURPOSE: the tool roster is part of the resumed
            # conversation's cached prefix; fork narrowing happens in
            # permission_control instead.
            allowed_tools=self._role_allowed_tools(),
            mcp_servers={"proof": {"type": "http", "url": fork_url}},
            env={"CLAUDE_CODE_ATTRIBUTION_HEADER": "0"},
            settings=json.dumps({"autoCompactWindow":
                _auto_compact_window(model, self.FORK_COMPACT_THRESHOLD)}),
            extra_args={"exclude-dynamic-system-prompt-sections": None},
            hooks={
                "PreToolUse": [
                    HookMatcher(matcher="*", hooks=[fork.permission_control]),
                ],
                "PostToolUse": [
                    HookMatcher(matcher="*", hooks=[fork._resume_model_timer]),
                ],
                "PostToolUseFailure": [
                    HookMatcher(matcher="*", hooks=[fork._resume_model_timer]),
                ],
                "PreCompact": [
                    HookMatcher(matcher="*", hooks=[fork.on_compact]),
                ],
            },
        )
        tag = f"[{fork._fork_name}]"
        try:
          while True:
            try:
              async with ClaudeSDKClient(options=fork_options) as fork_client:
                fork._client = fork_client
                # Wording avoids "Forget the previous instructions" / "MUST" /
                # "only task" — under FORKING_WITH_CTXT the fork resumes the
                # parent conversation, and those phrases trip Claude's anti-
                # injection training, leading the fork to ignore the prompt.
                fork_prompt = prompt_text
                answer_tool = self.tool_name(interaction.answer_tool_name)
                if answer_tool not in prompt_text:
                    fork_prompt += (
                        f"\nAnswer the question above by calling the "
                        f"`{answer_tool}` tool.")
                fork.log_interaction("fork", f"{tag} prompt:\n{prompt_text}")
                await fork_client.query(fork_prompt)
                fork._model_time_start = time()
                while True:
                    await self._pump_response(
                        fork_client, fork, tag=tag,
                        on_result=lambda m: fork.log_interaction(
                            "fork", f"{tag} completed: subtype={m.subtype}"))
                    assert fork.fork_pending is not None
                    if fork.fork_pending.answer.done():
                        break
                    fork.log_interaction("fork", f"{tag} retrying: interaction not answered")
                    await fork_client.query(
                        "It looks like you haven't submitted your answer. "
                        f"Call `{self.tool_name(fork.fork_pending.interaction.answer_tool_name)}` to submit it.")
                    fork._model_time_start = time()
              fork._client = None
              break
            # No LMUnreachable arm on purpose: it propagates out of this fork
            # into the caller's declared arm (ToolExecutor.execute), which
            # settles a terminal ResourceUnavailable on the calling session.
            except _QuotaError as e:
                self.warn_AoA_opr(f"{tag} Quota exhausted, waiting 20min to retry"
                                  + (f" ({e})" if str(e) else ""), to_isabelle=True)
                await self._quota_pause()
            except _TransientError as e:
                self.warn_AoA_opr(f"{tag} Transient API error, retrying in 2s: {e}")
                await asyncio.sleep(2)
            except Chat_Restart as e:
                # Abandon (弃子): the corruption may live in the parent prefix
                # this fork resumed, so no local rebuild is trustworthy — the
                # fork gives up its work and signals the deep restart. Its
                # self-judgment (a terminal quit_info) settles the answer
                # future via the SessionQuit rail, so the tail assert holds;
                # the parent's settle_quit refuses that terminal verdict while
                # its own DeepRestart is pending.
                assert fork.fork_pending is not None
                if fork.fork_pending.answer.done():
                    break                       # answer already delivered
                await fork.request_deep_restart(
                    detail=str(e), cli_record=str(self._cli_project_dir()))
                break
        finally:
            fork._client = None      # never leave it pointing at a dead client
            if self._http_server is not None and fork._session_id is not None:
                await self._http_server.unregister_session(fork._session_id)
            self.total_isabelle_time += fork.total_isabelle_time
            self.total_model_time += fork.total_model_time
            self.total_quota_wait_time += fork.total_quota_wait_time
            await fork.close()
        # See driver_api's counterpart: a fork either answered, or got a terminal
        # quit_info whose setter settled the slot with a SessionQuit that
        # `.result()` re-raises. Failing here is a real contract violation.
        assert fork.fork_pending is not None and fork.fork_pending.answer.done(), (
            f"fork {tag} left the loop with no answer and no terminal quit_info: "
            f"quit_info={fork.quit_info!r}")
        return fork.fork_pending.answer.result()

    def refresh_YAML(self):
        with open(self.YAML_path, 'w', encoding="utf-8") as f:
            self.print_proof_scope(0, MyIO(f), update_line=True, show_warnings=True)
