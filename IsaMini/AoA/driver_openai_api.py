"""OpenAI-SDK providers and the drivers built on them, for IsaMini.AoA.

Split out of driver_api.py so that importing a non-OpenAI driver does not import the
openai SDK. driver_anthropic (and the unregistered driver_gemini) need only Provider,
APIDriver and the Msg types, all of which stay in driver_api; every symbol here either
touches `openai.` or is reachable only from something that does. That is what lets
`pip install IsaMini[anthropic]` stop pulling openai and tiktoken.

Nothing outside this module may import these names: driver_api must not import
driver_openai_api, or the two form a cycle.
"""

from __future__ import annotations

import asyncio
import os
import re
import uuid
from time import time
from typing import Any, Awaitable, Callable

import httpx
import openai

from .model import *
from .language_model_driver import (_TransientError, _QuotaError, _T, PRICING,
                                    pricing_for, _parse_effort_suffix, Usage)

from .mcp_http_server import _cc_edit_schema_flat, _cc_edit_schema_raw
from .driver_api import (Provider, APIDriver, ToolCall, ProviderResponse,
                         Msg, SystemMsg, UserMsg, AssistantMsg, ToolResultMsg)


# ============================================================================
# OpenAI-Compatible Provider
# ============================================================================

def _strictify_schema(schema: dict, *, nullify: bool = True) -> dict:
    """Transform a JSON Schema for OpenAI strict mode.

    - ``additionalProperties: false`` on every object
    - All properties listed in ``required``; when ``nullify`` (default), optional
      ones are made nullable. Pass ``nullify=False`` to force-require every
      property without widening its type — for callers that rely on the parser
      treating an empty value (``[]``/``""``/``false``) the same as an absent one.
    """
    import copy
    schema = copy.deepcopy(schema)

    def _walk(node: Any) -> Any:
        if isinstance(node, dict):
            if "properties" in node and "type" not in node:
                node["type"] = "object"
            if "const" in node and "type" not in node:
                v = node["const"]
                if isinstance(v, str):
                    node["type"] = "string"
                elif isinstance(v, bool):
                    node["type"] = "boolean"
                elif isinstance(v, int):
                    node["type"] = "integer"
                elif isinstance(v, float):
                    node["type"] = "number"
            if node.get("type") == "object" and "properties" in node:
                node["additionalProperties"] = False
                props = node["properties"]
                required = set(node.get("required") or [])
                if nullify:
                    for prop_name in props:
                        if prop_name not in required:
                            _make_nullable(props, prop_name)
                node["required"] = list(props.keys())
            for v in node.values():
                _walk(v)
        elif isinstance(node, list):
            for v in node:
                _walk(v)
        return node

    def _make_nullable(props: dict, name: str) -> None:
        prop = props[name]
        if not isinstance(prop, dict):
            return
        if "anyOf" in prop:
            alts = prop["anyOf"]
            if not any(a == {"type": "null"} for a in alts):
                alts.append({"type": "null"})
        elif "$ref" in prop or "const" in prop:
            props[name] = {"anyOf": [prop, {"type": "null"}]}
        elif "type" in prop:
            t = prop["type"]
            if isinstance(t, str) and t != "null":
                prop["type"] = [t, "null"]
            elif isinstance(t, list) and "null" not in t:
                t.append("null")

    return _walk(schema)


def _flatten_edit_schema_deepseek(raw: dict) -> dict:
    """Build the ``edit`` schema for DeepSeek V4 ``/beta`` strict mode.

    DeepSeek strict compiles the tool schema into a constrained-decoding grammar
    that CANNOT resolve ``$ref`` — any ``$ref`` makes compilation fall back to a
    path that silently drops the schema from the prompt (the model then
    hallucinates field names). See memory ``deepseek-v4-strict-not-enforced``.
    So we fully inline (no ``$ref``) and additionally:
      - remove every ``proof``/``proofs`` field (no inline sub-proofs; the agent
        builds the tree incrementally — a bodiless op auto-opens a fillable
        child, so absent==open-block on the parser side);
      - collapse the self-recursive ``FactByName.discharge`` to plain name
        strings (``null`` kept for skip-a-premise; DeepSeek strict accepts null);
      - ``const`` (string) -> single-value ``enum`` (strict has no string const);
      - drop ``minItems``/``maxItems``/``default`` (unsupported by strict);
      - all object props ``required`` + ``additionalProperties:false`` WITHOUT
        nullify (the model sends empty values; parser treats empty == absent).
    """
    import copy
    raw = copy.deepcopy(raw)
    defs = raw.pop("$defs", {})
    _PROOF_KEYS = {"proof", "proofs"}
    _DROP_KEYS = {"minItems", "maxItems", "default"}
    _flat_fbn: dict | None = None

    def _factbyname() -> dict:
        nonlocal _flat_fbn
        if _flat_fbn is None:
            fbn = copy.deepcopy(defs["FactByName"])
            props = fbn.get("properties", {})
            if "discharge" in props:  # break the self-recursion: facts -> name strings
                props["discharge"]["items"] = {
                    "anyOf": [{"type": "string"}, {"type": "null"}]}
            _flat_fbn = fbn
        return copy.deepcopy(_flat_fbn)

    def _resolve(node: Any) -> Any:
        if isinstance(node, dict):
            ref = node.get("$ref")
            if isinstance(ref, str) and ref.startswith("#/$defs/"):
                name = ref[len("#/$defs/"):]
                if name == "FactByName":
                    return _resolve(_factbyname())
                return _resolve(copy.deepcopy(defs[name]))
            out: dict[str, Any] = {}
            for k, v in node.items():
                if k in _PROOF_KEYS or k in _DROP_KEYS:
                    continue
                if k == "const" and isinstance(v, str):
                    out["enum"] = [v]
                    out.setdefault("type", "string")
                    continue
                rv = _resolve(v)
                if k == "simplify" and isinstance(rv, dict) and rv.get("description"):
                    rv["description"] = rv["description"].rstrip() + " Most cases: true."
                out[k] = rv
            return out
        if isinstance(node, list):
            return [_resolve(x) for x in node]
        return node

    flat = _resolve(raw)
    # all-required + additionalProperties:false, but NO nullify (empty == absent).
    return _strictify_schema(flat, nullify=False)


_cc_edit_schema_deepseek_cache: dict | None = None


def _deepseek_edit_schema() -> dict:
    """Lazily build + cache the DeepSeek-strict ``edit`` schema (import-safe)."""
    global _cc_edit_schema_deepseek_cache
    if _cc_edit_schema_deepseek_cache is None:
        _cc_edit_schema_deepseek_cache = _flatten_edit_schema_deepseek(_cc_edit_schema_raw)
    return _cc_edit_schema_deepseek_cache


class OpenAIBase(Provider):
    """Shared config for OpenAI-family providers."""

    _CONTEXT_WINDOWS: dict[str, int] = {
        "gpt-5.5-pro": 1_050_000,
        "gpt-4.1": 1_048_576,
        "gpt-4.1-mini": 1_048_576,
        "gpt-4.1-nano": 1_048_576,
        "o3": 200_000,
        "o4-mini": 200_000,
    }

    # Per-model documented max output tokens (reasoning/CoT + visible output
    # combined — the Responses API counts both against this cap). Sent as
    # ``max_output_tokens`` to give the server a hard ceiling against runaway
    # generation. Models absent here are sent with no cap.
    _MAX_OUTPUT_TOKENS: dict[str, int] = {
        "gpt-5.5": 128_000,
        "gpt-5.5-pro": 128_000,
    }

    # Models whose API implements the OpenAI ``tool_choice: {"type":
    # "allowed_tools", ...}`` extension. ONLY ids listed here receive a
    # ``tool_choice`` when a fork requests ``allowed_tools``; every other model
    # gets NO ``tool_choice`` at all. Sending the ``allowed_tools`` variant to a
    # backend that doesn't model it (e.g. DeepSeek, whose Chat Completions only
    # accepts the string forms ``auto``/``none``/``required`` or the object
    # ``{"type": "function", ...}``) triggers a permanent 400
    # ``invalid_request_error`` ("unknown variant `allowed_tools`") — which the
    # retry layers then spin on forever, wedging the whole agent. Default-off is
    # the safe choice: a missing ``tool_choice`` only means the fork's answer
    # tool isn't *forced* (the fork loop re-prompts when no tool is called).
    # Keys are the bare model id; a provider prefix like ``deepseek/`` is
    # stripped before lookup (see ``_supports_allowed_tools_choice``).
    _ALLOWED_TOOLS_CHOICE_MODELS: frozenset[str] = frozenset({
        "gpt-5.5-pro", "gpt-5.5", "gpt-5.4",
        "gpt-4.1", "gpt-4.1-mini", "gpt-4.1-nano",
        "o3", "o4-mini",
    })

    _DEFAULT_TIMEOUT = httpx.Timeout(connect=5.0, read=1500.0, write=600.0, pool=600.0)

    def __init__(self, model: str, api_key: str | None = None,
                 base_url: str | None = None, cache_key: str | None = None,
                 default_context_window: int = 128_000,
                 temperature: float | None = None,
                 reasoning_effort: str | None = None,
                 extra_params: dict[str, Any] | None = None,
                 strict_tools: bool = False,
                 cot_retention: str | None = None,
                 timeout: httpx.Timeout | None = None,
                 max_stream_time: float = 1800,
                 use_stream: bool = True):
        self._model = model
        # Whether ``chat`` streams the completion. Default on (low first-token
        # latency + stall detection). A subclass sets this False when its backend
        # mis-handles streaming — e.g. the K2 vLLM deployment emits no tool-call
        # deltas while streaming, so tools silently never fire (see K2ThinkProvider).
        self._use_stream = use_stream
        self._client = openai.AsyncOpenAI(
            api_key=api_key or os.environ.get("OPENAI_API_KEY"),
            base_url=base_url,
            timeout=timeout or self._DEFAULT_TIMEOUT,
        )
        self._max_stream_time = max_stream_time
        self._cache_key = cache_key
        self._default_context_window = default_context_window
        self._strict_tools = strict_tools
        self._temperature = temperature
        self._reasoning_effort = reasoning_effort
        self._extra_params = extra_params or {}
        # How much of the assistant turns' chain-of-thought (DeepSeek-style
        # plaintext ``reasoning_content``) to feed back on later requests:
        #   "full"   – keep every assistant turn's CoT (default)
        #   "latest" – keep only the most recent assistant turn's CoT
        #   "none"   – strip all CoT before sending
        # NOTE: CoT is always *captured* regardless; this only governs what is
        # re-sent. On DeepSeek V4 thinking-mode models the API *requires* the
        # CoT of any assistant turn that made a tool call to be passed back —
        # so "latest"/"none" will trigger 400 on multi-turn tool calls there
        # and are only safe for non-V4 providers or tool-free use. Unknown
        # values are treated as "full".
        self._cot_retention = (
            cot_retention or os.environ.get("CHAT_COT_RETENTION") or "full"
        ).lower()

    @property
    def context_window(self) -> int:
        return self._CONTEXT_WINDOWS.get(self._model, self._default_context_window)

    @property
    def max_output_tokens(self) -> int | None:
        return self._MAX_OUTPUT_TOKENS.get(self._model)

    @property
    def model_name(self) -> str:
        return self._model

    def _supports_allowed_tools_choice(self) -> bool:
        """Whether this model's backend accepts the OpenAI ``allowed_tools``
        ``tool_choice`` variant. Exact match on the bare model id (any provider
        prefix like ``deepseek/`` stripped) against
        ``_ALLOWED_TOOLS_CHOICE_MODELS``; unknown ids default to ``False``."""
        bare = self._model.rsplit("/", 1)[-1]
        return bare in self._ALLOWED_TOOLS_CHOICE_MODELS

    def pricing(self) -> dict[str, float]:
        return pricing_for(self._model, PRICING["gpt-4.1"])

    def _strict_schema(self, name: str, schema: dict) -> dict:
        if name == "edit":
            return _strictify_schema(_cc_edit_schema_flat)
        return _strictify_schema(schema)

    def _strict_for_tool(self, name: str) -> bool:
        """Whether THIS tool is sent in strict mode. Base: all tools when
        ``strict_tools`` is enabled; subclasses may restrict per tool."""
        return self._strict_tools


class _WhitespaceRunaway(Exception):
    """Raised internally when a streamed response degenerates into an unbounded
    run of whitespace-only delta events — a known gpt-5.5 failure mode: the model
    starts a tool call / message, then emits endless spaces/tabs/newlines and
    never closes it (no ``response.completed``). Carries the whitespace-run
    length; caught in the ``chat()`` stream loop, which aborts the stream and
    retries (re-rolling the sample)."""


class OpenAIChatProvider(OpenAIBase):
    """Chat completions protocol (/v1/chat/completions)."""

    def _msgs_to_dicts(self, messages: list[Msg]) -> list[dict]:
        out: list[dict] = []
        for m in messages:
            match m:
                case SystemMsg(content=c):
                    out.append({"role": "system", "content": c})
                case UserMsg(content=c):
                    out.append({"role": "user", "content": c})
                case AssistantMsg(native=n) if n is not None:
                    out.append(n)
                case AssistantMsg(response=r):
                    msg: dict[str, Any] = {"role": "assistant", "content": r.content}
                    if r.thinking:
                        msg["reasoning_content"] = r.thinking
                    if r.tool_calls:
                        msg["tool_calls"] = [
                            {"id": tc.id, "type": "function",
                             "function": {"name": tc.name, "arguments": tc.arguments}}
                            for tc in r.tool_calls
                        ]
                    out.append(msg)
                case ToolResultMsg(call_id=cid, content=c):
                    out.append({"role": "tool", "tool_call_id": cid, "content": c})
        self._apply_cot_retention(out)
        return out

    def _apply_cot_retention(self, out: list[dict]) -> None:
        """Drop assistant ``reasoning_content`` from *out* per ``_cot_retention``.

        Operates in place but never mutates a stored ``native`` dict: entries to
        be stripped are *replaced* with fresh copies sans ``reasoning_content``.
        "full" (and any unknown value) leaves *out* untouched.
        """
        mode = self._cot_retention
        if mode not in ("latest", "none"):
            return
        idxs = [i for i, d in enumerate(out)
                if d.get("role") == "assistant" and "reasoning_content" in d]
        strip = idxs if mode == "none" else idxs[:-1]
        for i in strip:
            out[i] = {k: v for k, v in out[i].items() if k != "reasoning_content"}

    async def _consume_stream(self, stream: Any, text_parts: list[str],
                              rc_parts: list[str],
                              tc_map: dict[int, dict[str, str]]) -> Any:
        """Drain a streaming completion into the given accumulators; return the
        final usage chunk. Raises ``TimeoutError`` if no chunk arrives within
        ``_max_stream_time`` (caller maps it to a transient stall error)."""
        stream_usage: Any = None
        async with asyncio.timeout(self._max_stream_time):
            async for chunk in stream:
                if chunk.usage:
                    stream_usage = chunk.usage
                if not chunk.choices:
                    continue
                delta = chunk.choices[0].delta
                # DeepSeek-style plaintext CoT: a non-standard field the OpenAI
                # SDK surfaces via model_extra / attribute. Capture it so it can
                # be round-tripped (required on V4 thinking-mode tool calls).
                rc = getattr(delta, "reasoning_content", None)
                if rc:
                    rc_parts.append(rc)
                if delta.content:
                    text_parts.append(delta.content)
                if delta.tool_calls:
                    for tcd in delta.tool_calls:
                        idx = tcd.index
                        if idx not in tc_map:
                            tc_map[idx] = {"id": "", "name": "", "arguments": ""}
                        if tcd.id:
                            tc_map[idx]["id"] = tcd.id
                        if tcd.function:
                            if tcd.function.name:
                                tc_map[idx]["name"] = tcd.function.name
                            if tcd.function.arguments:
                                tc_map[idx]["arguments"] += tcd.function.arguments
        return stream_usage

    async def chat(self, messages: list[Msg], tools: list[dict],
                   *, previous_response_id: str | None = None,
                   allowed_tools: list[str] | None = None) -> ProviderResponse:
        params: dict[str, Any] = {
            "model": self._model,
            "messages": self._msgs_to_dicts(messages),
        }
        if self._temperature is not None:
            params["temperature"] = self._temperature
        if self._reasoning_effort is not None:
            params["reasoning_effort"] = self._reasoning_effort
        if tools:
            params["tools"] = tools
        if allowed_tools and self._supports_allowed_tools_choice():
            params["tool_choice"] = {
                "type": "allowed_tools",
                "allowed_tools": {
                    "mode": "required",
                    "tools": [{"type": "function", "function": {"name": n}} for n in allowed_tools],
                },
            }
        if self._cache_key:
            params.setdefault("extra_body", {})
            params["extra_body"]["prompt_cache_key"] = self._cache_key
            params["extra_body"]["prompt_cache_retention"] = "24h"
        if self._extra_params:
            params.setdefault("extra_body", {})
            params["extra_body"].update(self._extra_params)

        text_parts: list[str] = []
        rc_parts: list[str] = []
        tc_map: dict[int, dict[str, str]] = {}
        stream_usage: Any = None

        try:
            if self._use_stream:
                stream = await self._client.chat.completions.create(
                    **params, stream=True,
                    stream_options={"include_usage": True})
                stream_usage = await self._consume_stream(
                    stream, text_parts, rc_parts, tc_map)
            else:
                # Non-streaming: the server assembles the whole completion (incl.
                # tool_calls) and returns it in one shot. Used where the backend's
                # streaming tool-call parsing is broken (K2 vLLM).
                resp = await self._client.chat.completions.create(**params)
                stream_usage = resp.usage
                msg = resp.choices[0].message
                if msg.content:
                    text_parts.append(msg.content)
                rc = getattr(msg, "reasoning_content", None)
                if rc:
                    rc_parts.append(rc)
                for idx, tcd in enumerate(msg.tool_calls or []):
                    tc_map[idx] = {
                        "id": tcd.id or "",
                        "name": tcd.function.name or "",
                        "arguments": tcd.function.arguments or "",
                    }
        except openai.RateLimitError as e:
            if "insufficient_quota" in str(e):
                raise _QuotaError(str(e)) from e
            raise _TransientError(str(e)) from e
        except TimeoutError:
            raise _TransientError(
                f"stream stalled: not completed within {self._max_stream_time}s")
        except openai.APIError as e:
            # Retry only where a retry can plausibly change the outcome: 5xx
            # (server-side), plus 408 (request timeout) and 409 (conflict); 429
            # is already handled by the RateLimitError branch above. A status
            # error outside that set — 400/401/403/404/422/… — is a permanent
            # request error: re-raise so it propagates instead of being retried
            # forever (the bug behind the deepseek allowed_tools 400 wedge).
            # Non-status APIErrors (connection/timeout, no ``status_code``) stay
            # transient via the fall-through.
            if isinstance(e, openai.APIStatusError) and \
                    e.status_code < 500 and e.status_code not in (408, 409):
                raise
            raise _TransientError(str(e)) from e
        except httpx.TransportError as e:
            # A read/connection/protocol error (incl. httpx.ReadTimeout) raised
            # *during* stream consumption is NOT wrapped by the openai SDK — it
            # only wraps the initial request — so it escapes as a raw httpx
            # exception that _retry_transient (which catches only _TransientError)
            # would miss, crashing the whole run. Wrap it as transient so the
            # turn is retried, matching OpenAIResponsesProvider's stream handling.
            raise _TransientError(str(e)) from e

        tool_calls: list[ToolCall] = [
            ToolCall(id=v["id"], name=v["name"], arguments=v["arguments"])
            for _, v in sorted(tc_map.items())]
        self.validate_tool_call_json(tool_calls)

        cached = 0
        if stream_usage:
            details = getattr(stream_usage, 'prompt_tokens_details', None)
            if details:
                cached = getattr(details, 'cached_tokens', 0) or 0

        # OpenAI prompt_tokens INCLUDES cached → normalize to uncached input.
        usage = Usage.from_inclusive(
            prompt_tokens=stream_usage.prompt_tokens if stream_usage else 0,
            output_tokens=stream_usage.completion_tokens if stream_usage else 0,
            cached=cached,
        )

        return ProviderResponse(
            content="".join(text_parts) if text_parts else None,
            thinking="".join(rc_parts) if rc_parts else None,
            tool_calls=tool_calls,
            usage=usage,
        )

    def format_tools(self, tool_info: dict[str, dict[str, Any]]) -> list[dict]:
        out: list[dict] = []
        for name, info in tool_info.items():
            strict = self._strict_for_tool(name)
            fn: dict[str, Any] = {
                "name": name,
                "description": info["description"],
                "parameters": self._strict_schema(name, info["schema"]) if strict else info["schema"],
            }
            if strict:
                fn["strict"] = True
            out.append({"type": "function", "function": fn})
        return out

    def format_assistant_msg(self, response: ProviderResponse) -> AssistantMsg:
        msg: dict[str, Any] = {"role": "assistant", "content": response.content}
        if response.thinking:
            # Round-trip the CoT. DeepSeek V4 thinking-mode requires this on
            # assistant turns that made a tool call; harmless for providers
            # that don't emit reasoning_content. ``_apply_cot_retention``
            # governs how much survives on the way back out.
            msg["reasoning_content"] = response.thinking
        if response.tool_calls:
            msg["tool_calls"] = [
                {"id": tc.id, "type": "function",
                 "function": {"name": tc.name, "arguments": tc.arguments}}
                for tc in response.tool_calls
            ]
        return AssistantMsg(response=response, native=msg)


OpenAIProvider = OpenAIChatProvider


class OpenAIResponsesProvider(OpenAIBase):
    """Responses protocol (/v1/responses).

    Transient-error policy: this provider handles transient API errors
    (rate limits, network errors, timeouts) internally via retries and
    background-mode fallback.  Callers do not need ``_retry_transient``
    wrapping.  Only ``_QuotaError`` (insufficient quota), non-transient
    request errors (4xx other than 429), and ``_TransientError`` after
    exhausting the 1-hour background retry budget propagate.
    """

    # --- Endpoint policy (overridable per subclass; defaults == platform
    # behavior, so APIDriver_OpenAI is byte-identical). `chat` reads these so
    # there is no per-request "mode" branching. CodexResponsesProvider flips them
    # for the stateless ChatGPT-subscription codex backend. ---
    STORE: bool                     = True   # params["store"]
    SEND_PREVIOUS_RESPONSE_ID: bool = True   # chain via previous_response_id
    SURFACE_RESPONSE_ID: bool       = True   # return response.id (False -> None -> full resend)
    SEND_CACHE_RETENTION: bool      = True   # params["prompt_cache_retention"] = "24h"
    SEND_MAX_OUTPUT_TOKENS: bool    = True   # params["max_output_tokens"]
    BACKGROUND_FALLBACK: bool       = True   # allow _resubmit_background on stream timeout
    FAIL_FAST_NON_TRANSIENT: bool   = False  # conn-refused / 401 -> LMUnreachable (not a retry-spin)

    def _fail_fast(self, e: Exception):
        """Raise ``LMUnreachable`` with an actionable message. Called only when
        ``FAIL_FAST_NON_TRANSIENT`` is set (subscription mode) on a
        connection/auth failure, so the proof gives up cleanly instead of
        spinning in the transient-retry loop for an hour."""
        if isinstance(e, openai.AuthenticationError):
            raise LMUnreachable(
                "Codex-API: ChatGPT subscription credentials invalid/expired. "
                "Run `codex login` and retry.") from e
        raise LMUnreachable(
            f"Codex-API: local openai-oauth proxy unreachable at {self._client.base_url}. "
            "Start it (e.g. `npx openai-oauth`) and retry.") from e

    @staticmethod
    def _is_transient_upstream_error(e: Exception) -> bool:
        """True for an ``upstream_error``-typed 4xx coming from the local
        codex proxy (auth2api / openai-oauth). That ``type`` means the codex
        backend's OWN internal upstream momentarily failed — surfaced as e.g. a
        400 ``"Unsupported content type"`` — which is transient and worth
        retrying. A genuine client-side 400 (malformed request) carries a
        different ``type`` (e.g. ``invalid_request_error``) and is NOT matched,
        so it still fails fast. The platform OpenAI API never emits
        ``upstream_error``, so this stays a no-op there."""
        body = getattr(e, "body", None)
        if isinstance(body, dict):
            err = body.get("error")
            if isinstance(err, dict) and err.get("type") == "upstream_error":
                return True
        return "upstream_error" in str(e)

    def _msgs_to_input(self, messages: list[Msg]) -> list[Any]:
        """Convert Msg list → input_items.

        SystemMsg is mapped to ``{"role": "developer"}`` so that it
        persists in the stored conversation and enables prefix-based
        prompt caching across ``previous_response_id`` chains.
        """
        items: list[Any] = []
        for m in messages:
            match m:
                case SystemMsg(content=c):
                    items.append({"role": "developer", "content": c})
                case UserMsg(content=c):
                    items.append({"role": "user", "content": c})
                case AssistantMsg(native=n) if n is not None:
                    items.extend(n)
                case AssistantMsg(response=r):
                    if r.content:
                        items.append({"role": "assistant", "content": r.content})
                case ToolResultMsg(call_id=cid, content=c):
                    items.append({"type": "function_call_output",
                                  "call_id": cid, "output": c})
        return items

    async def chat(self, messages: list[Msg], tools: list[dict],
                   *, previous_response_id: str | None = None,
                   allowed_tools: list[str] | None = None) -> ProviderResponse:
        input_items = self._msgs_to_input(messages)
        params: dict[str, Any] = {
            "model": self._model,
            "input": input_items,
        }
        if self._reasoning_effort is not None:
            params["reasoning"] = {"effort": self._reasoning_effort}
        if self._temperature is not None:
            params["temperature"] = self._temperature
        if tools:
            params["tools"] = tools
        if allowed_tools and self._supports_allowed_tools_choice():
            params["tool_choice"] = {
                "type": "allowed_tools",
                "mode": "required",
                "tools": [{"type": "function", "name": n} for n in allowed_tools],
            }
        if self._cache_key:
            params["prompt_cache_key"] = self._cache_key
        if self._extra_params:
            params.setdefault("extra_body", {})
            params["extra_body"].update(self._extra_params)
        params["store"] = self.STORE
        params["include"] = ["reasoning.encrypted_content"]
        if self.SEND_CACHE_RETENTION:
            params["prompt_cache_retention"] = "24h"
        if self.SEND_MAX_OUTPUT_TOKENS and self.max_output_tokens is not None:
            params["max_output_tokens"] = self.max_output_tokens
        if self.SEND_PREVIOUS_RESPONSE_ID and previous_response_id is not None:
            params["previous_response_id"] = previous_response_id

        # Stream the response, retrying transient errors internally.
        # Falls back to background mode if streaming ran over 15 min
        # before failing, or on any read timeout.
        _BACKOFF_CAP = 30
        _BACKGROUND_THRESHOLD = 900
        _MAX_CHAT_TIME = 3600
        _MAX_STREAM_TIME = self._max_stream_time
        # Consecutive whitespace-only output chars that mark a runaway. Legit
        # JSON/YAML tool args interleave whitespace with content every few dozen
        # chars; thousands of pure-whitespace chars in a row never happen.
        _MAX_WS_RUN = 4096
        _chat_t0 = time()
        attempt = 0
        # Output items streamed via ``response.output_item.done``. Some backends
        # (the openai-oauth proxy fronting the codex backend) emit a
        # ``response.completed`` whose ``output`` is EMPTY even though they
        # streamed the items — so accumulate them and fall back to them when
        # ``response.output`` is empty. The platform API populates
        # ``response.output`` and is therefore unaffected.
        done_items: list[Any] = []
        while True:
            if time() - _chat_t0 >= _MAX_CHAT_TIME:
                self._log("chat() retry budget exhausted (1 hour); giving up")
                raise _TransientError("chat() retry budget exhausted (1 hour)")
            t0 = time()
            try:
                stream = await self._client.responses.create(**params, stream=True)
            except (openai.BadRequestError, openai.NotFoundError) as e:
                if params.get("previous_response_id") is not None:
                    self._log(f"responses.create rejected previous_response_id "
                              f"({type(e).__name__}); retrying without it: {e}")
                    params.pop("previous_response_id", None)
                    continue
                if self._is_transient_upstream_error(e):
                    attempt += 1
                    wait = min(2 ** attempt, _BACKOFF_CAP)
                    self._log(f"responses.create upstream_error "
                              f"({type(e).__name__}, attempt {attempt}, "
                              f"retry in {wait:.0f}s): {e}")
                    await asyncio.sleep(wait)
                    continue
                self._log(f"responses.create failed, non-retryable ({type(e).__name__}): {e}")
                raise
            except openai.RateLimitError as e:
                if "insufficient_quota" in str(e):
                    self._log(f"responses.create quota exhausted: {e}")
                    raise _QuotaError(str(e)) from e
                attempt += 1
                wait = min(2 ** attempt, _BACKOFF_CAP)
                self._log(f"responses.create rate-limited "
                          f"(attempt {attempt}, retry in {wait:.0f}s): {e}")
                await asyncio.sleep(wait)
                continue
            except openai.APIError as e:
                if self.FAIL_FAST_NON_TRANSIENT and isinstance(
                        e, (openai.APIConnectionError, openai.AuthenticationError)):
                    self._fail_fast(e)
                attempt += 1
                wait = min(2 ** attempt, _BACKOFF_CAP)
                self._log(f"responses.create API error "
                          f"(attempt {attempt}, retry in {wait:.0f}s): {e}")
                await asyncio.sleep(wait)
                continue
            attempt = 0

            try:
                async with asyncio.timeout(_MAX_STREAM_TIME):
                    ws_run = 0  # consecutive whitespace-only output chars
                    done_items = []  # reset per streaming attempt
                    async for event in stream:
                        if event.type == "response.completed":
                            response = event.response
                            break
                        elif event.type == "response.output_item.done":
                            _it = getattr(event, "item", None)
                            if _it is not None:
                                done_items.append(_it)
                        elif event.type in (
                                "response.function_call_arguments.delta",
                                "response.output_text.delta"):
                            d = getattr(event, "delta", "") or ""
                            if d.strip():
                                ws_run = 0
                            else:
                                ws_run += len(d)
                                if ws_run > _MAX_WS_RUN:
                                    raise _WhitespaceRunaway(ws_run)
                    else:
                        attempt += 1
                        wait = min(2 ** attempt, _BACKOFF_CAP)
                        self._log(f"stream ended without response.completed "
                                  f"(attempt {attempt}, retry in {wait:.0f}s)")
                        await asyncio.sleep(wait)
                        continue
            except _WhitespaceRunaway as e:
                attempt += 1
                wait = min(2 ** attempt, _BACKOFF_CAP)
                self._log(f"whitespace runaway: {e.args[0]} consecutive whitespace "
                          f"chars in model output with no content; aborting and "
                          f"retrying (attempt {attempt}, retry in {wait:.0f}s)")
                await asyncio.sleep(wait)
                continue
            except TimeoutError:
                attempt += 1
                wait = min(2 ** attempt, _BACKOFF_CAP)
                self._log(f"stream stalled: no response.completed within "
                          f"{_MAX_STREAM_TIME}s; aborting and retrying "
                          f"(attempt {attempt}, retry in {wait:.0f}s)")
                await asyncio.sleep(wait)
                continue
            except httpx.ReadTimeout:
                if not self.BACKGROUND_FALLBACK:
                    attempt += 1
                    wait = min(2 ** attempt, _BACKOFF_CAP)
                    self._log(f"read timeout while streaming; retrying in {wait:.0f}s "
                              f"(background disabled)")
                    await asyncio.sleep(wait)
                    continue
                self._log("read timeout while streaming; falling back to background mode")
                response = await self._resubmit_background(params)
            except (openai.APIError, httpx.TransportError) as e:
                if self.FAIL_FAST_NON_TRANSIENT and isinstance(
                        e, (openai.APIConnectionError, openai.AuthenticationError)):
                    self._fail_fast(e)
                if self.BACKGROUND_FALLBACK and time() - t0 > _BACKGROUND_THRESHOLD:
                    self._log(f"streaming failed after {time() - t0:.0f}s "
                              f"({type(e).__name__}); falling back to background mode: {e}")
                    response = await self._resubmit_background(params)
                elif isinstance(e, openai.APIStatusError) and e.status_code < 500 and not isinstance(e, openai.RateLimitError):
                    self._log(f"streaming failed, non-retryable ({type(e).__name__}): {e}")
                    raise
                else:
                    attempt += 1
                    wait = min(2 ** attempt, _BACKOFF_CAP)
                    self._log(f"streaming error ({type(e).__name__}, "
                              f"attempt {attempt}, retry in {wait:.0f}s): {e}")
                    await asyncio.sleep(wait)
                    continue
            finally:
                await stream.close()
            break

        thinking_parts: list[str] = []
        text_parts: list[str] = []
        tool_calls: list[ToolCall] = []
        output_items = list(response.output) if response.output else done_items

        for item in output_items:
            if item.type == "reasoning":
                if hasattr(item, 'summary') and item.summary:
                    for s in item.summary:
                        if hasattr(s, 'text') and s.text:
                            thinking_parts.append(s.text)
            elif item.type == "function_call":
                tool_calls.append(ToolCall(
                    id=item.call_id or "",
                    name=item.name or "",
                    arguments=item.arguments if item.arguments else "{}"))
            elif item.type == "message":
                for part in (item.content or []):
                    t = getattr(part, 'text', None)
                    if t:
                        text_parts.append(t)

        um = response.usage
        cached = 0
        if um:
            details = getattr(um, 'input_tokens_details', None)
            if details:
                cached = getattr(details, 'cached_tokens', 0) or 0

        # OpenAI input_tokens INCLUDES cached → normalize to uncached input.
        usage = Usage.from_inclusive(
            prompt_tokens=(um.input_tokens or 0) if um else 0,
            output_tokens=(um.output_tokens or 0) if um else 0,
            cached=cached,
        )

        self._last_output_items = output_items
        self.validate_tool_call_json(tool_calls)

        return ProviderResponse(
            content="\n".join(text_parts) if text_parts else None,
            thinking="\n".join(thinking_parts) if thinking_parts else None,
            tool_calls=tool_calls,
            usage=usage,
            response_id=(response.id if self.SURFACE_RESPONSE_ID else None),
        )

    async def _resubmit_background(self, params: dict[str, Any]):
        """Re-submit request in background mode after a streaming timeout.

        Handles all retries internally within a 1-hour time budget.
        """
        _POLL_INTERVAL = 2
        _MAX_TIME = 3600
        t0 = time()

        while True:
            try:
                resp = await self._client.responses.create(**params, background=True)
                break
            except openai.RateLimitError as e:
                if "insufficient_quota" in str(e):
                    self._log(f"background create quota exhausted: {e}")
                    raise _QuotaError(str(e)) from e
                self._log(f"background create rate-limited; retrying in {_POLL_INTERVAL}s: {e}")
            except openai.APIError as e:
                if isinstance(e, openai.APIStatusError) and e.status_code < 500 and not isinstance(e, openai.RateLimitError):
                    self._log(f"background create failed, non-retryable ({type(e).__name__}): {e}")
                    raise
                self._log(f"background create API error; retrying in {_POLL_INTERVAL}s: {e}")
            if time() - t0 >= _MAX_TIME:
                self._log("background create timed out (1 hour); giving up")
                raise _TransientError("Background create timed out")
            await asyncio.sleep(_POLL_INTERVAL)

        response_id = resp.id
        _not_found_count = 0
        while resp.status in ("queued", "in_progress"):
            await asyncio.sleep(_POLL_INTERVAL)
            if time() - t0 >= _MAX_TIME:
                self._log(f"background response {response_id} timed out after {_MAX_TIME}s; giving up")
                raise _TransientError(
                    f"Background response {response_id} timed out after {_MAX_TIME}s")
            try:
                resp = await self._client.responses.retrieve(response_id)
                _not_found_count = 0
            except openai.NotFoundError:
                _not_found_count += 1
                self._log(f"background response {response_id} not found "
                          f"({_not_found_count}/15); retrying")
                if _not_found_count > 15:
                    self._log(f"background response {response_id} not found after "
                              f"{_not_found_count} attempts; giving up")
                    raise _TransientError(
                        f"Background response {response_id} not found after {_not_found_count} attempts")
            except (httpx.TimeoutException, openai.APIConnectionError) as e:
                self._log(f"transient error polling background response {response_id} "
                          f"({type(e).__name__}); retrying: {e}")
        if resp.status == "completed":
            return resp
        self._log(f"background response {response_id} finished with status '{resp.status}'; giving up")
        raise _TransientError(
            f"Background response {response_id} finished with status '{resp.status}'")

    def format_tools(self, tool_info: dict[str, dict[str, Any]]) -> list[dict]:
        strict = self._strict_tools
        return [{"type": "function",
                 "name": name,
                 "description": info["description"],
                 "parameters": self._strict_schema(name, info["schema"]) if strict else info["schema"],
                 **({"strict": True} if strict else {}),
                 } for name, info in tool_info.items()]

    def format_assistant_msg(self, response: ProviderResponse) -> AssistantMsg:
        return AssistantMsg(response=response, native=self._last_output_items)


class CodexResponsesProvider(OpenAIResponsesProvider):
    """Responses provider for the ChatGPT-subscription codex backend, reached via
    the local ``openai-oauth`` proxy. Stateless (store=false, no
    ``previous_response_id``, full transcript resent each turn — the backend
    rejects ``previous_response_id`` over HTTP) and fail-fast when the proxy is
    unreachable. Reasoning items are still resent verbatim (codex-faithful; never
    stripped). See ``OpenAI_Codex_API_driver_plan.md``."""
    STORE                     = False   # codex backend
    SEND_PREVIOUS_RESPONSE_ID = False   # probe-3: 400 over HTTP -> full transcript each turn
    SURFACE_RESPONSE_ID       = False   # response_id None -> loop/fork resend full transcript
    SEND_CACHE_RETENTION      = False   # probe-4: 400 "Unsupported parameter"
    SEND_MAX_OUTPUT_TOKENS    = False   # probe-4: 400 "Unsupported parameter"
    BACKGROUND_FALLBACK       = False   # probe-5: 400 (backend requires stream=true)
    FAIL_FAST_NON_TRANSIENT   = True    # proxy down / 401 -> LMUnreachable -> ResourceUnavailable

    def _supports_allowed_tools_choice(self) -> bool:
        # The allowed_tools object `tool_choice` form is untested on this backend;
        # be conservative (a fork just won't *force* its answer tool — the fork
        # loop re-prompts when no tool is called).
        return False


# ============================================================================
# K2-Think Provider
# ============================================================================

class K2ThinkProvider(OpenAIProvider):
    """Provider for K2-Think (vLLM-served, thinking in <think> tags within content)."""

    _THINK_RE = re.compile(r'^(.*?)</think>\s*', re.DOTALL)

    def __init__(self, base_url: str, model: str, api_key: str | None = None,
                 context_window: int = 131_072):
        super().__init__(
            model=model,
            api_key=api_key or os.environ.get("K2_THINK_API_KEY", "dummy"),
            base_url=base_url,
            cache_key=None,
            default_context_window=context_window,
            temperature=0.2,
            extra_params={"think_budget_tokens": 32_768},
            # 10-min response cap (read timeout). K2 is non-streaming, so the
            # streaming ``max_stream_time`` never applies — the httpx read
            # timeout is the only per-response deadline. Overrides the 1500s
            # ``_DEFAULT_TIMEOUT`` inherited from OpenAIBase.
            timeout=httpx.Timeout(connect=5.0, read=600.0, write=600.0, pool=600.0),
            # The K2 vLLM deployment emits no tool-call deltas while streaming
            # (finish_reason=stop, empty tool_calls) — tools silently never fire.
            # Non-streaming returns the fully-assembled tool_calls correctly.
            use_stream=False,
        )

    def _msgs_to_dicts(self, messages: list[Msg]) -> list[dict]:
        # The K2 vLLM server rejects (HTTP 400) any assistant message in the
        # history that lacks a thinking field, even on turns the model emitted
        # no CoT (e.g. a bare tool call) or that ``_apply_cot_retention`` stripped.
        # It only checks for the field's *presence*, so backfill an empty
        # ``reasoning_content`` placeholder. Replace (never mutate) so a stored
        # ``native`` dict is left intact.
        out = super()._msgs_to_dicts(messages)
        for i, d in enumerate(out):
            if d.get("role") == "assistant" and "reasoning_content" not in d:
                out[i] = {**d, "reasoning_content": ""}
        return out

    async def chat(self, messages: list[Msg], tools: list[dict],
                   *, previous_response_id: str | None = None,
                   allowed_tools: list[str] | None = None) -> ProviderResponse:
        resp = await super().chat(messages, tools, previous_response_id=previous_response_id,
                                  allowed_tools=allowed_tools)
        if resp.content:
            m = self._THINK_RE.match(resp.content)
            if m:
                resp.thinking = m.group(1).strip()
                resp.content = resp.content[m.end():].strip() or None
        return resp

    def pricing(self) -> dict[str, float]:
        return {"input": 0.0, "cached": 0.0, "output": 0.0}


# ============================================================================
# Concrete Driver Registrations
# ============================================================================

@agent_driver("OpenAI")
class APIDriver_OpenAI(APIDriver):
    DEFAULT_MODEL = "gpt-5.5"
    FORK_CHEAPER_MODEL = "gpt-5.5"

    def __init__(self, *args, provider: Provider | None = None,
                 argument: str | None = None, **kwargs):
        if provider is None:
            model, effort = _parse_effort_suffix(argument, self.DEFAULT_MODEL)
            provider = OpenAIResponsesProvider(
                model=model,
                cache_key=f"proof-{uuid.uuid4().hex[:8]}",
                reasoning_effort=effort,
            )
        super().__init__(*args, provider=provider, **kwargs)

    async def _retry_transient(self, fn: Callable[[], Awaitable[_T]]) -> _T:
        """No-op override: ``OpenAIResponsesProvider`` already retries transient
        errors internally and only raises ``_TransientError`` after its 1-hour
        budget is exhausted. The base 10-attempt wrapper would just restart that
        budget each time (~10h worst case), so we skip it and let the error go
        straight to Layer 0 (``_with_retry`` / ``_run_fork``)."""
        return await fn()

    def __str__(self) -> str:
        prov = self._provider
        effort = f"-{prov._reasoning_effort}" if isinstance(prov, OpenAIBase) and prov._reasoning_effort else ""
        return f"{self._driver_name}({prov.model_name}{effort})"

    def estimate_tokens(self, messages: list[Msg]) -> int:
        import tiktoken
        try:
            enc = tiktoken.encoding_for_model(self._provider.model_name)
        except KeyError:
            enc = tiktoken.get_encoding("o200k_base")
        total = 0
        for m in messages:
            match m:
                case SystemMsg(content=c) | UserMsg(content=c) | ToolResultMsg(content=c):
                    total += len(enc.encode(c))
                case AssistantMsg(response=r):
                    if r.content:
                        total += len(enc.encode(r.content))
                    if r.thinking:
                        total += len(enc.encode(r.thinking))
                    for tc in r.tool_calls:
                        total += len(enc.encode(tc.name)) + len(enc.encode(tc.arguments))
        return total

    def _fork_provider(self, mode: ForkingMode) -> Provider:
        if mode == ForkingMode.FORKING_CHEAPER_NO_CTXT and self.FORK_CHEAPER_MODEL:
            parent_prov = self._provider
            effort = (parent_prov._reasoning_effort
                      if isinstance(parent_prov, OpenAIBase) else None)
            cheaper = OpenAIResponsesProvider(
                model=self.FORK_CHEAPER_MODEL,
                cache_key=None,
                reasoning_effort=effort,
            )
            # Freshly built provider never passes through APIDriver.__init__,
            # so wire its Layer-2 logging hook here too.
            cheaper._log = self.warn_AoA_opr
            return cheaper
        return self._provider


@agent_driver("Codex-API")
class APIDriver_OpenAICodex(APIDriver_OpenAI):
    """gpt-5.5 via the ChatGPT-subscription codex backend, through the local
    ``openai-oauth`` proxy (OpenAI-compatible; the proxy owns the OAuth
    lifecycle, so this driver carries no auth code). Reuses APIDriver_OpenAI
    wholesale; only swaps in ``CodexResponsesProvider`` (stateless + fail-fast)
    pointed at the proxy. The proxy is launcher-owned — this driver never starts
    it and fails fast (``LMUnreachable`` -> ``ResourceUnavailable``) if it is
    unreachable. See ``OpenAI_Codex_API_driver_plan.md``."""
    DEFAULT_MODEL      = "gpt-5.5"
    # None ⇒ APIDriver_OpenAI._fork_provider's cheaper-fork guard is falsy, so
    # every fork reuses self._provider (the proxy-configured CodexResponsesProvider)
    # — no second provider is ever built against the real api.openai.com.
    FORK_CHEAPER_MODEL = None

    def __init__(self, *args, provider: Provider | None = None,
                 argument: str | None = None, **kwargs):
        if provider is None:
            model, effort = _parse_effort_suffix(argument, self.DEFAULT_MODEL)
            base_url = os.environ.get(
                "OPENAI_OAUTH_BASE_URL", "http://127.0.0.1:10531/v1")
            provider = CodexResponsesProvider(
                model=model,
                # openai-oauth needs no key (the dummy satisfies the SDK's
                # non-empty-string requirement); key-validating proxies such as
                # auth2api need the configured key via OPENAI_OAUTH_API_KEY.
                api_key=os.environ.get("OPENAI_OAUTH_API_KEY", "openai-oauth-local"),
                base_url=base_url,
                cache_key=f"proof-{uuid.uuid4().hex[:8]}",
                reasoning_effort=effort,
            )
        super().__init__(*args, provider=provider, **kwargs)
        # "perfect input cache" cost accounting for this stateless full-resend
        # path (codex prompt caching is best-effort/intermittent). This reports
        # NOTIONAL, not real, cache counts, so it is OFF by default; set
        # AOA_ASSUME_PERFECT_CACHE to a truthy value (e.g. "1") to enable.
        # See _cache_assumed_usage.
        self._assume_perfect_cache = os.environ.get(
            "AOA_ASSUME_PERFECT_CACHE", "0").strip().lower() in (
                "1", "true", "yes", "on")


@agent_driver("K2-Think")
class APIDriver_K2Think(APIDriver):
    DEFAULT_MODEL = "k2moe375B_mid4_v2_checkpoint_0004000"

    def __init__(self, *args, provider: Provider | None = None,
                 argument: str | None = None, **kwargs):
        if provider is None:
            model = argument or self.DEFAULT_MODEL
            provider = K2ThinkProvider(
                base_url=os.environ.get("K2_BASE_URL", "http://16.78.75.185:8000/v1"),
                model=model,
                api_key=os.environ.get("K2_THINK_API_KEY"),
            )
        super().__init__(*args, provider=provider, **kwargs)


# Per-model context windows (tokens) for the generic Chat driver. The Chat driver
# computes effective = min(this default, CHAT_CONTEXT_WINDOW) and hands it to a
# _ChatProvider, whose context_window returns it verbatim — so this table (plus
# the env cap) is authoritative even for ids that also live in
# OpenAIBase._CONTEXT_WINDOWS (which would otherwise shadow the cap).
# Values mirror each provider's own per-model table (true model maxima), except
# DeepSeek V4 which *supports* 1M (official V4 Model Card, 2026-04-27) but is
# capped here to 384K as a practical default. Unlisted ids fall back to
# _CHAT_DEFAULT_CONTEXT; proxy ids like "deepseek/deepseek-v4-flash" don't match.
_CHAT_DEFAULT_CONTEXT = 131_072
_CHAT_CONTEXT_WINDOWS: dict[str, int] = {
    # OpenAI — gpt series capped to 384K (true maxima: gpt-5.5* / gpt-5.4 = 1.05M
    # per developers.openai.com; gpt-4.1* = 1M). o3 / o4-mini are natively 200K.
    "gpt-5.5-pro":   384_000,
    "gpt-5.5":       384_000,
    "gpt-5.4":       384_000,
    "gpt-4.1":       384_000,
    "gpt-4.1-mini":  384_000,
    "gpt-4.1-nano":  384_000,
    "o3":            200_000,
    "o4-mini":       200_000,
    # Anthropic — 4-6 (1M-capable) capped to 384K; 4-5 are legacy 200k
    # (platform.claude.com models overview).
    "claude-opus-4-6":   384_000,
    "claude-sonnet-4-6": 384_000,
    "claude-opus-4-5":   200_000,
    "claude-sonnet-4-5": 200_000,
    # Gemini (per GeminiProvider._CONTEXT_WINDOWS)
    "gemini-2.5-pro":         1_048_576,
    "gemini-2.5-flash":       1_048_576,
    "gemini-3.1-pro-preview": 1_048_576,
    "gemini-3-flash-preview": 1_048_576,
    # DeepSeek V4 (1M-capable, capped to 384K as a practical default)
    "deepseek-v4-flash": 384_000,
    "deepseek-v4-pro":   384_000,
}


class _ChatProvider(OpenAIChatProvider):
    """OpenAIChatProvider whose context window is fully driver-controlled.

    The base ``context_window`` consults ``OpenAIBase._CONTEXT_WINDOWS`` first,
    which would shadow the per-model default + ``CHAT_CONTEXT_WINDOW`` cap the
    Chat driver computes for OpenAI ids that live in that class table. This
    override always returns the value the driver passed as
    ``default_context_window``.
    """

    @property
    def context_window(self) -> int:
        return self._default_context_window


@agent_driver("Chat")
class APIDriver_Chat(APIDriver):
    """Generic OpenAI-compatible Chat Completions driver.

    Point it at any ``/v1/chat/completions`` endpoint via environment:

      * ``CHAT_BASE_URL``  – e.g. ``https://api.deepseek.com`` or
        ``https://api.openai-next.com/v1`` (required)
      * ``CHAT_API_KEY``   – bearer token for that endpoint
      * ``CHAT_MODEL``     – fallback model id when the driver argument omits one
      * ``CHAT_CONTEXT_WINDOW`` – a *cap* on the context window in tokens. The
        effective window is ``min(per-model default, CHAT_CONTEXT_WINDOW)``; when
        unset the per-model default (``_CHAT_CONTEXT_WINDOWS``, else 131072) is
        used as-is. Use it to compact earlier than the model's real limit, never
        above it. (Compaction fires at 80% of the effective window.)
      * ``CHAT_COT_RETENTION`` – full (default) / latest / none; how much of the
        plaintext ``reasoning_content`` CoT to round-trip (see OpenAIChatProvider)

    The model id is the driver argument after the dot, e.g.
    ``Chat.deepseek-v4-flash`` or ``Chat.deepseek/deepseek-v4-flash``
    (``toplevel`` splits only on the first dot, so slashes survive).
    """

    def __init__(self, *args, provider: Provider | None = None,
                 argument: str | None = None, **kwargs):
        if provider is None:
            raw = argument or os.environ.get("CHAT_MODEL")
            if not raw:
                raise InternalError(
                    "Chat driver needs a model id: use 'Chat.<model>' "
                    "(e.g. Chat.deepseek-v4-flash) or set CHAT_MODEL.")
            model, effort = _parse_effort_suffix(raw, raw, default_effort="high")
            base_url = os.environ.get("CHAT_BASE_URL")
            if not base_url:
                raise InternalError(
                    "Chat driver needs CHAT_BASE_URL set "
                    "(e.g. https://api.deepseek.com).")
            ctx = _CHAT_CONTEXT_WINDOWS.get(model, _CHAT_DEFAULT_CONTEXT)
            cap = os.environ.get("CHAT_CONTEXT_WINDOW")
            if cap:
                ctx = min(ctx, int(cap))
            provider = _ChatProvider(
                model=model,
                base_url=base_url,
                api_key=os.environ.get("CHAT_API_KEY"),
                default_context_window=ctx,
                reasoning_effort=effort,
            )
        super().__init__(*args, provider=provider, **kwargs)

    def __str__(self) -> str:
        prov = self._provider
        effort = f"-{prov._reasoning_effort}" if isinstance(prov, OpenAIBase) and prov._reasoning_effort else ""
        return f"{self._driver_name}({prov.model_name}{effort})"


class DeepSeekProvider(OpenAIChatProvider):
    """Chat Completions provider for DeepSeek V4 (``/beta`` strict).

    Strict mode is applied to the ``edit`` tool ONLY — its schema is sent fully
    inlined (no ``$ref``) with proof fields removed, the only form that keeps the
    schema in the prompt under DeepSeek strict (memory:
    ``deepseek-v4-strict-not-enforced``). All other tools are sent non-strict with
    their raw schemas; ``/beta`` accepts the mix (verified). Enforcement is soft
    even so — the existing error->tool-result->next-turn self-correction is the
    real safety net.
    """

    def _strict_for_tool(self, name: str) -> bool:
        return self._strict_tools and name == "edit"

    def _strict_schema(self, name: str, schema: dict) -> dict:
        if name == "edit":
            return _deepseek_edit_schema()
        return schema


@agent_driver("DeepSeek")
class APIDriver_DeepSeek(APIDriver):
    """DeepSeek driver — ``/beta``, strict on the ``edit`` tool only.

    Driver string ``DeepSeek.V4-pro`` / ``DeepSeek.V4-flash`` (default ``V4-pro``);
    a full model id (``deepseek-v4-...``) may also be passed after the dot.
    Reads ``DEEPSEEK_API_KEY`` (fallback ``CHAT_API_KEY``); base url defaults to
    ``https://api.deepseek.com/beta`` (overridable via ``DEEPSEEK_BASE_URL`` — strict
    needs ``/beta``). CoT retention is pinned to ``full`` (V4 thinking 400s on
    multi-turn tool calls otherwise).
    """

    DEFAULT_MODEL = "deepseek-v4-pro"
    SUBAGENT_NESTING_DEPTH = 2
    # The global-lemma delegation gate is ON for DeepSeek (declare global lemmas,
    # then dispatch a sub-agent to prove them — see model.py Session gate).
    gate_global_lemma_proofs = True

    def __init__(self, *args, provider: Provider | None = None,
                 argument: str | None = None, **kwargs):
        if provider is None:
            arg = (argument or "V4-pro").strip().lower()
            model = f"deepseek-{arg}" if arg in ("v4-pro", "v4-flash") else arg
            api_key = os.environ.get("DEEPSEEK_API_KEY") or os.environ.get("CHAT_API_KEY")
            if not api_key:
                raise InternalError(
                    "DeepSeek driver needs DEEPSEEK_API_KEY (or CHAT_API_KEY) set.")
            # DeepSeek V4 flash & pro both support up to 1M; 384K is a practical
            # default. CHAT_CONTEXT_WINDOW may cap it lower to compact earlier.
            ctx = 384_000
            cap = os.environ.get("CHAT_CONTEXT_WINDOW")
            if cap:
                ctx = min(ctx, int(cap))
            provider = DeepSeekProvider(
                model=model,
                base_url=os.environ.get("DEEPSEEK_BASE_URL", "https://api.deepseek.com/beta"),
                api_key=api_key,
                default_context_window=ctx,
                strict_tools=True,
                cot_retention="full",
                timeout=httpx.Timeout(connect=5.0, read=600.0, write=600.0, pool=600.0),
                max_stream_time=900,
            )
        super().__init__(*args, provider=provider, **kwargs)

    def __str__(self) -> str:
        return f"{self._driver_name}({self._provider.model_name})"
