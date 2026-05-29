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
import re
import shutil
import tempfile
import uuid
from abc import ABC, abstractmethod
from dataclasses import dataclass
from io import StringIO
from time import time
from typing import Any

import httpx
import openai

from .model import *
from .language_model_driver import LMDriver, _TransientError, _QuotaError

from .mcp_http_server import ToolExecutor, _cc_edit_schema_flat
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
class Usage:
    input_tokens: int
    output_tokens: int
    cached_tokens: int
    cache_creation_tokens: int = 0


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

    @abstractmethod
    async def chat(self, messages: list[Msg], tools: list[dict],
                   *, previous_response_id: str | None = None,
                   allowed_tools: list[str] | None = None) -> ProviderResponse:
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


# ============================================================================
# OpenAI-Compatible Provider
# ============================================================================

def _strictify_schema(schema: dict) -> dict:
    """Transform a JSON Schema for OpenAI strict mode.

    - ``additionalProperties: false`` on every object
    - All properties listed in ``required``; optional ones made nullable
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

    _PRICING: dict[str, dict[str, float]] = {
        "gpt-5.5-pro":  {"input": 30.00e-6, "cached": 30.00e-6, "output": 180.00e-6},
        "gpt-5.5":      {"input": 5.00e-6, "cached": 0.50e-6, "output": 30.00e-6},
        "gpt-5.4":      {"input": 2.50e-6, "cached": 0.25e-6, "output": 15.00e-6},
        "gpt-4.1":      {"input": 2.00e-6, "cached": 0.50e-6, "output": 8.00e-6},
        "gpt-4.1-mini": {"input": 0.40e-6, "cached": 0.10e-6, "output": 1.60e-6},
        "gpt-4.1-nano": {"input": 0.10e-6, "cached": 0.025e-6, "output": 0.40e-6},
        "o3":           {"input": 2.00e-6, "cached": 0.50e-6, "output": 8.00e-6},
        "o4-mini":      {"input": 1.10e-6, "cached": 0.275e-6, "output": 4.40e-6},
    }

    def __init__(self, model: str, api_key: str | None = None,
                 base_url: str | None = None, cache_key: str | None = None,
                 default_context_window: int = 128_000,
                 temperature: float | None = None,
                 reasoning_effort: str | None = None,
                 extra_params: dict[str, Any] | None = None,
                 strict_tools: bool = False):
        self._model = model
        self._client = openai.AsyncOpenAI(
            api_key=api_key or os.environ.get("OPENAI_API_KEY"),
            base_url=base_url,
            timeout=httpx.Timeout(connect=5.0, read=1500.0, write=600.0, pool=600.0),
        )
        self._cache_key = cache_key
        self._default_context_window = default_context_window
        self._strict_tools = strict_tools
        self._temperature = temperature
        self._reasoning_effort = reasoning_effort
        self._extra_params = extra_params or {}

    @property
    def context_window(self) -> int:
        return self._CONTEXT_WINDOWS.get(self._model, self._default_context_window)

    @property
    def model_name(self) -> str:
        return self._model

    def pricing(self) -> dict[str, float]:
        return self._PRICING.get(self._model, {"input": 2.00e-6, "cached": 0.50e-6, "output": 8.00e-6})

    def _strict_schema(self, name: str, schema: dict) -> dict:
        if name == "edit":
            return _strictify_schema(_cc_edit_schema_flat)
        return _strictify_schema(schema)


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
                    if r.tool_calls:
                        msg["tool_calls"] = [
                            {"id": tc.id, "type": "function",
                             "function": {"name": tc.name, "arguments": tc.arguments}}
                            for tc in r.tool_calls
                        ]
                    out.append(msg)
                case ToolResultMsg(call_id=cid, content=c):
                    out.append({"role": "tool", "tool_call_id": cid, "content": c})
        return out

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
        if allowed_tools:
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

        try:
            stream = await self._client.chat.completions.create(
                **params, stream=True,
                stream_options={"include_usage": True})
        except openai.RateLimitError as e:
            if "insufficient_quota" in str(e):
                raise _QuotaError(str(e)) from e
            raise _TransientError(str(e)) from e
        except openai.APIError as e:
            raise _TransientError(str(e)) from e

        text_parts: list[str] = []
        tc_map: dict[int, dict[str, str]] = {}
        stream_usage: Any = None

        try:
            async for chunk in stream:
                if chunk.usage:
                    stream_usage = chunk.usage
                if not chunk.choices:
                    continue
                delta = chunk.choices[0].delta
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
        except openai.APIError as e:
            if isinstance(e, openai.APIStatusError) and e.status_code < 500 and not isinstance(e, openai.RateLimitError):
                raise
            raise _TransientError(str(e)) from e

        tool_calls: list[ToolCall] = [
            ToolCall(id=v["id"], name=v["name"], arguments=v["arguments"])
            for _, v in sorted(tc_map.items())]

        cached = 0
        if stream_usage:
            details = getattr(stream_usage, 'prompt_tokens_details', None)
            if details:
                cached = getattr(details, 'cached_tokens', 0) or 0

        usage = Usage(
            input_tokens=stream_usage.prompt_tokens if stream_usage else 0,
            output_tokens=stream_usage.completion_tokens if stream_usage else 0,
            cached_tokens=cached,
        )

        return ProviderResponse(
            content="".join(text_parts) if text_parts else None,
            thinking=None,
            tool_calls=tool_calls,
            usage=usage,
        )

    def format_tools(self, tool_info: dict[str, dict[str, Any]]) -> list[dict]:
        strict = self._strict_tools
        return [{"type": "function", "function": {
            "name": name,
            "description": info["description"],
            "parameters": self._strict_schema(name, info["schema"]) if strict else info["schema"],
            **({"strict": True} if strict else {}),
        }} for name, info in tool_info.items()]

    def format_assistant_msg(self, response: ProviderResponse) -> AssistantMsg:
        msg: dict[str, Any] = {"role": "assistant", "content": response.content}
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
        if allowed_tools:
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
        params["store"] = True
        params["include"] = ["reasoning.encrypted_content"]
        params["prompt_cache_retention"] = "24h"
        if previous_response_id is not None:
            params["previous_response_id"] = previous_response_id

        # Stream the response, retrying transient errors internally.
        # Falls back to background mode if streaming ran over 15 min
        # before failing, or on any read timeout.
        _BACKOFF_CAP = 30
        _BACKGROUND_THRESHOLD = 900
        _MAX_CHAT_TIME = 3600
        _chat_t0 = time()
        attempt = 0
        while True:
            if time() - _chat_t0 >= _MAX_CHAT_TIME:
                raise _TransientError("chat() retry budget exhausted (1 hour)")
            t0 = time()
            try:
                stream = await self._client.responses.create(**params, stream=True)
            except (openai.BadRequestError, openai.NotFoundError):
                if params.get("previous_response_id") is not None:
                    params.pop("previous_response_id", None)
                    continue
                raise
            except openai.RateLimitError as e:
                if "insufficient_quota" in str(e):
                    raise _QuotaError(str(e)) from e
                attempt += 1
                await asyncio.sleep(min(2 ** attempt, _BACKOFF_CAP))
                continue
            except openai.APIError:
                attempt += 1
                await asyncio.sleep(min(2 ** attempt, _BACKOFF_CAP))
                continue
            attempt = 0

            try:
                async for event in stream:
                    if event.type == "response.completed":
                        response = event.response
                        break
                else:
                    attempt += 1
                    await asyncio.sleep(min(2 ** attempt, _BACKOFF_CAP))
                    continue
            except httpx.ReadTimeout:
                response = await self._resubmit_background(params)
            except (openai.APIError, httpx.TransportError) as e:
                if time() - t0 > _BACKGROUND_THRESHOLD:
                    response = await self._resubmit_background(params)
                elif isinstance(e, openai.APIStatusError) and e.status_code < 500 and not isinstance(e, openai.RateLimitError):
                    raise
                else:
                    attempt += 1
                    await asyncio.sleep(min(2 ** attempt, _BACKOFF_CAP))
                    continue
            finally:
                await stream.close()
            break

        thinking_parts: list[str] = []
        text_parts: list[str] = []
        tool_calls: list[ToolCall] = []
        output_items = list(response.output) if response.output else []

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

        usage = Usage(
            input_tokens=(um.input_tokens or 0) if um else 0,
            output_tokens=(um.output_tokens or 0) if um else 0,
            cached_tokens=cached,
        )

        self._last_output_items = output_items

        return ProviderResponse(
            content="\n".join(text_parts) if text_parts else None,
            thinking="\n".join(thinking_parts) if thinking_parts else None,
            tool_calls=tool_calls,
            usage=usage,
            response_id=response.id,
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
                    raise _QuotaError(str(e)) from e
            except openai.APIError as e:
                if isinstance(e, openai.APIStatusError) and e.status_code < 500 and not isinstance(e, openai.RateLimitError):
                    raise
            if time() - t0 >= _MAX_TIME:
                raise _TransientError("Background create timed out")
            await asyncio.sleep(_POLL_INTERVAL)

        response_id = resp.id
        _not_found_count = 0
        while resp.status in ("queued", "in_progress"):
            await asyncio.sleep(_POLL_INTERVAL)
            if time() - t0 >= _MAX_TIME:
                raise _TransientError(
                    f"Background response {response_id} timed out after {_MAX_TIME}s")
            try:
                resp = await self._client.responses.retrieve(response_id)
                _not_found_count = 0
            except openai.NotFoundError:
                _not_found_count += 1
                if _not_found_count > 15:
                    raise _TransientError(
                        f"Background response {response_id} not found after {_not_found_count} attempts")
            except (httpx.TimeoutException, openai.APIConnectionError):
                pass
        if resp.status == "completed":
            return resp
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
        )

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

class APIDriver(LMDriver):
    """Agent driver that owns the chat loop, calling Provider.chat() directly."""

    COMPACTION_THRESHOLD = 0.80
    COMPACTION_RECENT_ROUNDS = 3
    DEFAULT_MODEL: str = ""
    FORK_CHEAPER_MODEL: str | None = None

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
        self._messages: list[Msg] = []
        self._interrupted = False
        self._executor: ToolExecutor | None = None
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
        if self.is_planning:
            with open(self.YAML_path, "w", encoding="utf-8") as f:
                root.print(0, MyIO(f), update_line=True, show_warnings=True)
        elif self.is_worker:
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

    def _initial_messages(self) -> list[Msg]:
        msgs: list[Msg] = []
        sp = self.system_prompt()
        if sp is not None:
            msgs.append(SystemMsg(sp))
        msgs.append(UserMsg(self.initial_prompt()))
        return msgs

    async def _run_agent_loop(self):
        await self._with_retry(self._api_loop)

    async def _api_loop(self):
        assert self._executor is not None
        if self._budget_start_time is None:
            self._budget_start_time = time()
        self._messages = self._initial_messages()
        self._last_response_id = None
        self._msgs_sent_through = 0
        tools = self._provider.format_tools(self._executor.tool_schemas())

        while True:
            while not self._interrupted:
                if self._last_response_id is not None:
                    msgs_to_send = self._messages[self._msgs_sent_through:]
                else:
                    msgs_to_send = self._messages

                self._model_time_start = time()
                response = await self._retry_transient(
                    lambda: self._provider.chat(
                        msgs_to_send, tools,
                        previous_response_id=self._last_response_id))

                if response.response_id is not None:
                    self._last_response_id = response.response_id
                    self._msgs_sent_through = len(self._messages) + 1

                if self._model_time_start is not None:
                    self.total_model_time += time() - self._model_time_start
                    self._model_time_start = None
                self._accumulate_usage(response.usage)

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
                    if self.root.quit_info is not None:
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
                    compacted = await self._compact(self._messages, tools)
                    if compacted is not self._messages:
                        self._last_response_id = None
                        self._msgs_sent_through = 0
                    self._messages = compacted

            if not self._restart_requested:
                break

            self._restart_requested = False
            self._interrupted = False
            self.root.quit_info = None
            self.refresh_YAML()
            self._messages = self._initial_messages()
            self._last_response_id = None
            self._msgs_sent_through = 0
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
        total = usage.input_tokens + usage.output_tokens
        return total > self._provider.context_window * self.COMPACTION_THRESHOLD

    def _find_recent_start(self, messages: list[Msg]) -> int:
        rounds_seen = 0
        for i in range(len(messages) - 1, -1, -1):
            if isinstance(messages[i], AssistantMsg):
                rounds_seen += 1
                if rounds_seen == self.COMPACTION_RECENT_ROUNDS:
                    return i
        return len(self._initial_messages())

    async def _compact(self, messages: list[Msg], tools: list[dict]) -> list[Msg]:
        self.log_AoA_opr(
            f"Compaction triggered: {len(messages)} messages, "
            f"input={self.total_input_tokens} output={self.total_output_tokens}")
        recent_start = self._find_recent_start(messages)
        recent_messages = messages[recent_start:]

        messages.append(UserMsg(COMPACTION_PROMPT))
        try:
            summary_resp = await self._provider.chat(messages, [])
        except Exception:
            self.warn_AoA_opr("Compaction summary request failed, continuing without compaction")
            messages.pop()
            return messages
        summary = summary_resp.content or ""
        self._accumulate_usage(summary_resp.usage)

        self._reset_view_state()

        self.refresh_YAML()
        new_messages: list[Msg] = []
        sp = self.system_prompt()
        if sp is not None:
            new_messages.append(SystemMsg(sp))
        new_messages.append(UserMsg(
            self.initial_prompt() + "\n\nPrevious progress:\n" + summary))
        new_messages.extend(recent_messages)
        est = self.estimate_tokens(new_messages)
        self.log_AoA_opr(f"Compacted to ~{est} tokens ({len(new_messages)} messages). Summary: {summary[:200]}...")
        self._log_meta("COMPACTION", summary=summary)
        return new_messages

    # ------------------------------------------------------------------
    # Forking
    # ------------------------------------------------------------------

    async def fork_interaction(self, interaction: 'Interaction') -> Any:
        buffer = StringIO()
        try:
            await interaction.prompt(0, MyIO(buffer))
        except ImmediateAnswer as e:
            return e.answer

        ctx = contextvars.copy_context()
        task = asyncio.get_running_loop().create_task(
            self._run_fork(interaction, buffer.getvalue()), context=ctx)
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
                    # Pending function_calls: API requires fco before
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

        all_schemas = fork._executor.tool_schemas()
        fork_tools = self._provider.format_tools(all_schemas)

        fork_provider = self._fork_provider(mode)
        tag = f"[{fork._fork_name}]"
        fork.log_interaction("fork", f"{tag} prompt:\n{prompt_text}")
        _pre_input = self.total_input_tokens
        _pre_cached = self.total_cache_read_input_tokens
        _pre_creation = self.total_cache_creation_input_tokens
        _pre_output = self.total_output_tokens

        fork_msgs_sent_through: int = 0

        try:
          while True:
            try:
              for _ in range(30):
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
                    lambda: fork_provider.chat(
                        fork_msgs_to_send, fork_tools,
                        previous_response_id=fork_response_id,
                        allowed_tools=_fork_allowed))

                if resp.response_id is not None:
                    fork_response_id = resp.response_id
                    fork_msgs_sent_through = len(fork_messages) + 1

                if fork._model_time_start is not None:
                    fork.total_model_time += time() - fork._model_time_start
                    fork._model_time_start = None
                self._accumulate_usage(resp.usage)

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
            except _QuotaError:
                self.warn_AoA_opr(f"{tag} Quota exhausted, waiting 20min to retry")
                t0 = time()
                await asyncio.sleep(1200)
                self.total_quota_wait_time += time() - t0
            except _TransientError as e:
                self.warn_AoA_opr(f"{tag} Transient API error, retrying in 2s: {e}")
                await asyncio.sleep(2)
        finally:
            self.total_isabelle_time += fork.total_isabelle_time
            self.total_model_time += fork.total_model_time
            self.total_quota_wait_time += fork.total_quota_wait_time
            await fork.close()

        assert fork.fork_pending is not None and fork.fork_pending.answer.done()
        return fork.fork_pending.answer.result()

    # ------------------------------------------------------------------
    # Lemma Sub-Agent
    # ------------------------------------------------------------------

    async def spawn_lemma_subagent(self, have_node, lemma_name: str) -> bool:
        ctx = contextvars.copy_context()
        task = asyncio.get_running_loop().create_task(
            self._run_lemma_subagent(have_node, lemma_name), context=ctx)
        result = await task
        self.refresh_YAML()
        return result

    async def _run_lemma_subagent(self, have_node, lemma_name: str) -> bool:
        from .model import _session_var, Role_Worker
        _session_var.set(None)  # type: ignore
        sub = self.__class__._make_fork(self, role=Role_Worker(target=have_node))
        sub._fork_name = f"{self._fork_name}.lemma_{lemma_name}"
        await sub.initialize(self.root)

        tag = f"[{sub._fork_name}]"
        self.log_interaction("lemma_subagent", f"{tag} spawned for lemma '{lemma_name}'")

        try:
            await sub._run_agent_loop()
        except asyncio.CancelledError:
            self.warn_AoA_opr(f"{tag} cancelled")
        except Exception as e:
            self.warn_AoA_opr(f"{tag} failed with {type(e).__name__}: {e}")
        finally:
            self.root.quit_info = None
            self._accumulate_subagent_costs(sub)
            await sub.close()

        success = have_node.is_proof_finished()
        self.log_interaction(
            "lemma_subagent",
            f"{tag} {'succeeded' if success else 'failed'} for lemma '{lemma_name}'")
        return success

    # ------------------------------------------------------------------
    # Cost Tracking
    # ------------------------------------------------------------------

    def _accumulate_usage(self, usage: Usage):
        self.total_input_tokens += usage.input_tokens
        self.total_output_tokens += usage.output_tokens
        self.total_cache_read_input_tokens += usage.cached_tokens
        self.total_cache_creation_input_tokens += usage.cache_creation_tokens
        self._log_meta("USAGE",
                       input_tokens=usage.input_tokens,
                       output_tokens=usage.output_tokens,
                       cached_tokens=usage.cached_tokens,
                       cache_creation_tokens=usage.cache_creation_tokens)

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

    def _compute_cost(self):
        p = self._provider.pricing()
        non_cached = max(0, self.total_input_tokens
                         - self.total_cache_read_input_tokens
                         - self.total_cache_creation_input_tokens)
        cache_write_rate = p.get("cache_write", p["input"])
        self.total_cost_usd = (
            non_cached * p["input"]
            + self.total_cache_creation_input_tokens * cache_write_rate
            + self.total_cache_read_input_tokens * p["cached"]
            + self.total_output_tokens * p["output"]
        )


# ============================================================================
# Concrete Driver Registrations
# ============================================================================

def _parse_effort_suffix(argument: str | None, default_model: str
                         ) -> tuple[str, str]:
    """Parse ``"model-effort"`` into ``(model, effort)``.

    Recognised suffixes: ``-high``, ``-medium``, ``-low``.
    Default effort when no suffix is given: ``"medium"``.
    """
    raw = argument or default_model
    for suffix in ("-high", "-medium", "-low"):
        if raw.endswith(suffix):
            return raw[: -len(suffix)], suffix[1:]
    return raw, "medium"


@agent_driver("ChatGPT")
class APIDriver_ChatGPT(APIDriver):
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
            return OpenAIResponsesProvider(
                model=self.FORK_CHEAPER_MODEL,
                cache_key=None,
                reasoning_effort=effort,
            )
        return self._provider


@agent_driver("K2-Think")
class APIDriver_K2Think(APIDriver):
    DEFAULT_MODEL = "moe-375b-mid3-final"

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


