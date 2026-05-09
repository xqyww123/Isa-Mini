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

import anthropic
import httpx
import openai
from google import genai
from google.genai import types as genai_types
from google.genai import errors as genai_errors

from .model import *

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
    async def chat(self, messages: list[Msg], tools: list[dict]) -> ProviderResponse:
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
        "gpt-4.1": 1_048_576,
        "gpt-4.1-mini": 1_048_576,
        "gpt-4.1-nano": 1_048_576,
        "o3": 200_000,
        "o4-mini": 200_000,
    }

    _PRICING: dict[str, dict[str, float]] = {
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

    async def chat(self, messages: list[Msg], tools: list[dict]) -> ProviderResponse:
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
        if self._cache_key:
            params.setdefault("extra_body", {})
            params["extra_body"]["prompt_cache_key"] = self._cache_key
            params["extra_body"]["prompt_cache_retention"] = "24h"
        if self._extra_params:
            params.setdefault("extra_body", {})
            params["extra_body"].update(self._extra_params)

        stream = await self._client.chat.completions.create(
            **params, stream=True,
            stream_options={"include_usage": True})

        text_parts: list[str] = []
        tc_map: dict[int, dict[str, str]] = {}
        stream_usage: Any = None

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
    """Responses protocol (/v1/responses)."""

    def _msgs_to_input(self, messages: list[Msg]) -> tuple[str | None, list[Any]]:
        """Convert Msg list → (instructions, input_items)."""
        instructions: str | None = None
        items: list[Any] = []
        for m in messages:
            match m:
                case SystemMsg(content=c):
                    instructions = c
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
        return instructions, items

    async def chat(self, messages: list[Msg], tools: list[dict]) -> ProviderResponse:
        instructions, input_items = self._msgs_to_input(messages)
        params: dict[str, Any] = {
            "model": self._model,
            "input": input_items,
        }
        if instructions is not None:
            params["instructions"] = instructions
        if self._reasoning_effort is not None:
            params["reasoning"] = {"effort": self._reasoning_effort}
        if self._temperature is not None:
            params["temperature"] = self._temperature
        if tools:
            params["tools"] = tools
        if self._cache_key:
            params["prompt_cache_key"] = self._cache_key
        if self._extra_params:
            params.setdefault("extra_body", {})
            params["extra_body"].update(self._extra_params)
        params["store"] = False
        params["include"] = ["reasoning.encrypted_content"]

        stream = await self._client.responses.create(**params, stream=True)
        response = None
        async for event in stream:
            if event.type == "response.completed":
                response = event.response
        if response is None:
            raise RuntimeError("OpenAI responses stream ended without response.completed event")

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
        )

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

    async def chat(self, messages: list[Msg], tools: list[dict]) -> ProviderResponse:
        resp = await super().chat(messages, tools)
        if resp.content:
            m = self._THINK_RE.match(resp.content)
            if m:
                resp.thinking = m.group(1).strip()
                resp.content = resp.content[m.end():].strip() or None
        return resp

    def pricing(self) -> dict[str, float]:
        return {"input": 0.0, "cached": 0.0, "output": 0.0}


# ============================================================================
# Gemini Provider
# ============================================================================

class GeminiProvider(Provider):
    """Provider for Google Gemini models (2.5 Pro, 2.5 Flash, etc.)."""

    _CONTEXT_WINDOWS: dict[str, int] = {
        "gemini-2.5-pro": 1_048_576,
        "gemini-2.5-flash": 1_048_576,
        "gemini-3.1-pro-preview": 1_048_576,
        "gemini-3-flash-preview": 1_048_576,
    }

    _PRICING: dict[str, dict[str, float]] = {
        "gemini-2.5-pro":           {"input": 1.25e-6, "cached": 0.3125e-6, "output": 10.00e-6},
        "gemini-2.5-flash":         {"input": 0.15e-6, "cached": 0.0375e-6, "output": 0.60e-6},
        "gemini-3.1-pro-preview":   {"input": 2.00e-6, "cached": 0.20e-6,   "output": 12.00e-6},
        "gemini-3-flash-preview":   {"input": 0.50e-6, "cached": 0.05e-6,   "output": 3.00e-6},
    }

    def __init__(self, model: str, api_key: str | None = None,
                 thinking_budget: int = 8192,
                 default_context_window: int = 1_048_576):
        self._model = model
        self._client = genai.Client(
            api_key=api_key or os.environ.get("GEMINI_API_KEY"))
        self._async_models = self._client.aio.models
        self._thinking_budget = thinking_budget
        self._default_context_window = default_context_window
        self._call_id_to_name: dict[str, str] = {}
        self._call_id_counter = 0

    async def chat(self, messages: list[Msg], tools: list[dict]) -> ProviderResponse:
        system_instruction: str | None = None
        contents: list[genai_types.Content] = []
        for m in messages:
            match m:
                case SystemMsg(content=c):
                    system_instruction = c
                case UserMsg(content=c):
                    contents.append(genai_types.Content(
                        role="user", parts=[genai_types.Part(text=c)]))
                case AssistantMsg(native=n) if n is not None:
                    contents.append(n)
                case AssistantMsg(response=r):
                    contents.append(genai_types.Content(
                        role="model", parts=[genai_types.Part(text=r.content or "")]))
                case ToolResultMsg(name=name, content=c):
                    contents.append(genai_types.Content(
                        role="user",
                        parts=[genai_types.Part.from_function_response(
                            name=name, response={"result": c})]))

        merged: list[genai_types.Content] = []
        for c in contents:
            if merged and merged[-1].role == c.role:
                if merged[-1].parts is not None and c.parts is not None:
                    merged[-1].parts.extend(c.parts)
            else:
                merged.append(c)

        config_kwargs: dict[str, Any] = {}
        if system_instruction is not None:
            config_kwargs["system_instruction"] = system_instruction
        if tools:
            config_kwargs["tools"] = tools
            config_kwargs["tool_config"] = genai_types.ToolConfig(
                function_calling_config=genai_types.FunctionCallingConfig(
                    mode=genai_types.FunctionCallingConfigMode.ANY))
        if self._thinking_budget > 0:
            config_kwargs["thinking_config"] = genai_types.ThinkingConfig(
                thinking_budget=self._thinking_budget, include_thoughts=True)
        config_kwargs["temperature"] = 0.6

        config = genai_types.GenerateContentConfig(**config_kwargs)

        try:
            stream = await self._async_models.generate_content_stream(
                model=self._model, contents=merged, config=config)
        except genai_errors.ClientError as e:
            if e.code == 429:
                dummy_req = httpx.Request("POST",
                    self._client._api_client.get_read_only_http_options().get(
                        'base_url', 'https://generativelanguage.googleapis.com/'))
                msg_text = str(e)
                if "quota" in msg_text.lower():
                    msg_text = f"insufficient_quota: {msg_text}"
                raise openai.RateLimitError(
                    message=msg_text,
                    response=httpx.Response(429, text=msg_text, request=dummy_req),
                    body=None) from e
            raise

        thinking_parts: list[str] = []
        text_parts: list[str] = []
        tool_calls: list[ToolCall] = []
        all_parts: list[genai_types.Part] = []
        um: Any = None

        async for chunk in stream:
            if chunk.usage_metadata:
                um = chunk.usage_metadata
            if chunk.candidates and chunk.candidates[0].content:
                for part in (chunk.candidates[0].content.parts or []):
                    all_parts.append(part)
                    if part.thought and part.text:
                        thinking_parts.append(part.text)
                    elif part.function_call:
                        fc = part.function_call
                        call_id = fc.id
                        if not call_id:
                            self._call_id_counter += 1
                            call_id = f"gemini-call-{self._call_id_counter}"
                        self._call_id_to_name[call_id] = fc.name or ""
                        tool_calls.append(ToolCall(
                            id=call_id,
                            name=fc.name or "",
                            arguments=json.dumps(fc.args) if fc.args else "{}"))
                    elif part.text:
                        text_parts.append(part.text)

        self._last_response_content = genai_types.Content(
            role="model", parts=all_parts) if all_parts else None
        usage = Usage(
            input_tokens=(um.prompt_token_count or 0) if um else 0,
            output_tokens=(um.candidates_token_count or 0) if um else 0,
            cached_tokens=(um.cached_content_token_count or 0) if um else 0,
        )

        return ProviderResponse(
            content="\n".join(text_parts) if text_parts else None,
            thinking="\n".join(thinking_parts) if thinking_parts else None,
            tool_calls=tool_calls,
            usage=usage,
        )

    def format_tools(self, tool_info: dict[str, dict[str, Any]]) -> list[dict]:
        decls = [genai_types.FunctionDeclaration(
            name=name,
            description=info["description"],
            parameters_json_schema=(
                _cc_edit_schema_flat if name == "edit" else info["schema"]),
        ) for name, info in tool_info.items()]
        return [genai_types.Tool(function_declarations=decls)]  # type: ignore[list-item]

    def format_assistant_msg(self, response: ProviderResponse) -> AssistantMsg:
        return AssistantMsg(response=response, native=self._last_response_content)

    @property
    def context_window(self) -> int:
        return self._CONTEXT_WINDOWS.get(self._model, self._default_context_window)

    @property
    def model_name(self) -> str:
        return self._model

    def pricing(self) -> dict[str, float]:
        return self._PRICING.get(self._model,
            {"input": 1.25e-6, "cached": 0.3125e-6, "output": 10.00e-6})


# ============================================================================
# Anthropic Provider
# ============================================================================

class AnthropicProvider(Provider):
    """Provider for Anthropic Claude models via the Messages API."""

    _CONTEXT_WINDOWS: dict[str, int] = {
        "claude-opus-4-6": 1_048_576,
        "claude-sonnet-4-6": 1_048_576,
    }

    _PRICING: dict[str, dict[str, float]] = {
        "claude-opus-4-6":   {"input": 5.00e-6, "cache_write": 10.00e-6, "cached": 0.50e-6, "output": 25.00e-6},
        "claude-sonnet-4-6": {"input": 3.00e-6, "cache_write": 3.75e-6,  "cached": 0.30e-6, "output": 15.00e-6},
    }

    def __init__(self, model: str, api_key: str | None = None,
                 thinking_effort: str = "high",
                 default_context_window: int = 1_048_576):
        self._model = model
        self._client = anthropic.AsyncAnthropic(
            api_key=api_key or os.environ.get("CLAUDE_API_KEY") or os.environ.get("ANTHROPIC_API_KEY"),
        )
        self._thinking_effort = thinking_effort
        self._default_context_window = default_context_window
        self._last_response: Any = None

    async def chat(self, messages: list[Msg], tools: list[dict]) -> ProviderResponse:
        system_blocks: list[dict] | None = None
        api_messages: list[dict] = []

        for m in messages:
            match m:
                case SystemMsg(content=c):
                    system_blocks = [
                        {"type": "text", "text": c,
                         "cache_control": {"type": "ephemeral"}}
                    ]
                case UserMsg(content=c):
                    api_messages.append(
                        {"role": "user", "content": [{"type": "text", "text": c}]})
                case AssistantMsg(native=n) if n is not None:
                    api_messages.append(n)
                case AssistantMsg(response=r):
                    content_blocks: list[dict] = []
                    if r.content:
                        content_blocks.append({"type": "text", "text": r.content})
                    for tc in r.tool_calls:
                        content_blocks.append({
                            "type": "tool_use", "id": tc.id,
                            "name": tc.name,
                            "input": json.loads(tc.arguments),
                        })
                    api_messages.append({"role": "assistant", "content": content_blocks})
                case ToolResultMsg(call_id=cid, content=c):
                    block = {"type": "tool_result", "tool_use_id": cid,
                             "content": [{"type": "text", "text": c}]}
                    if (api_messages and api_messages[-1]["role"] == "user"
                            and isinstance(api_messages[-1]["content"], list)
                            and api_messages[-1]["content"]
                            and api_messages[-1]["content"][0].get("type") == "tool_result"):
                        api_messages[-1]["content"].append(block)
                    else:
                        api_messages.append({"role": "user", "content": [block]})

        params: dict[str, Any] = {
            "model": self._model,
            "max_tokens": 128_000,
            "messages": api_messages,
        }
        if system_blocks is not None:
            params["system"] = system_blocks
        if tools:
            params["tools"] = tools
        if self._thinking_effort:
            params["thinking"] = {"type": "adaptive"}
            params["output_config"] = {"effort": self._thinking_effort}

        try:
            raw_stream = await self._client.messages.create(
                    **params,
                    stream=True,
                    extra_headers={"anthropic-beta": "interleaved-thinking-2025-05-14"})
        except anthropic.RateLimitError as e:
            dummy_req = httpx.Request("POST", str(self._client.base_url))
            msg_text = str(e)
            if "quota" in msg_text.lower():
                msg_text = f"insufficient_quota: {msg_text}"
            raise openai.RateLimitError(
                message=msg_text,
                response=httpx.Response(429, text=msg_text, request=dummy_req),
                body=None) from e
        except anthropic.APIStatusError as e:
            if e.status_code in (402, 529):
                dummy_req = httpx.Request("POST", str(self._client.base_url))
                raise openai.RateLimitError(
                    message=f"insufficient_quota: {e}",
                    response=httpx.Response(e.status_code, text=str(e), request=dummy_req),
                    body=None) from e
            raise

        built_blocks: list[Any] = []
        cur: dict[str, Any] = {}
        json_parts: list[str] = []
        usage_info: dict[str, int] = {}

        async for event in raw_stream:
            if event.type == "message_start":
                if hasattr(event, 'message') and hasattr(event.message, 'usage'):
                    u = event.message.usage
                    for k in ("input_tokens", "output_tokens",
                              "cache_read_input_tokens", "cache_creation_input_tokens"):
                        usage_info[k] = getattr(u, k, 0) or 0
            elif event.type == "content_block_start":
                cur = event.content_block.model_dump()
                json_parts = []
            elif event.type == "content_block_delta":
                delta = event.delta
                if delta.type == "text_delta":
                    cur["text"] = cur.get("text", "") + delta.text
                elif delta.type == "thinking_delta":
                    cur["thinking"] = cur.get("thinking", "") + delta.thinking
                elif delta.type == "signature_delta":
                    cur["signature"] = delta.signature
                elif delta.type == "input_json_delta":
                    if delta.partial_json:
                        json_parts.append(delta.partial_json)
            elif event.type == "content_block_stop":
                if cur.get("type") == "tool_use" and json_parts:
                    cur["input"] = json.loads("".join(json_parts))
                btype = cur.get("type")
                if btype == "thinking":
                    built_blocks.append(anthropic.types.ThinkingBlock.model_construct(**cur))
                elif btype == "text":
                    built_blocks.append(anthropic.types.TextBlock.model_construct(**cur))
                elif btype == "tool_use":
                    built_blocks.append(anthropic.types.ToolUseBlock.model_construct(**cur))
                cur = {}
            elif event.type == "message_delta":
                if hasattr(event, 'usage') and event.usage:
                    u = event.usage
                    for k in ("input_tokens", "output_tokens",
                              "cache_read_input_tokens", "cache_creation_input_tokens"):
                        v = getattr(u, k, None)
                        if v:
                            usage_info[k] = v

        response = anthropic.types.Message.model_construct(
            id="",
            type="message",
            role="assistant",
            model=self._model,
            content=built_blocks,
            stop_reason="end_turn",
            stop_sequence=None,
            usage=anthropic.types.Usage.model_construct(_fields_set=None, **usage_info),
        )
        self._last_response = response

        thinking_parts: list[str] = []
        text_parts: list[str] = []
        tool_calls: list[ToolCall] = []

        for block in response.content:
            if block.type == "thinking":
                thinking_parts.append(block.thinking)
            elif block.type == "text":
                text_parts.append(block.text)
            elif block.type == "tool_use":
                tool_calls.append(ToolCall(
                    id=block.id,
                    name=block.name,
                    arguments=json.dumps(block.input),
                ))

        u = response.usage
        usage = Usage(
            input_tokens=u.input_tokens,
            output_tokens=u.output_tokens,
            cached_tokens=getattr(u, 'cache_read_input_tokens', 0) or 0,
            cache_creation_tokens=getattr(u, 'cache_creation_input_tokens', 0) or 0,
        )

        return ProviderResponse(
            content="\n".join(text_parts) if text_parts else None,
            thinking="\n".join(thinking_parts) if thinking_parts else None,
            tool_calls=tool_calls,
            usage=usage,
        )

    def format_tools(self, tool_info: dict[str, dict[str, Any]]) -> list[dict]:
        return [{
            "name": name,
            "description": info["description"],
            "input_schema": info["schema"],
        } for name, info in tool_info.items()]

    def format_assistant_msg(self, response: ProviderResponse) -> AssistantMsg:
        resp = self._last_response
        content_blocks: list[dict] = []
        for block in resp.content:
            if block.type == "thinking":
                tb: dict[str, Any] = {"type": "thinking", "thinking": block.thinking}
                if hasattr(block, 'signature') and block.signature:
                    tb["signature"] = block.signature
                content_blocks.append(tb)
            elif block.type == "text":
                content_blocks.append({"type": "text", "text": block.text})
            elif block.type == "tool_use":
                content_blocks.append({
                    "type": "tool_use", "id": block.id,
                    "name": block.name, "input": block.input,
                })
        native = {"role": "assistant", "content": content_blocks}
        return AssistantMsg(response=response, native=native)

    @property
    def context_window(self) -> int:
        return self._CONTEXT_WINDOWS.get(self._model, self._default_context_window)

    @property
    def model_name(self) -> str:
        return self._model

    def pricing(self) -> dict[str, float]:
        return self._PRICING.get(self._model,
            {"input": 5.00e-6, "cache_write": 10.00e-6, "cached": 0.50e-6, "output": 25.00e-6})


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

class APIDriver(Session):
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
    def _make_fork(cls, parent: 'APIDriver') -> 'APIDriver':
        from .model import _session_var
        try:
            current = _session_var.get()
        except LookupError:
            current = None
        if current is not None:
            raise InternalError(
                "_make_fork must be called in a fresh context")
        return cls(provider=parent._provider, parent=parent)

    async def initialize(self, root: Root):
        await super().initialize(root)
        with open(self.YAML_path, "w", encoding="utf-8") as f:
            root.print(0, MyIO(f), update_line=True, show_warnings=True)
        self._executor = ToolExecutor(self)

    async def run(self):
        self.log_AoA_opr(f"Driver {self}, Working directory: {self.working_dir}, Log directory: {self.log_dir}")
        await self._run_with_retry()

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
            self.root.print(0, MyIO(f), update_line=True, show_warnings=True)

    # ------------------------------------------------------------------
    # Retry Logic
    # ------------------------------------------------------------------

    class _RateLimitError(Exception):
        pass

    class _QuotaError(Exception):
        pass

    async def _run_with_retry(self):
        while True:
            try:
                await self._run_loop()
                return
            except self._QuotaError:
                self.warn_AoA_opr("Quota exhausted, waiting 20min to retry")
                await asyncio.sleep(1200)
            except self._RateLimitError:
                self.warn_AoA_opr("API rate limit, waiting 2s to retry")
                await asyncio.sleep(2)

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

    async def _run_loop(self):
        assert self._executor is not None
        self._budget_start_time = time()
        self._messages = self._initial_messages()
        tools = self._provider.format_tools(self._executor.tool_schemas())

        while not self._interrupted:
            self._model_time_start = time()
            try:
                response = await self._provider.chat(self._messages, tools)
            except openai.RateLimitError as e:
                if "insufficient_quota" in str(e):
                    raise self._QuotaError() from e
                raise self._RateLimitError() from e

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
                if self.check_budget():
                    break
            else:
                unfinished: set[Node] = set()
                self.root.unfinished_nodes(unfinished)
                if not unfinished:
                    break
                self._retry_count += 1
                if self.check_budget():
                    break
                retry = self.retry_prompt(unfinished)
                self._messages.append(UserMsg(retry))
                self.log_retry(unfinished, retry)

            if self._should_compact(response.usage):
                self._messages = await self._compact(self._messages, tools)

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

        self.seen_commands.clear()
        self.seen_entities.clear()
        self.seen_opaque_note = False
        self.showed_suffices_notice = False
        self.showed_fill_hint = False

        self.refresh_YAML()
        new_messages: list[Msg] = []
        sp = self.system_prompt()
        if sp is not None:
            new_messages.append(SystemMsg(sp))
        new_messages.append(UserMsg(
            self.initial_prompt() + "\n\nPrevious progress:\n" + summary))
        new_messages.extend(recent_messages)
        self.log_AoA_opr(f"Compacted. Summary: {summary[:200]}...")
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
        from .model import _session_var, Fork_Pending
        _session_var.set(None)  # type: ignore
        fork = self.__class__._make_fork(self)
        fork.fork_pending = Fork_Pending(
            interaction, asyncio.get_running_loop().create_future())
        fork._executor = ToolExecutor(fork)

        mode = interaction.forking
        if mode == ForkingMode.FORKING_WITH_CTXT:
            fork_messages: list[Msg] = list(self._messages)
        else:
            fork_messages: list[Msg] = []
            sp = self.system_prompt()
            if sp is not None:
                fork_messages.append(SystemMsg(sp))

        fork_prompt = "Let's consider a sub-task forked from the context:\n" + prompt_text
        if "answer" not in prompt_text:
            fork_prompt += "\nAnswer the question above by calling the answer tool."
        fork_messages.append(UserMsg(fork_prompt))

        allowed = interaction.fork_allowed_tools
        all_schemas = fork._executor.tool_schemas()
        fork_tool_info = {k: v for k, v in all_schemas.items() if k in allowed}
        fork_tools = self._provider.format_tools(fork_tool_info)

        fork_provider = self._fork_provider(mode)
        tag = f"[{fork._fork_name}]"
        fork.log_interaction("fork", f"{tag} prompt:\n{prompt_text}")

        try:
            for _ in range(30):
                if fork._interrupted:
                    break
                fork._model_time_start = time()
                try:
                    resp = await fork_provider.chat(fork_messages, fork_tools)
                except openai.RateLimitError as e:
                    if "insufficient_quota" in str(e):
                        raise self._QuotaError() from e
                    raise self._RateLimitError() from e

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
                        result, is_error = await fork._executor.execute(tc.name, args)
                        fork_messages.append(
                            ToolResultMsg(call_id=tc.id, name=tc.name, content=result))
                        fork.total_tool_calls += 1

                assert fork.fork_pending is not None
                if fork.fork_pending.answer.done():
                    fork.log_interaction("fork", f"{tag} completed")
                    break

                if not resp.tool_calls:
                    fork_messages.append(UserMsg(
                        "Call the answer tool to submit your answer."))
                    fork.log_interaction("fork", f"{tag} retrying: no tool calls")
        finally:
            self.total_tool_calls += fork.total_tool_calls
            self.total_isabelle_time += fork.total_isabelle_time
            self.total_model_time += fork.total_model_time
            await fork.close()

        assert fork.fork_pending is not None and fork.fork_pending.answer.done()
        return fork.fork_pending.answer.result()

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

@agent_driver("ChatGPT")
class APIDriver_ChatGPT(APIDriver):
    DEFAULT_MODEL = "gpt-5.5"
    FORK_CHEAPER_MODEL = "gpt-5.5"

    def __init__(self, *args, argument: str | None = None, **kwargs):
        model = argument or self.DEFAULT_MODEL
        provider = OpenAIResponsesProvider(
            model=model,
            cache_key=f"proof-{uuid.uuid4().hex[:8]}",
            reasoning_effort="high",
        )
        super().__init__(*args, provider=provider, **kwargs)

    def _fork_provider(self, mode: ForkingMode) -> Provider:
        if mode == ForkingMode.FORKING_CHEAPER_NO_CTXT and self.FORK_CHEAPER_MODEL:
            return OpenAIResponsesProvider(
                model=self.FORK_CHEAPER_MODEL,
                cache_key=None,
            )
        return self._provider


@agent_driver("K2-Think")
class APIDriver_K2Think(APIDriver):
    DEFAULT_MODEL = "moe-375b-mid3-final"

    def __init__(self, *args, argument: str | None = None, **kwargs):
        model = argument or self.DEFAULT_MODEL
        provider = K2ThinkProvider(
            base_url=os.environ.get("K2_BASE_URL", "http://16.78.75.185:8000/v1"),
            model=model,
            api_key=os.environ.get("K2_THINK_API_KEY"),
        )
        super().__init__(*args, provider=provider, **kwargs)


@agent_driver("Gemini")
class APIDriver_GeminiPro(APIDriver):
    DEFAULT_MODEL = "gemini-3.1-pro-preview"
    FORK_CHEAPER_MODEL = "gemini-3-flash-preview"

    def __init__(self, *args, argument: str | None = None, **kwargs):
        model = argument or self.DEFAULT_MODEL
        provider = GeminiProvider(
            model=model,
            thinking_budget=8192,
        )
        super().__init__(*args, provider=provider, **kwargs)

    def _fork_provider(self, mode: ForkingMode) -> Provider:
        if mode == ForkingMode.FORKING_CHEAPER_NO_CTXT and self.FORK_CHEAPER_MODEL:
            return GeminiProvider(
                model=self.FORK_CHEAPER_MODEL,
                thinking_budget=0,
            )
        return self._provider


@agent_driver("Claude")
class APIDriver_Claude(APIDriver):
    DEFAULT_MODEL = "claude-opus-4-6"

    def __init__(self, *args, argument: str | None = None, **kwargs):
        model = argument or self.DEFAULT_MODEL
        provider = AnthropicProvider(
            model=model,
            thinking_effort="high",
        )
        super().__init__(*args, provider=provider, **kwargs)
