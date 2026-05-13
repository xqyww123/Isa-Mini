"""Anthropic Claude API driver for IsaMini.AoA."""

from __future__ import annotations

import json
import os
from typing import Any

import anthropic
import httpx
import openai

from .model import *
from .driver_api import (
    Provider, ToolCall, Usage, ProviderResponse,
    Msg, SystemMsg, UserMsg, AssistantMsg, ToolResultMsg,
    APIDriver, agent_driver,
)


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

    async def chat(self, messages: list[Msg], tools: list[dict],
                   *, previous_response_id: str | None = None) -> ProviderResponse:
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


@agent_driver("Claude")
class APIDriver_Claude(APIDriver):
    DEFAULT_MODEL = "claude-opus-4-6"

    def __init__(self, *args, provider: Provider | None = None,
                 argument: str | None = None, **kwargs):
        if provider is None:
            model = argument or self.DEFAULT_MODEL
            provider = AnthropicProvider(
                model=model,
                thinking_effort="high",
            )
        super().__init__(*args, provider=provider, **kwargs)
