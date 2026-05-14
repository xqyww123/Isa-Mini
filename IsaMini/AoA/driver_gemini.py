"""Gemini API driver for IsaMini.AoA."""

from __future__ import annotations

import json
import os
from typing import Any

from google import genai
from google.genai import types as genai_types
from google.genai import errors as genai_errors

from .model import *
from .language_model_driver import _TransientError, _QuotaError
from .driver_api import (
    Provider, ToolCall, Usage, ProviderResponse,
    Msg, SystemMsg, UserMsg, AssistantMsg, ToolResultMsg,
    APIDriver, ForkingMode, agent_driver,
)
from .mcp_http_server import _cc_edit_schema_flat


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

    async def chat(self, messages: list[Msg], tools: list[dict],
                   *, previous_response_id: str | None = None) -> ProviderResponse:
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
                if "quota" in str(e).lower():
                    raise _QuotaError(str(e)) from e
                raise _TransientError(str(e)) from e
            raise
        except genai_errors.ServerError as e:
            raise _TransientError(str(e)) from e

        thinking_parts: list[str] = []
        text_parts: list[str] = []
        tool_calls: list[ToolCall] = []
        all_parts: list[genai_types.Part] = []
        um: Any = None

        try:
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
        except genai_errors.ClientError as e:
            if e.code == 429:
                raise _TransientError(str(e)) from e
            raise
        except genai_errors.ServerError as e:
            raise _TransientError(str(e)) from e

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


@agent_driver("Gemini")
class APIDriver_GeminiPro(APIDriver):
    DEFAULT_MODEL = "gemini-3.1-pro-preview"
    FORK_CHEAPER_MODEL = "gemini-3-flash-preview"

    def __init__(self, *args, provider: Provider | None = None,
                 argument: str | None = None, **kwargs):
        if provider is None:
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
