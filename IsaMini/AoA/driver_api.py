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


@dataclass
class ProviderResponse:
    content: str | None
    thinking: str | None
    tool_calls: list[ToolCall]
    usage: Usage


# ============================================================================
# Provider ABC
# ============================================================================

class Provider(ABC):
    """Format-agnostic LLM provider interface.

    The ABC uses generic list[dict] for messages and tools so that future
    non-OpenAI providers (Anthropic, Gemini) can implement the same interface
    with completely different HTTP backends and message formats.
    """

    @abstractmethod
    async def chat(self, messages: list[dict], tools: list[dict]) -> ProviderResponse:
        ...

    @abstractmethod
    def format_tools(self, tool_info: dict[str, dict[str, Any]]) -> list[dict]:
        """Convert {name: {"description": ..., "schema": ...}} to provider-specific tool format."""
        ...

    @abstractmethod
    def format_tool_result(self, tool_call_id: str, content: str) -> dict:
        """Format a tool result message for the conversation history."""
        ...

    @abstractmethod
    def format_assistant_msg(self, response: ProviderResponse) -> dict:
        """Build the assistant message dict to append to history."""
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

class OpenAIProvider(Provider):
    """Provider for any OpenAI-compatible endpoint (ChatGPT, K2-Think, DeepSeek, etc.)."""

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
                 extra_params: dict[str, Any] | None = None):
        self._model = model
        self._client = openai.AsyncOpenAI(
            api_key=api_key or os.environ.get("OPENAI_API_KEY"),
            base_url=base_url,
        )
        self._cache_key = cache_key
        self._default_context_window = default_context_window
        self._temperature = temperature
        self._reasoning_effort = reasoning_effort
        self._extra_params = extra_params or {}

    async def chat(self, messages: list[dict], tools: list[dict]) -> ProviderResponse:
        params: dict[str, Any] = {
            "model": self._model,
            "messages": messages,
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

        response = await self._client.chat.completions.create(**params)
        choice = response.choices[0]
        msg = choice.message

        tool_calls: list[ToolCall] = []
        if msg.tool_calls:
            for tc in msg.tool_calls:
                tool_calls.append(ToolCall(
                    id=tc.id, name=tc.function.name,
                    arguments=tc.function.arguments))

        cached = 0
        if response.usage:
            details = getattr(response.usage, 'prompt_tokens_details', None)
            if details:
                cached = getattr(details, 'cached_tokens', 0) or 0

        usage = Usage(
            input_tokens=response.usage.prompt_tokens if response.usage else 0,
            output_tokens=response.usage.completion_tokens if response.usage else 0,
            cached_tokens=cached,
        )

        return ProviderResponse(
            content=msg.content,
            thinking=None,
            tool_calls=tool_calls,
            usage=usage,
        )

    def format_tools(self, tool_info: dict[str, dict[str, Any]]) -> list[dict]:
        return [{"type": "function", "function": {
            "name": name,
            "description": info["description"],
            "parameters": info["schema"],
        }} for name, info in tool_info.items()]

    def format_tool_result(self, tool_call_id: str, content: str) -> dict:
        return {"role": "tool", "tool_call_id": tool_call_id, "content": content}

    def format_assistant_msg(self, response: ProviderResponse) -> dict:
        msg: dict[str, Any] = {"role": "assistant", "content": response.content}
        if response.tool_calls:
            msg["tool_calls"] = [
                {"id": tc.id, "type": "function",
                 "function": {"name": tc.name, "arguments": tc.arguments}}
                for tc in response.tool_calls
            ]
        return msg

    @property
    def context_window(self) -> int:
        return self._CONTEXT_WINDOWS.get(self._model, self._default_context_window)

    @property
    def model_name(self) -> str:
        return self._model

    def pricing(self) -> dict[str, float]:
        return self._PRICING.get(self._model, {"input": 2.00e-6, "cached": 0.50e-6, "output": 8.00e-6})


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

    async def chat(self, messages: list[dict], tools: list[dict]) -> ProviderResponse:
        resp = await super().chat(messages, tools)
        if resp.content:
            m = self._THINK_RE.match(resp.content)
            if m:
                resp.thinking = m.group(1).strip()
                resp.content = resp.content[m.end():].strip() or None
        return resp

    def format_assistant_msg(self, response: ProviderResponse) -> dict:
        msg: dict[str, Any] = {"role": "assistant", "content": response.content}
        if response.tool_calls:
            msg["tool_calls"] = [
                {"id": tc.id, "type": "function",
                 "function": {"name": tc.name, "arguments": tc.arguments}}
                for tc in response.tool_calls
            ]
        return msg

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

    async def chat(self, messages: list[dict], tools: list[dict]) -> ProviderResponse:
        system_instruction: str | None = None
        msg_start = 0
        if messages and messages[0].get("role") == "system":
            system_instruction = messages[0]["content"]
            msg_start = 1

        contents: list[genai_types.Content] = []
        for msg in messages[msg_start:]:
            gc = msg.get("_gemini_content")
            if gc is not None:
                contents.append(gc)
            elif msg["role"] == "user":
                contents.append(genai_types.Content(
                    role="user", parts=[genai_types.Part(text=msg["content"])]))
            elif msg["role"] == "assistant":
                contents.append(genai_types.Content(
                    role="model", parts=[genai_types.Part(text=msg.get("content") or "")]))
            elif msg["role"] == "tool":
                tc_id = msg["tool_call_id"]
                name = self._call_id_to_name.get(tc_id, "unknown")
                contents.append(genai_types.Content(
                    role="user",
                    parts=[genai_types.Part.from_function_response(
                        name=name, response={"result": msg["content"]})]))

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
            response = await self._async_models.generate_content(
                model=self._model, contents=merged, config=config)
        except genai_errors.ClientError as e:
            if e.code == 429:
                dummy_req = httpx.Request("POST", "https://generativelanguage.googleapis.com/")
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
        self._last_response_content: genai_types.Content | None = None

        if response.candidates and response.candidates[0].content:
            self._last_response_content = response.candidates[0].content
            for part in (response.candidates[0].content.parts or []):
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

        um = response.usage_metadata
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

    def format_tool_result(self, tool_call_id: str, content: str) -> dict:
        name = self._call_id_to_name.get(tool_call_id, "unknown")
        return {
            "role": "tool",
            "tool_call_id": tool_call_id,
            "_gemini_content": genai_types.Content(
                role="user",
                parts=[genai_types.Part.from_function_response(
                    name=name, response={"result": content})]),
        }

    def format_assistant_msg(self, response: ProviderResponse) -> dict:
        msg: dict[str, Any] = {"role": "assistant", "content": response.content}
        if self._last_response_content is not None:
            msg["_gemini_content"] = self._last_response_content
        return msg

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
# APIDriver — Generic Agent Loop
# ============================================================================

class APIDriver(Session):
    """Agent driver that owns the chat loop, calling Provider.chat() directly."""

    COMPACTION_THRESHOLD = 0.80
    DEFAULT_MODEL: str = ""
    FORK_CHEAPER_MODEL: str | None = None

    working_dir: str
    YAML_path: str
    _fork_counter: int
    _fork_name: str

    def __init__(self, *args, provider: Provider,
                 parent: 'APIDriver | None' = None, **kwargs):
        super().__init__(*args, parent=parent, **kwargs)
        self._provider = provider
        self._messages: list[dict] = []
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
        self.log_AoA_opr(f"Working directory: {self.working_dir}, Log directory: {self.log_dir}")
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

    def _system_messages(self) -> list[dict]:
        sp = self.system_prompt()
        return [{"role": "system", "content": sp}] if sp is not None else []

    async def _run_loop(self):
        assert self._executor is not None
        self._messages = [
            *self._system_messages(),
            {"role": "user", "content": self.initial_prompt()},
        ]
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
                        self._provider.format_tool_result(tc.id, text))
            else:
                unfinished: set[Node] = set()
                self.root.unfinished_nodes(unfinished)
                if not unfinished:
                    break
                retry = self.retry_prompt(unfinished)
                self._messages.append({"role": "user", "content": retry})
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

    async def _compact(self, messages: list[dict], tools: list[dict]) -> list[dict]:
        # TODO: polish prompt wording
        messages.append({"role": "user", "content":
            "Please summarize your current proof strategy and progress so far."})
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
        new_messages = [
            *self._system_messages(),
            {"role": "user", "content":
                self.initial_prompt() + "\n\nPrevious progress:\n" + summary},
        ]
        self.log_AoA_opr(f"Compacted. Summary: {summary[:200]}...")
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
            fork_messages = list(self._messages)
        else:
            fork_messages = [*self._system_messages()]

        fork_prompt = "Let's consider a sub-task forked from the context:\n" + prompt_text
        if "answer" not in prompt_text:
            fork_prompt += "\nAnswer the question above by calling the answer tool."
        fork_messages.append({"role": "user", "content": fork_prompt})

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
                            fork_provider.format_tool_result(tc.id, result))
                        fork.total_tool_calls += 1

                assert fork.fork_pending is not None
                if fork.fork_pending.answer.done():
                    fork.log_interaction("fork", f"{tag} completed")
                    break

                if not resp.tool_calls:
                    fork_messages.append({"role": "user", "content":
                        "Call the answer tool to submit your answer."})
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

    def _compute_cost(self):
        p = self._provider.pricing()
        non_cached = max(0, self.total_input_tokens - self.total_cache_read_input_tokens)
        self.total_cost_usd = (
            non_cached * p["input"]
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

    def __init__(self, *args, **kwargs):
        provider = OpenAIProvider(
            model=self.DEFAULT_MODEL,
            cache_key=f"proof-{uuid.uuid4().hex[:8]}",
            reasoning_effort="high",
        )
        super().__init__(*args, provider=provider, **kwargs)

    def _fork_provider(self, mode: ForkingMode) -> Provider:
        if mode == ForkingMode.FORKING_CHEAPER_NO_CTXT and self.FORK_CHEAPER_MODEL:
            return OpenAIProvider(
                model=self.FORK_CHEAPER_MODEL,
                cache_key=None,
            )
        return self._provider


@agent_driver("K2-Think")
class APIDriver_K2Think(APIDriver):
    DEFAULT_MODEL = "moe-375b-mid3-final"

    def __init__(self, *args, **kwargs):
        provider = K2ThinkProvider(
            base_url=os.environ.get("K2_BASE_URL", "http://16.78.75.185:8000/v1"),
            model=self.DEFAULT_MODEL,
            api_key=os.environ.get("K2_THINK_API_KEY"),
        )
        super().__init__(*args, provider=provider, **kwargs)


@agent_driver("Gemini")
class APIDriver_GeminiPro(APIDriver):
    DEFAULT_MODEL = "gemini-3.1-pro-preview"
    FORK_CHEAPER_MODEL = "gemini-3-flash-preview"

    def __init__(self, *args, **kwargs):
        provider = GeminiProvider(
            model=self.DEFAULT_MODEL,
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
