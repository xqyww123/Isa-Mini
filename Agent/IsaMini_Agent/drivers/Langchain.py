"""LangChain-based driver that mirrors the Gemini2 tool execution loop."""

from __future__ import annotations

import json
<<<<<<< HEAD
=======
import datetime
>>>>>>> main
import os
from dataclasses import dataclass
from typing import Any, Callable

from dotenv import load_dotenv
from langchain.chat_models import init_chat_model
from langchain_core.messages import AIMessage, HumanMessage, SystemMessage, ToolMessage
from langchain_core.tools import StructuredTool
from pydantic import ConfigDict, Field, create_model
from pydantic.fields import FieldInfo

from driver import ProofChat, ProofFail

load_dotenv()

<<<<<<< HEAD
MODEL_NAME = "gemini-2.5-flash"
=======
MODEL_NAME = "gemini-2.5-pro"
>>>>>>> main


@dataclass
class ConversationState:
    turns: int = 0
    proved: bool = False
    tools_enabled: bool = False
    limit_reached: bool = False


class ToolDispatcher:
    def __init__(self, opr: Callable[[str, dict[str, Any]], tuple[bool, Any]], state: ConversationState, *, max_turns: int) -> None:
        self._opr = opr
        self._state = state
        self._max_turns = max_turns

    def set_enabled(self, enabled: bool) -> None:
        self._state.tools_enabled = enabled

    def dispatch(self, tool_name: str, arguments: dict[str, Any]) -> dict[str, Any]:
        if not self._state.tools_enabled:
            return {
                "proved": False,
                "result": "Tool usage is disabled for this turn.",
            }

        if self._state.turns >= self._max_turns:
            self._state.limit_reached = True
            self._state.tools_enabled = False
            return {
                "proved": False,
                "result": "Tool invocation limit reached; stopping further execution.",
            }

        self._state.turns += 1
        proved, payload = self._opr(tool_name, arguments)
        self._state.proved = proved
        return {"proved": proved, "result": payload}


class Proof_Chat(ProofChat):
    MAX_TURNS = 30

    def __init__(self, initial_state_printing: str):
        self.initial_state_printing = initial_state_printing
        base = os.path.dirname(os.path.dirname(__file__))
        with open(os.path.join(base, "prompts", "gemini.md"), "r", encoding="utf-8") as fh:
            self.system_prompt = fh.read()
        with open(os.path.join(base, "prompts", "gemini.json"), "r", encoding="utf-8") as fh:
            self.function_specs = json.load(fh)
<<<<<<< HEAD
=======
        # Log file for prompts and tool calls (JSON array). 
        self._log_path = os.path.join(os.getcwd(), "cache", "isa_mini_llm_trace.json")
        
        os.makedirs(os.path.dirname(self._log_path), exist_ok=True)
        self._log_events: list[dict[str, Any]] = []

    def _now(self) -> str:
        return datetime.datetime.utcnow().isoformat() + "Z"

    def _append_log(self, record: dict[str, Any]) -> None:
        # Collect logs in-memory; flushed once per run for valid JSON structure
        try:
            self._log_events.append(record)
        except Exception:
            pass

    def _flush_log(self) -> None:
        try:
            with open(self._log_path, "w", encoding="utf-8") as lf:
                json.dump(self._log_events, lf, ensure_ascii=False, indent=2)
        except Exception:
            pass

    @staticmethod
    def _simplify_messages(messages: list[Any]) -> list[dict[str, Any]]:
        def role_of(msg: Any) -> str:
            if isinstance(msg, SystemMessage):
                return "system"
            if isinstance(msg, HumanMessage):
                return "user"
            if isinstance(msg, AIMessage):
                return "assistant"
            if isinstance(msg, ToolMessage):
                return "tool"
            return type(msg).__name__.lower()

        simple: list[dict[str, Any]] = []
        for m in messages:
            content = getattr(m, "content", None)
            simple.append({
                "role": role_of(m),
                "content": Proof_Chat._render_text(content),
            })
        return simple
>>>>>>> main

    @staticmethod
    def _render_text(content: Any) -> str | None:
        if content is None:
            return None
        if isinstance(content, str):
            return content
        if isinstance(content, list):
            parts = [part.get("text") for part in content if isinstance(part, dict) and "text" in part]
            return "\n".join(part for part in parts if part)
        return str(content)

    @staticmethod
    def _pythonize(name: str) -> str:
        return "".join(ch if ch.isalnum() else "_" for ch in name).lower()

    @staticmethod
    def _schema_to_type(schema: dict[str, Any]) -> type:
        schema_type = schema.get("type")
        if schema_type == "string":
            return str
        if schema_type == "integer":
            return int
        if schema_type == "number":
            return float
        if schema_type == "boolean":
            return bool
        if schema_type == "array":
            item_schema = schema.get("items", {})
            item_type = Proof_Chat._schema_to_type(item_schema)
            return list[item_type]  # type: ignore[index]
        return Any

    def _build_tool(self, spec: dict[str, Any], dispatcher: ToolDispatcher) -> StructuredTool:
        json_name: str = spec["name"]
        description: str = spec.get("description", "")
        parameters: dict[str, Any] = spec.get("parameters", {})
        properties: dict[str, Any] = parameters.get("properties", {})
        required: list[str] = parameters.get("required", [])

        fields: dict[str, tuple[type, FieldInfo]] = {}
        for original_name, prop in properties.items():
            field_type = self._schema_to_type(prop)
            py_name = self._pythonize(original_name)
            if original_name in required or field_type == Any:
                annotation = field_type
            else:
                annotation = field_type | None  # type: ignore[operator]
            field_info = Field(
                default=... if original_name in required else None,
                alias=original_name,
                description=prop.get("description"),
            )
            fields[py_name] = (annotation, field_info)

        config = ConfigDict(validate_by_name=True, extra="forbid")
        args_model = create_model(
            f"{json_name}Input",
            __config__=config,
            **fields,
        )

        def tool_func(**kwargs: Any) -> str:
            data = args_model(**kwargs)
            payload = data.model_dump(by_alias=True, exclude_none=True)
            result = dispatcher.dispatch(json_name, payload)
            return json.dumps(result, ensure_ascii=False)

        return StructuredTool.from_function(
            func=tool_func,
            name=json_name,
            description=description,
            args_schema=args_model,
        )

    def run(self, opr: Callable[[str, dict[str, Any]], tuple[bool, Any]]) -> None:
<<<<<<< HEAD
        state = ConversationState()
        dispatcher = ToolDispatcher(opr, state, max_turns=self.MAX_TURNS)
        tools = [self._build_tool(spec, dispatcher) for spec in self.function_specs]
        tool_map = {tool.name: tool for tool in tools}

        planner = init_chat_model(
            MODEL_NAME,
            model_provider="google_genai",
            temperature=0.1,
        )
        executor = planner.bind_tools(tools)

        system_message = SystemMessage(content=self.system_prompt)
        plan_prompt = (
            f"{self.initial_state_printing}\n"
            "You should first draft an informal plan before using any operations."
        )

        dispatcher.set_enabled(False)
        messages: list[Any] = [system_message, HumanMessage(content=plan_prompt)]
        plan_response = planner.invoke(messages)
        if isinstance(plan_response, AIMessage):
            plan_text = self._render_text(plan_response.content)
            if plan_text:
                print("[AGENT]", plan_text)
        messages.append(plan_response)

        dispatcher.set_enabled(True)
        exec_prompt = (
            "Execute your plan now. Call exactly one Isabelle tool at a time and wait for the"
            " returned proof state before deciding on the next action."
        )
        messages.append(HumanMessage(content=exec_prompt))

        while not state.proved and not state.limit_reached:
            response = executor.invoke(messages)
            if not isinstance(response, AIMessage):
                raise ProofFail("LangChain returned a non-AI message response")
            messages.append(response)

            tool_calls = getattr(response, "tool_calls", None) or []
            if not tool_calls:
                raise ProofFail("Model did not request a tool call during execution")
            if len(tool_calls) != 1:
                raise ProofFail("Model requested multiple tool calls in a single turn")

            tool_call = tool_calls[0]
            tool_name = tool_call.get("name")
            if tool_name not in tool_map:
                raise ProofFail(f"Requested unsupported tool: {tool_name}")

            tool = tool_map[tool_name]
            result_text = tool.invoke(tool_call.get("args", {}))
            messages.append(
                ToolMessage(content=result_text, tool_call_id=tool_call["id"])
            )

            if state.limit_reached:
                break

        if state.limit_reached:
            raise ProofFail(f"LangChain stopped after reaching the {self.MAX_TURNS}-tool limit")

        if not state.proved:
            raise ProofFail("LangChain finished without closing all subgoals")

        dispatcher.set_enabled(False)
        closing_prompt = "All subgoals are solved. Provide a concise Isabelle-oriented summary."
        messages.append(HumanMessage(content=closing_prompt))
        final_response = planner.invoke(messages)
        if isinstance(final_response, AIMessage):
            final_text = self._render_text(final_response.content)
            if final_text:
                print("[AGENT]", final_text)
=======
        def _extract_usage(msg: AIMessage) -> tuple[int, int, int]:
            """Return (input_tokens, output_tokens, total_tokens) from an AIMessage.

            Tries LangChain normalized fields first, then provider-specific metadata.
            """
            inp = out = tot = 0
            usage = getattr(msg, "usage_metadata", None)
            meta = getattr(msg, "response_metadata", {}) or {}
            if not usage:
                usage = meta.get("usage_metadata") or meta.get("token_usage") or meta.get("usage") or {}

            if isinstance(usage, dict):
                inp = int(usage.get("input_tokens") or usage.get("prompt_tokens") or usage.get("prompt_token_count") or 0)
                out = int(usage.get("output_tokens") or usage.get("completion_tokens") or usage.get("candidates_token_count") or 0)
                tot = int(usage.get("total_tokens") or usage.get("total_token_count") or (inp + out))
            else:
                inp = int(getattr(usage, "input_tokens", getattr(usage, "prompt_token_count", 0)) or 0)
                out = int(getattr(usage, "output_tokens", getattr(usage, "candidates_token_count", 0)) or 0)
                tot = int(getattr(usage, "total_tokens", getattr(usage, "total_token_count", inp + out)) or (inp + out))

            # Some providers only expose *_token_count directly on response_metadata
            if tot == 0 and meta:
                try:
                    pinp = int(meta.get("prompt_token_count") or meta.get("prompt_tokens") or 0)
                    pout = int(meta.get("candidates_token_count") or meta.get("completion_tokens") or 0)
                    ptot = int(meta.get("total_token_count") or meta.get("total_tokens") or (pinp + pout))
                    inp = max(inp, pinp)
                    out = max(out, pout)
                    tot = max(tot, ptot)
                except Exception:
                    pass

            return inp, out, tot

        try:
            state = ConversationState()
            dispatcher = ToolDispatcher(opr, state, max_turns=self.MAX_TURNS)
            tools = [self._build_tool(spec, dispatcher) for spec in self.function_specs]
            tool_map = {tool.name: tool for tool in tools}

            planner = init_chat_model(
                MODEL_NAME,
                model_provider="google_genai",
            )
            executor = planner.bind_tools(tools)

            system_message = SystemMessage(content=self.system_prompt)
            plan_prompt = (
                f"PROOF CONTEXT:\n{self.initial_state_printing}\n"
                "You should first draft an informal plan before using any tools."
            )

            dispatcher.set_enabled(False)
            messages: list[Any] = [system_message, HumanMessage(content=plan_prompt)]
            # Usage accumulators
            total_in_tokens = 0
            total_out_tokens = 0
            total_tokens = 0

            # Log the planning request
            self._append_log({
                "ts": self._now(),
                "event": "llm_request",
                "phase": "plan",
                "model": MODEL_NAME,
                "tools_enabled": False,
                "turn": state.turns,
                "messages": self._simplify_messages(messages),
            })

            plan_response = executor.invoke(messages)
            if isinstance(plan_response, AIMessage):
                plan_text = self._render_text(plan_response.content)
                if plan_text:
                    print("[AGENT]", plan_text)
                pin, pout, ptot = _extract_usage(plan_response)
                total_in_tokens += pin
                total_out_tokens += pout
                total_tokens += ptot
                # Log the planning response (including any tool call stubs if present)
                self._append_log({
                    "ts": self._now(),
                    "event": "llm_response",
                    "phase": "plan",
                    "model": MODEL_NAME,
                    "turn": state.turns,
                    "text": plan_text,
                    "tool_calls": getattr(plan_response, "tool_calls", None) or [],
                    "usage": {
                        "input_tokens": pin,
                        "output_tokens": pout,
                        "total_tokens": ptot,
                    },
                })
            messages.append(plan_response)

            dispatcher.set_enabled(True)
            exec_prompt = (
                "Execute your plan now. Call exactly one Isabelle tool at a time and wait for the prover feedback before proceeding to the next next."
            )
            messages.append(HumanMessage(content=exec_prompt))

            while not state.proved and not state.limit_reached:
                # Log the execution turn request
                self._append_log({
                    "ts": self._now(),
                    "event": "llm_request",
                    "phase": "exec",
                    "model": MODEL_NAME,
                    "tools_enabled": state.tools_enabled,
                    "turn": state.turns,
                    "messages": self._simplify_messages(messages),
                })

                response = executor.invoke(messages)
                if not isinstance(response, AIMessage):
                    raise ProofFail("LangChain returned a non-AI message response")
                messages.append(response)
                rin, rout, rtot = _extract_usage(response)
                total_in_tokens += rin
                total_out_tokens += rout
                total_tokens += rtot
                # print("[RESPONSE]", response) # DEBUG
                tool_calls = getattr(response, "tool_calls", None) or []
                # Log the model response including tool calls (if any)
                self._append_log({
                    "ts": self._now(),
                    "event": "llm_response",
                    "phase": "exec",
                    "model": MODEL_NAME,
                    "turn": state.turns,
                    "text": self._render_text(response.content),
                    "tool_calls": tool_calls,
                    "usage": {
                        "input_tokens": rin,
                        "output_tokens": rout,
                        "total_tokens": rtot,
                    },
                })
                # if not tool_calls:
                #     raise ProofFail("Model did not request a tool call during execution")
                if len(tool_calls) != 1:
                    raise ProofFail("Model requested multiple tool calls in a single turn")

                # print("[TOOL CALL]", tool_calls) # DEBUG
                tool_call = tool_calls[0] if tool_calls else {}
                tool_name = tool_call.get("name")
                if not tool_name or tool_name not in tool_map:
                    raise ProofFail(f"Requested unsupported tool: {tool_name}")

                tool = tool_map[tool_name]
                tool_args = tool_call.get("args", {})
                # Log the actual tool invocation with arguments
                self._append_log({
                    "ts": self._now(),
                    "event": "tool_call",
                    "phase": "exec",
                    "turn": state.turns + 1,  # incrementing as dispatch will count this turn
                    "name": tool_name,
                    "args": tool_args,
                })
                result_text = tool.invoke(tool_call)
                messages.append(
                    ToolMessage(content=result_text, tool_call_id=tool_call["id"])
                )

                if state.limit_reached:
                    break

            if state.limit_reached:
                raise ProofFail(f"LangChain stopped after reaching the {self.MAX_TURNS}-tool limit")

            if not state.proved:
                raise ProofFail("LangChain finished without closing all subgoals")

            dispatcher.set_enabled(False)
            closing_prompt = "All subgoals are solved. Provide a concise Isabelle-oriented summary."
            messages.append(HumanMessage(content=closing_prompt))
            # Log the final closing request
            self._append_log({
                "ts": self._now(),
                "event": "llm_request",
                "phase": "closing",
                "model": MODEL_NAME,
                "tools_enabled": False,
                "turn": state.turns,
                "messages": self._simplify_messages(messages),
            })

            final_response = planner.invoke(messages)
            if isinstance(final_response, AIMessage):
                final_text = self._render_text(final_response.content)
                if final_text:
                    print("[AGENT]", final_text)
                fin, fout, ftot = _extract_usage(final_response)
                total_in_tokens += fin
                total_out_tokens += fout
                total_tokens += ftot
                # Log the final response
                self._append_log({
                    "ts": self._now(),
                    "event": "llm_response",
                    "phase": "closing",
                    "model": MODEL_NAME,
                    "turn": state.turns,
                    "text": final_text,
                    "tool_calls": getattr(final_response, "tool_calls", None) or [],
                    "usage": {
                        "input_tokens": fin,
                        "output_tokens": fout,
                        "total_tokens": ftot,
                    },
                })

            # Print usage & optional cost summary
            try:
                in_price = float(os.getenv("GEMINI_INPUT_PRICE_PER_1K", "0") or 0)
                out_price = float(os.getenv("GEMINI_OUTPUT_PRICE_PER_1K", "0") or 0)
            except ValueError:
                in_price = out_price = 0.0
            cost = (total_in_tokens / 1000.0) * in_price + (total_out_tokens / 1000.0) * out_price
            print(
                f"[USAGE] input_tokens={total_in_tokens} output_tokens={total_out_tokens} total_tokens={total_tokens}"
            )
            if in_price or out_price:
                print(
                    f"[USAGE] est_cost=${cost:.6f} (in ${in_price}/1K, out ${out_price}/1K)"
                )
        finally:
            # Always flush logs to JSON file even on error
            self._flush_log()
>>>>>>> main
