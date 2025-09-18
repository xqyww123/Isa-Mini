"""LangChain-based driver that mirrors the Gemini2 tool execution loop."""

from __future__ import annotations

import json
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

MODEL_NAME = "gemini-2.5-flash"


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
