from __future__ import annotations

import json
from pathlib import Path
from typing import Annotated, Any, Literal

import driver
from google import genai
from google.genai import types
from pydantic import BaseModel, ConfigDict, Field, field_validator

MODEL = "gemini-2.5-flash"
max_tool_calls = 50

# --- 1. Argument Models ---
# We create a Pydantic model for each tool's "parameters"
# to ensure strict type checking and handle 'required' fields.


class ATPParams(BaseModel):
    """Arguments for the ATP tool"""

    lemmas: list[str] | None = Field(
        None, description="additional lemmas that can be helpful for proving the goal"
    )
    model_config = ConfigDict(extra="forbid")


class RETRIEVEParams(BaseModel):
    """Arguments for the RETRIEVE tool"""

    patterns: list[str] | None = Field(
        None, description="patterns that the target facts should match"
    )
    negative_patterns: list[str] | None = Field(
        None,
        alias="negative patterns",
        description="negative patterns that the target facts should NOT match",
    )
    names: list[str] | None = Field(
        None, description="substrings that the names of the target facts should contain"
    )
    model_config = ConfigDict(extra="forbid")


class SIMPLIFYParams(BaseModel):
    """Arguments for the SIMPLIFY tool"""

    rules: list[str] | None = Field(
        None, description="Additional simplification rules to use"
    )
    model_config = ConfigDict(extra="forbid")


class UNFOLDParams(BaseModel):
    """Arguments for the UNFOLD tool"""

    targets: list[str] | None = Field(
        None, description="The target constants to unfold"
    )
    model_config = ConfigDict(extra="forbid")


class WITNESSParams(BaseModel):
    """Arguments for the WITNESS tool"""

    # This field is required in the original schema
    witnesses: list[str] = Field(
        description="Terms of witnesses to instantiate. "
        "The number of the terms must be smaller than the number "
        "of the leading existential quantifications in the goal."
    )
    model_config = ConfigDict(extra="forbid")


class RULEParams(BaseModel):
    """Arguments for the RULE tool"""

    rule: str | None = Field(
        None,
        description="The reasoning rule to apply. "
        "If omitted, the default rule will be taken.",
    )
    model_config = ConfigDict(extra="forbid")


class CASESPLITParams(BaseModel):
    """Arguments for the CASE_SPLIT tool"""

    # "target" is required in the original schema
    target: str = Field(description="target term of the case analysis")
    rule: str | None = Field(
        None,
        description="optional case-split rule indicating "
        "non-standard case-split behavior",
    )
    model_config = ConfigDict(extra="forbid")


class INDUCTParams(BaseModel):
    """Arguments for the INDUCT tool"""

    # "target" is required in the original schema
    target: str = Field(description="target term of the induction")
    arbitrary: list[str] | None = Field(
        None,
        description="variables to be re-quantified universally in each induction "
        "subgoal, allowing them to take different values in different inductive "
        "cases, rather than being fixed to a single value throughout the entire "
        "induction",
    )
    rule: str | None = Field(
        None,
        description="optional induction rule indicating how the induction should work",
    )
    model_config = ConfigDict(extra="forbid")


class BRANCHParams(BaseModel):
    """Arguments for the BRANCH tool"""

    cases: list[str] | None = Field(
        None, description="The cases that the proof goal is split into."
    )
    model_config = ConfigDict(extra="forbid")


class HAVEParams(BaseModel):
    """Arguments for the HAVE tool"""

    subgoals: list[str] | None = Field(
        None,
        description="Array of subgoal propositions",
        json_schema_extra={
            "items": {"description": "the expression of each subgoal proposition"}
        },
    )
    model_config = ConfigDict(extra="forbid")


class OBTAINVariable(BaseModel):
    """A variable to be obtained, with its name and optional type."""

    name: str = Field(description="The name of the variable")
    type: str | None = Field(None, description="The type of the variable")


class OBTAINParams(BaseModel):
    """Arguments for the OBTAIN tool"""

    variables: list[OBTAINVariable] | None = Field(
        None, description="variable names and types"
    )
    conditions: list[str] | None = Field(
        None, description="constraints of the variables"
    )
    model_config = ConfigDict(extra="forbid")


class ROLLBACKParams(BaseModel):
    """Arguments for the ROLLBACK tool"""

    # "step" is required in the original schema
    step: int = Field(description="the step number that you expect to rollback")
    model_config = ConfigDict(extra="forbid")


# --- 2. Tool Call Models ---
# Each model represents a specific tool call, using "name" as a Literal type


class ATPTool(BaseModel):
    """Apply powerful Automated Theorem Provers to prove a goal."""

    name: Literal["ATP"] = "ATP"
    arguments: ATPParams


class RETRIEVETool(BaseModel):
    """Retrieves facts from the system knowledge-base"""

    name: Literal["RETRIEVE"] = "RETRIEVE"
    arguments: RETRIEVEParams


class SIMPLIFYTool(BaseModel):
    """Simplify the proof goal"""

    name: Literal["SIMPLIFY"] = "SIMPLIFY"
    arguments: SIMPLIFYParams


class UNFOLDTool(BaseModel):
    """Unfolding definitions."""

    name: Literal["UNFOLD"] = "UNFOLD"
    arguments: UNFOLDParams


class WITNESSTool(BaseModel):
    """Instantiate witnesses of existential quantifications in the proof goal."""

    name: Literal["WITNESS"] = "WITNESS"
    arguments: WITNESSParams


class RULETool(BaseModel):
    """Reduce the proof goal by applying a reasoning rule"""

    name: Literal["RULE"] = "RULE"
    arguments: RULEParams


class CASESPLITTool(BaseModel):
    """Apply structural case analysis over a given term."""

    name: Literal["CASE_SPLIT"] = "CASE_SPLIT"
    arguments: CASESPLITParams


class INDUCTTool(BaseModel):
    """Apply induction over a given term."""

    name: Literal["INDUCT"] = "INDUCT"
    arguments: INDUCTParams


class BRANCHTool(BaseModel):
    """Conduct case-by-case discussion and split the proof goal into cases"""

    name: Literal["BRANCH"] = "BRANCH"
    arguments: BRANCHParams


class HAVETool(BaseModel):
    """Introduce subgoals"""

    name: Literal["HAVE"] = "HAVE"
    arguments: HAVEParams


class OBTAINTool(BaseModel):
    """Extract witnesses from existential statements, e.g., let x be such that P(x)"""

    name: Literal["OBTAIN"] = "OBTAIN"
    arguments: OBTAINParams


class ROLLBACKTool(BaseModel):
    """Rollback to a previous step"""

    name: Literal["ROLLBACK"] = "ROLLBACK"
    arguments: ROLLBACKParams


# --- 3. Final Union Model ---
# Use Annotated and Field(discriminator="name") to create
# an efficient Tagged Union.

ToolCall = Annotated[
    ATPTool
    | RETRIEVETool
    | SIMPLIFYTool
    | UNFOLDTool
    | WITNESSTool
    | RULETool
    | CASESPLITTool
    | INDUCTTool
    | BRANCHTool
    | HAVETool
    | OBTAINTool
    | ROLLBACKTool,
    Field(discriminator="name"),
]

class ToolChoice(BaseModel):
    """
    A model that forces the selection of exactly one tool call
    from the available list of tools.
    """

    thought: str = Field(
        description="A brief, step-by-step reasoning or thought process "
        "that justifies the chosen tool call."
    )
    tool_call: ToolCall = Field(description="The tool call to be executed")

    @field_validator("tool_call", mode="before")
    @classmethod
    def parse_tool_call_args(cls, v: Any) -> Any:
        if isinstance(v, dict) and "arguments" in v and v["arguments"] == {}:
            v["arguments"] = None
        return v

    model_config = ConfigDict(extra="forbid")

class Proof_Chat(driver.ProofChat):
    def __init__(self, initial_state_printing: str):
        self.client = genai.Client()

        system_prompt_path = Path(__file__).parent.parent.joinpath("prompts/gemini_xiaokun.md")
        system_prompt = system_prompt_path.read_text()

        common_config = {
            "temperature": 0.1,
            "system_instruction": system_prompt,
        }

        self.plan_config = types.GenerateContentConfig(**common_config)

        self.step_config = types.GenerateContentConfig(
            **common_config,
            response_mime_type="application/json",
            response_schema=ToolChoice.model_json_schema(),
        )

        self.max_tool_calls = max_tool_calls
        self.tool_call_count = 0
        self.contents: list[types.Content] = [
            types.Content(role="user", parts=[types.Part(text=initial_state_printing)])
        ]
        self.proof_plan = None

        print("[AGENT] Proof_Chat initialized for Structured Output.")

    def run(self, opr):
        is_proved = False

        if not self.proof_plan:
            print("[AGENT] Phase 1: Requesting high-level proof plan...")
            try:
                plan_response: types.GenerateContentResponse = (
                    self.client.models.generate_content(
                        model=MODEL, config=self.plan_config, contents=self.contents
                    )
                )

                if (
                    not plan_response.candidates
                    or not plan_response.candidates[0].content
                ):
                    raise driver.ProofFail("No plan returned from model")

                model_plan_content = plan_response.candidates[0].content
                self.contents.append(model_plan_content)

                if not model_plan_content.parts:
                    raise driver.ProofFail("Model returned empty plan part")

                plan_text = model_plan_content.parts[0].text
                self.proof_plan = plan_text
                print(f"[AGENT] Captured main proof plan:\n{plan_text}")

                plan_follow_up = (
                    "Great. This is the high-level plan. "
                    "Now, please start executing this plan. "
                    "You must respond with your 'thought' and a 'tool_call' "
                    "in the required JSON format for every step."
                )
                self.contents.append(
                    types.Content(role="user", parts=[types.Part(text=plan_follow_up)])
                )

            except Exception as e:
                raise driver.ProofFail(f"Failed to generate proof plan: {e}")

        print("[AGENT] Phase 2: Starting execution loop...")
        while not is_proved:

            self._inject_failure_reminder()

            if (
                self.max_tool_calls is not None
                and self.tool_call_count >= self.max_tool_calls
            ):
                raise driver.ProofFail(
                    f"Proof failed: Exceeded maximum allowed tool calls ({self.max_tool_calls})."
                )

            response: types.GenerateContentResponse = (
                self.client.models.generate_content(
                    model=MODEL, config=self.step_config, contents=self.contents
                )
            )

            if not response.candidates or not response.candidates[0].content:
                raise driver.ProofFail("No candidates or contents returned from model")

            model_response_content = response.candidates[0].content
            self.contents.append(model_response_content)

            if (
                not model_response_content.parts
                or not model_response_content.parts[0].text
            ):
                raise driver.ProofFail("Model returned empty part, expected JSON.")

            json_text = model_response_content.parts[0].text
            tool_name = None

            try:
                data = json.loads(json_text)

                thought_text = data.get("thought", "(No 'thought' provided)")
                print(f"[AGENT] Thinking: {thought_text}")

                tool_call_data = data.get("tool_call")
                if not tool_call_data:
                    raise driver.ProofFail("Model JSON missing 'tool_call' key.")

                tool_name = tool_call_data.get("name")
                tool_args = tool_call_data.get("arguments")

                if not tool_name:
                    raise driver.ProofFail("Model JSON missing 'name' in 'tool_call'.")

                print(f"[AGENT] Calling tool: {tool_name}({tool_args})")

                is_proved, opr_response = opr(tool_name, tool_args)

            except json.JSONDecodeError:
                print(f"[AGENT] [ERROR] Invalid JSON response: {json_text}")
                is_proved = False
                opr_response = f"Operation failed: You did not provide valid JSON. You MUST respond with JSON matching the schema. Response was: {json_text}"
                tool_name = "json_error"
            except Exception as e:
                print(f"[AGENT] [ERROR] Tool call processing failed: {e}")
                is_proved = False
                opr_response = f"Operation failed: {e}"
                tool_name = tool_name or "error"

            self.tool_call_count += 1

            function_response_part = types.Part.from_function_response(
                name=tool_name,
                response={"result": opr_response},
            )
            self.contents.append(
                types.Content(role="tool", parts=[function_response_part])
            )

            if is_proved:
                print("[AGENT] Proof successful!")
                break

    def _inject_failure_reminder(self):
        if (
            not self.proof_plan
            or not self.contents
            or self.contents[-1].role != "tool"
            or not self.contents[-1].parts
        ):
            return

        last_tool_part = self.contents[-1].parts[0]
        if (
            last_tool_part.function_response is None
            or last_tool_part.function_response.response is None
        ):
            return

        try:
            tool_response_dict = last_tool_part.function_response.response
            tool_response_str = str(tool_response_dict.get("result", ""))
        except Exception:
            return

        if "Operation failed" in tool_response_str or "Fail to " in tool_response_str:
            reminder_text = (
                f"The last tool call ({last_tool_part.function_response.name}) failed:\n"
                f'"{tool_response_str}"\n\n'
                "REMINDER: Your original high-level plan was:\n"
                f"--- MAIN PLAN ---\n{self.proof_plan}\n---\n\n"
                "Please analyze the failure and try a different approach or "
                "a more detailed sub-plan to solve the current subgoal."
            )
            print(f"[AGENT] Injecting failure reminder...")
            self.contents.append(
                types.Content(role="user", parts=[types.Part(text=reminder_text)])
            )
