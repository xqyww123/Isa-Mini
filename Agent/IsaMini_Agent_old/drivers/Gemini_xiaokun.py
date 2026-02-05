import json
from pathlib import Path

import driver
from google import genai
from google.genai import types

MODEL = "gemini-2.5-flash"
max_tool_calls = 50


class Proof_Chat(driver.ProofChat):
    def __init__(self, initial_state_printing: str, log_file: str | None = None):
        self.client = genai.Client()

        self.tool_config = types.ToolConfig(
            function_calling_config=types.FunctionCallingConfig(
                mode=types.FunctionCallingConfigMode.AUTO
            )
        )

        functions_path = Path(__file__).parent.parent.joinpath("prompts/gemini.json")
        self.functions = json.loads(functions_path.read_text())

        system_prompt_path = Path(__file__).parent.parent.joinpath(
            "prompts/gemini_xiaokun.md"
        )
        system_prompt = system_prompt_path.read_text()

        tools = types.Tool(function_declarations=self.functions)
        self.config = types.GenerateContentConfig(
            tools=[tools],
            tool_config=self.tool_config,
            temperature=0.1,
            system_instruction=system_prompt,
        )

        self.max_tool_calls = max_tool_calls  # maximum allowed tool calls
        self.tool_call_count = 0  # initialize tool call counter
        self.contents: list[types.Content] = [
            types.Content(role="user", parts=[types.Part(text=initial_state_printing)])
        ]

        self.proof_plan = None

    def run(self, opr):
        is_proved = False

        while not is_proved:
            response: types.GenerateContentResponse = (
                self.client.models.generate_content(
                    model=MODEL, config=self.config, contents=self.contents
                )
            )

            if not response.candidates or not response.candidates[0].content:
                raise driver.ProofFail("No candidates or contents returned from model")

            model_response_content = response.candidates[0].content
            self.contents.append(model_response_content)

            parts = model_response_content.parts
            function_calls = response.function_calls

            thinking_text = ""
            if parts and parts[0].text:
                thinking_text = parts[0].text
                print(f"[AGENT] Thinking: {thinking_text}")

                if not self.proof_plan:
                    self.proof_plan = thinking_text
                    print("[AGENT] Captured main proof plan.")

            if not function_calls:
                if not thinking_text:
                    print("[AGENT] No function calls or thinking text found.")
            else:
                for function_call in function_calls:
                    if (
                        self.max_tool_calls is not None
                        and self.tool_call_count >= self.max_tool_calls
                    ):
                        raise driver.ProofFail(
                            f"Proof failed: Exceeded maximum allowed tool calls ({self.max_tool_calls})."
                        )

                    try:
                        print(
                            f"[AGENT] Calling tool: {function_call.name}({function_call.args})"
                        )
                        is_proved, opr_response = opr(
                            function_call.name, function_call.args
                        )
                    except Exception as e:
                        print(f"[AGENT] [ERROR] Tool call failed: {e}")
                        is_proved = False
                        opr_response = f"Operation failed: {e}"

                    self.tool_call_count += 1

                    function_response_part = types.Part.from_function_response(
                        name=function_call.name or "none",
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

        tool_response_dict = last_tool_part.function_response.response
        tool_response_str = str(tool_response_dict.get("result", ""))

        if "Operation failed" in tool_response_str or "Fail to " in tool_response_str:
            reminder_text = (
                f"The last tool call ({last_tool_part.function_response.name}) failed:\n"
                f'"{tool_response_str}"\n\n'
                "REMINDER: Your original high-level plan was:\n"
                f"--- MAIN PLAN ---\n{self.proof_plan}\n---\n\n"
                "Do not abandon this step. Please create a 'sub-plan' "
                "using more detailed tools to solve the current subgoal "
                "if necessary."
            )
            print(f"[AGENT] Injecting failure reminder...")
            self.contents.append(
                types.Content(role="user", parts=[types.Part(text=reminder_text)])
            )
