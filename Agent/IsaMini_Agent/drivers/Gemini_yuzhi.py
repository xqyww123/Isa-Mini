import driver
from google import genai
from google.genai import types
import os
import json

MODEL="gemini-2.5-flash"
max_tool_calls = 10

class Proof_Chat(driver.ProofChat):
    def __init__(self, initial_state_printing):
        self.client = genai.Client()

        self.tool_config = types.ToolConfig(
            function_calling_config=types.FunctionCallingConfig(
                mode="AUTO"
                #mode="AUTO"
            )
        )

        functions = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'prompts', 'gemini.json')
        with open(functions, 'r') as f:
            self.functions = json.load(f)
        
        system_prompt = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'prompts', 'gemini.md')
        with open(system_prompt, 'r') as f:
            system_prompt = f.read()

        tools = types.Tool(function_declarations=self.functions[:3])
        self.config = types.GenerateContentConfig(
                    tools=[tools],
                    tool_config=self.tool_config,
                    temperature=0.1,
                    system_instruction = system_prompt
                )

        self.max_tool_calls = max_tool_calls # maximum allowed tool calls
        self.tool_call_count = 0 # initialize tool call counter
        self.contents = [
            types.Content(
                role="user", parts=[types.Part(text=initial_state_printing)]
            )
        ]

    def run(self, opr):
        is_proved = False
        while not is_proved:
            response = self.client.models.generate_content(
                model=MODEL,
                config=self.config,
                contents=self.contents)
            
            # Always append the model's response to the conversation history,
            # whether it's a text response or a tool call.
            self.contents.append(response.candidates[0].content)

            # Print the model's thinking process if it's a text response
            if not response.function_calls:
                text = response.candidates[0].content.parts[0].text
                print(f"[AGENT] Thinking: {text}")

            function_calls = response.function_calls

            if function_calls: # If there are function calls
                if len(function_calls) == 1:
                    function_call = function_calls[0]
                    is_proved, opr_response = opr(function_call.name, function_call.args)

                    self.tool_call_count += 1 # 每次成功调用工具后增加计数

                    function_response_part = types.Part.from_function_response(
                        name=function_call.name,
                        response={"result": opr_response}
                    )
                    self.contents.append(types.Content(role="tool", parts=[function_response_part]))
                else:
                    # More than one function call, still an error as per original logic
                    raise driver.ProofFail("More than one function call")
            else:
                # No function calls, meaning the model returned text (thinking).
                # The text is already appended to self.contents.
                # The loop will continue, allowing the model to generate next turn.
                pass 

        # If the loop ends but the proof is not complete, and the maximum tool call count has been reached, raise an error
        if not is_proved and self.max_tool_calls is not None and self.tool_call_count >= self.max_tool_calls:
            raise driver.ProofFail(f"Proof failed: Exceeded maximum allowed tool calls ({self.max_tool_calls}).")
