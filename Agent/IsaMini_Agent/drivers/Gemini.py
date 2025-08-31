import driver
from google import genai
from google.genai import types
import os
import json

class Proof_Chat(driver.ProofChat):
    def __init__(self, initial_state_printing):
        self.client = genai.Client()

        self.tool_config2 = types.ToolConfig(
            function_calling_config=types.FunctionCallingConfig(
                mode="NONE"
                #mode="AUTO"
            )
        )

        self.tool_config = types.ToolConfig(
            function_calling_config=types.FunctionCallingConfig(
                mode="ANY"
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
        self.config2 = types.GenerateContentConfig(
                    tools=[tools],
                    tool_config=self.tool_config2,
                    temperature=0.1,
                    system_instruction = system_prompt
                )

        self.contents = [
            #types.Content(
            #    role="system", parts=[types.Part(text=system_prompt)]
            #),
            types.Content(
                role="user", parts=[types.Part(text=initial_state_printing + "\n You should first draft an informal plan.")]
            )
        ]

    def run(self, opr):
        response = self.client.models.generate_content(
            model="gemini-2.5-flash",
            config=self.config2,
            contents=self.contents)
        text = response.candidates[0].content.parts[0].text
        print(text)
        self.contents.append(response.candidates[0].content)
        self.contents.append(types.Content(
                role="user", parts=[types.Part(text="Now let us implement the plan using the operations.")]
            ))
        is_proved = False
        while not is_proved:
            response = self.client.models.generate_content(
                model="gemini-2.5-flash",
                config=self.config,
                contents=self.contents)
            function_calls = response.function_calls
            match function_calls:
                case []:
                    raise driver.ProofFail("No function call found")
                case [function_call]:
                    pass
                case _:
                    raise driver.ProofFail("More than one function call")
            self.contents.append(response.candidates[0].content)

            is_proved, response = opr(function_call.name, function_call.args)

            function_response_part = types.Part.from_function_response(
                name=function_call.name,
                response={"result": response}
            )

            self.contents.append(types.Content(role="user", parts=[function_response_part]))
