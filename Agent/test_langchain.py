import datetime
import getpass
import os
import dotenv
from langchain.chat_models import init_chat_model
from langchain_core.messages import HumanMessage, SystemMessage, ToolMessage
from langchain_core.tools import tool

dotenv.load_dotenv()

if not os.environ.get("GOOGLE_API_KEY"): # Use dotenv to load the API key from the .env file
  os.environ["GOOGLE_API_KEY"] = getpass.getpass("Enter API key for Google Gemini: ")

@tool
def get_current_time(time_format: str = "hh:mm:ss") -> str:
    """Get the current time in the specified format (e.g., hh:mm:ss)."""
    # Map user-friendly tokens to strftime
    mapping = {
        "hh:mm:ss": "%H:%M:%S",
        "HH:mm:ss": "%H:%M:%S",
        "YYYY-MM-DD": "%Y-%m-%d",
        "yyyy-MM-dd": "%Y-%m-%d",
    }
    fmt = mapping.get(time_format, "%H:%M:%S")
    return datetime.datetime.now().strftime(fmt)

tools = [get_current_time]

# class ConversationalResponse(TypedDict):
#     """Respond in a conversational manner with a question, ending with a emoji. Be kind and helpful."""

#     response: Annotated[str, ..., "A conversational response to the user's query"]

# class FinalResponse(TypedDict):
#     final_output: Union[Joke, ConversationalResponse]

llm = init_chat_model("gemini-2.5-flash-lite", model_provider="google_genai")

# prompt = ChatPromptTemplate.from_messages([
#     ("system", "You are a helpful assistant named {name} that can answer questions and help with tasks."), 
#     ("user", "{text}")
#     ])

# name = "John"
# text = "Write me a 1 verse song about goldfish on the moon"

# Correct usage: pass variables as keyword args or unpack a dict

# print("--------------------------------")
# prompt.format_prompt(name=name, text=text)
# prompt.pretty_print()
# for chunk in model.stream(prompt):
#     print(chunk.content, end="|", flush=True)
model_with_tools = llm.bind_tools(tools)

# Build a manual tool-execution loop so tool results are fed back
messages = [
    SystemMessage(content="You can call tools to help."),
    HumanMessage(content="What is the current time in the format hh:mm:ss?"),
]

ai = model_with_tools.invoke(messages)
print(ai)

# Execute tool calls (if any), send ToolMessage, and continue
while getattr(ai, "tool_calls", None):
    messages.append(ai)
    for call in ai.tool_calls:
        result = get_current_time.invoke(call["args"])  # executes the tool
        messages.append(ToolMessage(content=result, tool_call_id=call["id"]))
    ai = model_with_tools.invoke(messages)
    print(ai)

print("Final answer:\n", ai.content)
