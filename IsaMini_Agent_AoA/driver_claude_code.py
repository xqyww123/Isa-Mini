from typing import Any, cast
import jsoncomment
import asyncio
import os
import tempfile
import shutil
from .model import *
from . import prompts as P
from claude_agent_sdk import tool, create_sdk_mcp_server, ClaudeAgentOptions, ClaudeSDKClient, HookMatcher
from claude_agent_sdk.types import (
    HookInput,
    HookContext,
    HookJSONOutput,
    PreToolUseHookInput,
)
from io import StringIO
import Isabelle_Semantic_Embedding
from Isabelle_Semantic_Embedding.semantics import mk_query_by_name_tool, mk_query_by_position_tool

type ToolCall_ret = dict[str, Any]
def _mk_ret(str: str) -> ToolCall_ret:
    return {"content": [ {"type": "text", "text": str} ] }

# Load schema for edit tool
_current_file = os.path.abspath(__file__)
_cc_edit_path = os.path.join(os.path.dirname(_current_file), "tools", "cc_edit.jsonc")
with open(_cc_edit_path, "r", encoding="utf-8") as _f:
    _cc_edit_schema = jsoncomment.JsonComment().load(_f)

# Load schema for answer tool
_cc_answer_path = os.path.join(os.path.dirname(_current_file), "tools", "cc_answer.jsonc")
with open(_cc_answer_path, "r", encoding="utf-8") as _f:
    _cc_answer_schema = jsoncomment.JsonComment().load(_f)

# Load schema for cancel tool
_cc_cancel_path = os.path.join(os.path.dirname(_current_file), "tools", "cc_cancel.jsonc")
with open(_cc_cancel_path, "r", encoding="utf-8") as _f:
    _cc_cancel_schema = jsoncomment.JsonComment().load(_f)

def _execute_proof_action(
    session: 'ClaudeCode',
    action: str,
    step: str,
    gen_node: gen_node,
    tool_name: str,
    log_prefix: str
) -> str:
    """Execute a proof action with complete error handling."""
    if not callable(gen_node):
        raise TypeError(f"gen_node must be callable, got {type(gen_node)}")

    try:
        match action:
            case "fill":
                node = session.root.fill(step, gen_node)
                session.refresh_YAML()  # type: ignore[attr-defined]
                response = P.filled_step_message(step, session.root, node)
            case "insert_before":
                raise NotImplementedError(P.NOT_IMPLEMENTED_INSERT_BEFORE)
            case "amend":
                raise NotImplementedError(P.NOT_IMPLEMENTED_AMEND)
            case "delete":
                raise NotImplementedError(P.NOT_IMPLEMENTED_DELETE)
            case "delete_all_after":
                raise NotImplementedError(P.NOT_IMPLEMENTED_DELETE_ALL_AFTER)
            case _:
                raise ArgumentError({"action": action}, P.invalid_action_error(action))

        session.log_tool_response(tool_name, response)
        session.log_proof_tree_snapshot(f"{log_prefix}_step_{step}")
        return response

    except RaiseInteraction as e:
        buffer = StringIO()
        e.interaction.prompt(0, MyIO(buffer))
        session.interaction = e.interaction
        session.suspended_opr = (action, step)  # type: ignore[attr-defined]
        session.log_interaction(tool_name, buffer.getvalue())
        return buffer.getvalue()

    except AoA_Error as e:
        error_msg = str(e)
        session.log_tool_response(tool_name, f"ERROR: {error_msg}")
        return error_msg

# # Simple test tool with minimal schema for debugging
# @tool("test_hello", "A simple test tool to verify MCP server works", {"name": {"type": "string"}})
# async def _test_tool(args: ToolCall_arg) -> ToolCall_ret:
#     """Simple test tool to verify MCP server is discoverable."""
#     name = args.get("name", "World")
#     return {"content": [{"type": "text", "text": f"Hello, {name}! MCP server is working!"}]}

@tool("edit", "Edit the proof.yaml file", input_schema=_cc_edit_schema)
async def _edit_tool(args: ToolCall_arg) -> ToolCall_ret:
    """Edit the proof.yaml file based on provided content."""
    # Get the current session instance
    from .model import the_session
    session = the_session()
    if not isinstance(session, ClaudeCode):
        raise InternalError(f"Expected ClaudeCode session, got {type(session)}")
    session : ClaudeCode = cast(ClaudeCode, session)

    # Log tool call
    session.log_tool_call("mcp__proof__edit", args)

    step = args["target_step"]
    gen_node = Parse_Node(args["proof_operation"])

    response = _execute_proof_action(
        session, args["action"], step, gen_node,
        "mcp__proof__edit", "after_fill"
    )
    return _mk_ret(response)

@tool("answer", "Answer a pending question", input_schema=_cc_answer_schema)
async def _answer_tool(args: ToolCall_arg) -> ToolCall_ret:
    """Answer a pending interaction with the selected indexes."""
    from .model import the_session
    session = the_session()
    if not isinstance(session, ClaudeCode):
        raise InternalError(f"Expected ClaudeCode session, got {type(session)}")
    session : ClaudeCode = cast(ClaudeCode, session)

    # Log tool call
    session.log_tool_call("mcp__proof__answer", args)

    # Check if there's a pending interaction
    if session.interaction is None:
        error_msg = "No pending interaction to answer"
        session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
        return _mk_ret(error_msg)

    # Normalize indexes to satisfy invariant: sorted and all elements distinct
    normalized_indexes = normalize_answer(args["indexes"])

    # Call interaction.answer with the normalized indexes
    gen_node = session.interaction.answer(normalized_indexes)

    # Resume the suspended operation
    suspended = session.suspended_opr  # type: ignore[attr-defined]
    if suspended is None:
        raise InternalError("No suspended operation found despite having an interaction")

    action, step = suspended

    # Clear interaction state BEFORE executing (allows nested interactions)
    session.interaction = None
    session.suspended_opr = None  # type: ignore[attr-defined]

    response = _execute_proof_action(
        session, action, step, gen_node,
        "mcp__proof__answer", "after_answer"
    )

    return _mk_ret(response)

@tool("cancel", "Cancel the pending interaction and abort the current operation", input_schema=_cc_cancel_schema)
async def _cancel_tool(args: ToolCall_arg) -> ToolCall_ret:
    """Cancel a pending interaction."""
    from .model import the_session
    session = the_session()
    if not isinstance(session, ClaudeCode):
        raise InternalError(f"Expected ClaudeCode session, got {type(session)}")
    session : ClaudeCode = cast(ClaudeCode, session)

    session.log_tool_call("mcp__proof__cancel", args)

    if session.interaction is None:
        error_msg = "No pending interaction to cancel"
        session.log_tool_response("mcp__proof__cancel", f"ERROR: {error_msg}")
        return _mk_ret(error_msg)

    # Clear interaction state
    session.interaction = None
    session.suspended_opr = None  # type: ignore[attr-defined]

    response = "Interaction cancelled. The pending operation has been aborted."
    session.log_tool_response("mcp__proof__cancel", response)
    return _mk_ret(response)

@agent_driver("ClaudeCode")
class ClaudeCode(Session):
    TOOL_WHITELIST = [
        'Read',
        'Grep',
        'Write',
        'Edit',
        'Skill',
        'Agent',
        'TaskCreate',
        'TaskGet',
        'TaskList',
        'TaskUpdate',
        'WebFetch',
        'WebSearch',
        'ExitPlanMode',
        'MCPSearch',
        'mcp__proof__edit',
        'mcp__proof__answer',
        'mcp__proof__cancel',
        'mcp__proof__query_by_name',
        'mcp__proof__query_by_position',
        'ToolSearch'
    ]
    TOOL_TO_CALL = [
        'TaskCreate',
        'Agent',
        'Skill',
        'Read',
        'Grep',
        'mcp__proof__edit',
        'mcp__proof__query_by_name',
        'mcp__proof__query_by_position',
    ]

    working_dir: str
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # Create a fresh, empty temporary working directory for each session
        self.working_dir = tempfile.mkdtemp(prefix="agent_AoA_")
        # Check for both read and write permissions
        if not os.access(self.working_dir, os.R_OK | os.W_OK):
            raise InternalError(f"The working directory {self.working_dir} is not readable and writable. Please ensure the temporary directory is writable.")
        self.YAML_path = os.path.join(self.working_dir, "proof.yaml")
        self.suspended_opr: tuple[str, str] | None = None

    def initialize(self, root: Root):
        super().initialize(root)
        with open(self.YAML_path, "w", encoding="utf-8") as f:
            root.print(0, MyIO(f), update_line=True)
        # Build MCP tools — semantic query tools need the Isabelle connection
        connection = root.ml_state.connection
        tools = [
            _edit_tool, _answer_tool, _cancel_tool,
            mk_query_by_name_tool(connection, []),
            mk_query_by_position_tool(connection, []),
        ]
        self.mcp = create_sdk_mcp_server("proof", tools=tools)
        self.options = ClaudeAgentOptions(
            cwd=self.working_dir,
            permission_mode="default",
            allowed_tools=self.TOOL_WHITELIST,
            mcp_servers={"proof": self.mcp},
            hooks={
                "PreToolUse": [
                    HookMatcher(matcher="*", hooks=[self.permission_control]),
                ]
            },
        )

    def run(self):
        asyncio.run(self._run())

    def close(self):
        """Clean up the session and remove the temporary directory."""
        super().close()
        # Remove the temporary working directory
        if hasattr(self, 'working_dir') and os.path.exists(self.working_dir):
            try:
                shutil.rmtree(self.working_dir)
                self.debug_info(f"[CLEANUP] Removed temporary directory: {self.working_dir}")
            except Exception as e:
                self.debug_info(f"[CLEANUP] Failed to remove temporary directory {self.working_dir}: {e}")

    def _get_tool_not_allowed_reason(self, tool: str, tool_input: dict) -> str:
        """Generate detailed rejection reason for tools not in whitelist."""
        reason = P.tool_not_allowed_base(tool)

        if tool == "Edit":
            # Check if editing proof.yaml
            target_file = tool_input.get('file_path', '')
            if target_file.endswith('proof.yaml') or 'proof.yaml' in target_file:
                reason += P.EDIT_TOOL_USE_MCP_FOR_PROOF_YAML
            else:
                reason += P.EDIT_TOOL_ONLY_PROOF_YAML
        elif tool == "AskUserQuestion":
            reason += P.ASK_USER_QUESTION_REJECTION
        elif tool == "Bash":
            reason += P.BASH_REJECTION

        return reason

    async def permission_control(
        self,
        hook_input: HookInput,
        tool_use_id: str | None,
        context: HookContext,
    ) -> HookJSONOutput:
        pre_tool_input = cast(PreToolUseHookInput, hook_input)
        tool = pre_tool_input["tool_name"]
        tool_input = pre_tool_input.get("tool_input") or {}
        cwd = pre_tool_input.get("cwd") or str(self.working_dir)

        # 1. Check if tool is in whitelist
        if tool not in self.TOOL_WHITELIST:
            return {
                "continue_": False,
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "deny",
                    "permissionDecisionReason": self._get_tool_not_allowed_reason(tool, tool_input),
                },
            }

        # 2. Check proof MCP tool interaction state
        if tool.startswith("mcp__proof__"):
            if self.interaction is not None:
                # There's a pending interaction - only allow answer and cancel tools
                if tool not in ("mcp__proof__answer", "mcp__proof__cancel"):
                    return {
                        "continue_": False,
                        "hookSpecificOutput": {
                            "hookEventName": "PreToolUse",
                            "permissionDecision": "deny",
                            "permissionDecisionReason": "There is a pending interaction that must be answered or cancelled first. Use the mcp__proof__answer or mcp__proof__cancel tool.",
                        },
                    }
            else:
                # No pending interaction - reject answer and cancel tools
                if tool in ("mcp__proof__answer", "mcp__proof__cancel"):
                    return {
                        "continue_": False,
                        "hookSpecificOutput": {
                            "hookEventName": "PreToolUse",
                            "permissionDecision": "deny",
                            "permissionDecisionReason": "No pending interaction. The answer and cancel tools can only be used when there is an active interaction.",
                        },
                    }

        # 3. For file tools, check path restrictions
        if tool in ['Read', 'Grep', 'Write', 'Edit']:
            # Get target file path
            target_path = None
            if tool == 'Read':
                target_path = tool_input.get('file_path')
            elif tool == 'Grep':
                target_path = tool_input.get('path')
            elif tool in ['Write', 'Edit']:
                target_path = tool_input.get('file_path')

            if target_path is None:
                if tool == 'Grep':
                    return {}

            # Normalize paths for comparison
            if target_path:
                import os
                target_path_abs = os.path.abspath(os.path.join(cwd, target_path))
                yaml_path_abs = os.path.abspath(self.YAML_path)

                # Normalize path separator for cross-platform checking
                target_path_normalized = target_path_abs.replace(os.sep, '/')

                # Check if path is allowed:
                # 1. Is within any .claude/plan directory (cross-platform check) - allows all operations
                is_in_claude_plan = ("/.claude/plans/" in target_path_normalized or
                                    target_path_normalized.endswith("/.claude/plan"))

                # 2. Matches proof.yaml
                is_yaml = (target_path == self.YAML_path or target_path_abs == yaml_path_abs)

                # Permission logic:
                # - .claude/plan files: allow all tools (Read, Grep, Write, Edit)
                # - proof.yaml: allow only Read and Grep; deny Write and Edit
                if is_in_claude_plan:
                    # Allow all operations for .claude/plan
                    pass
                elif is_yaml:
                    # For proof.yaml, deny Write and Edit
                    if tool in ['Write', 'Edit']:
                        return {
                            "continue_": False,
                            "hookSpecificOutput": {
                                "hookEventName": "PreToolUse",
                                "permissionDecision": "deny",
                                "permissionDecisionReason": f"Cannot use {tool} on proof.yaml. Use the mcp__proof__edit tool instead.",
                            },
                        }
                    # Allow Read and Grep for proof.yaml
                else:
                    # Deny access to all other paths
                    return {
                        "continue_": False,
                        "hookSpecificOutput": {
                            "hookEventName": "PreToolUse",
                            "permissionDecision": "deny",
                            "permissionDecisionReason": P.path_access_denied(tool, self.YAML_path, target_path),
                        },
                    }

        # 4. Passed all checks, allow execution
        return { }

    async def _list_tools(self, client):
        """List all available tools to verify MCP tools are discoverable."""
        await client.query("List all available tools you have access to.")
        async for message in client.receive_response():
            content = getattr(message, "content", None)
            if isinstance(content, list):
                for block in content:
                    text = getattr(block, "text", None)
                    if isinstance(text, str) and text:
                        self.debug_info(f"[TOOLS LIST] {text}")

    async def _run(self):
        async with ClaudeSDKClient(options=self.options) as client:
            # First, list all available tools to verify MCP tools are discoverable
            #await self._list_tools(client)

            await client.query(P.INITIAL_PROMPT)
            while True:
                # Stream model outputs and log them in debug mode
                async for message in client.receive_response():
                    content = getattr(message, "content", None)
                    if isinstance(content, list):
                        for block in content:
                            text = getattr(block, "text", None)
                            if isinstance(text, str) and text:
                                self.log_model_output(text)
                            thinking = getattr(block, "thinking", None)
                            if isinstance(thinking, str) and thinking:
                                self.log_model_thinking(thinking)
                unfinished_nodes = set()
                self.root.unfinished_nodes(unfinished_nodes)
                if unfinished_nodes:
                    retry_prompt = P.RETRY_PROMPT(unfinished_nodes)
                    self.log_retry(unfinished_nodes, retry_prompt)
                    await client.query(retry_prompt)
                else:
                    self.log_proof()
                    return

    def refresh_YAML(self):
        with open(self.YAML_path, 'w') as f:
            self.root.print(0, MyIO(f), update_line=True)
