from typing import Any, cast
import jsoncomment
import asyncio
import contextvars
import os
import tempfile
import shutil
from .model import *
from . import prompts as P
from claude_agent_sdk import tool, create_sdk_mcp_server, ClaudeAgentOptions, ClaudeSDKClient, HookMatcher, ResultMessage

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

# Load schema for delete tool
_cc_delete_path = os.path.join(os.path.dirname(_current_file), "tools", "cc_delete.jsonc")
with open(_cc_delete_path, "r", encoding="utf-8") as _f:
    _cc_delete_schema = jsoncomment.JsonComment().load(_f)

# Load schema for semantic search tool
_cc_semantic_search_path = os.path.join(os.path.dirname(_current_file), "tools", "cc_semantic_search.jsonc")
with open(_cc_semantic_search_path, "r", encoding="utf-8") as _f:
    _cc_semantic_search_schema = jsoncomment.JsonComment().load(_f)


class _Prompt(NamedTuple):
    """A prompt string to return to the LLM."""
    text: str

class _Result(NamedTuple):
    """A resolved result (gen_node or Any)."""
    value: Any

async def _handle_raise_interaction(
    session: 'ClaudeCode',
    e: RaiseInteraction,
    tool_name: str,
) -> '_Prompt | _Result':
    """Dispatch a RaiseInteraction. Returns _Prompt (for LLM) or _Result (all done)."""
    wi = Working_Interactions(
        interactions=e.interactions,
        results=[None] * len(e.interactions),
        result_set=[False] * len(e.interactions),
        kontinuation=e.kontinuation,
    )
    session.working_interactions.append(wi)
    n_forking = sum(1 for inter in e.interactions if inter.forking)
    n_inline = len(e.interactions) - n_forking
    session.log_interaction(tool_name,
        f"{len(e.interactions)} interactions ({n_forking} forking, {n_inline} inline)")

    # 1. Launch forking interactions as background tasks (don't await yet)
    forking = [(i, inter) for i, inter in enumerate(e.interactions) if inter.forking]
    if forking:
        session._launch_forks(forking, wi)  # type: ignore[attr-defined]

    # 2. Find first unfinished non-forking interaction
    for i, inter in enumerate(wi.interactions):
        if wi.result_set[i] is False:
            buffer = StringIO()
            inter.prompt(0, MyIO(buffer))
            session.log_tool_response(tool_name, f"[INTERACTION PROMPT]\n{buffer.getvalue()}")
            return _Prompt(buffer.getvalue())

    # 3. All non-forking done — await forks and call continuation
    session.log_interaction("continuation", "all interactions resolved")
    result = await wi.run_continuation()
    session.working_interactions.pop()
    session.log_tool_response(tool_name, f"[INTERACTION RESOLVED] {result}")
    return _Result(result)


async def _execute_proof_action(
    session: 'ClaudeCode',
    action: str,
    step: str,
    gen_node: gen_node,
    tool_name: str,
    log_prefix: str
) -> str:
    """Execute a proof action with complete error handling."""
    session.root.session.age += 1
    if not callable(gen_node):
        raise TypeError(f"gen_node must be callable, got {type(gen_node)}")

    try:
        match action:
            case "fill":
                node = session.root.fill(step, gen_node)
                session.refresh_YAML()  # type: ignore[attr-defined]
                response = await P.filled_step_message(step, session.root, node, session)
            case "insert_before":
                node = session.root.insert_before(step, gen_node)
                session.refresh_YAML()  # type: ignore[attr-defined]
                response = await P.inserted_before_step_message(step, session.root, node, session)
            case "amend":
                node = session.root.amend(step, gen_node)
                session.refresh_YAML()  # type: ignore[attr-defined]
                response = await P.amended_step_message(step, session.root, node, session)
            case _:
                raise ArgumentError({"action": action}, P.invalid_action_error(action))

        session.log_tool_response(tool_name, response)
        session.log_proof_tree_snapshot(f"{log_prefix}_step_{step}")
        return response

    except RaiseInteraction as e:
        # Wrap the continuation: after it returns a gen_node, recurse into _execute_proof_action
        original_kont = e.kontinuation
        async def wrapped_kont(results: list[Any]) -> Any:
            gn = cast(gen_node, await original_kont(results))
            assert callable(gn), \
                "Continuation from _execute_proof_action must return gen_node (callable)"
            return await _execute_proof_action(
                session, action, step, gn, tool_name, log_prefix)
        wrapped_e = RaiseInteraction(e.interactions, wrapped_kont)
        result = await _handle_raise_interaction(session, wrapped_e, tool_name)
        if isinstance(result, _Prompt):
            return result.text
        return result.value # type: ignore[arg-type]

    except AoA_Cancel as e:
        error_msg = f"The edit action is cancelled because:\n{e}"
        session.log_tool_response(tool_name, error_msg)
        return error_msg

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

    try:
        step = args["target_step"]
        try:
            gen_node = Parse_Node(args["proof_operation"])
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__edit", f"ERROR: {error_msg}")
            return _mk_ret(error_msg)

        response = await _execute_proof_action(
            session, args["action"], step, gen_node,
            "mcp__proof__edit", "after_fill"
        )
        return _mk_ret(response)
    except Exception as e:
        session.log_tool_response("mcp__proof__edit", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        raise

@tool("delete", "Delete proof steps", input_schema=_cc_delete_schema)
async def _delete_tool(args: ToolCall_arg) -> ToolCall_ret:
    """Delete one or more proof steps by their step IDs."""
    from .model import the_session
    session = the_session()
    if not isinstance(session, ClaudeCode):
        raise InternalError(f"Expected ClaudeCode session, got {type(session)}")
    session: ClaudeCode = cast(ClaudeCode, session)

    session.log_tool_call("mcp__proof__delete", args)

    try:
        session.root.session.age += 1
        steps = args["target_steps"]
        try:
            session.root.delete(steps)
            session.refresh_YAML()  # type: ignore[attr-defined]
            response = await P.deleted_steps_message(steps, session.root, session)
        except AoA_Cancel as e:
            error_msg = f"The delete action is cancelled because:\n{e}"
            session.log_tool_response("mcp__proof__delete", error_msg)
            return _mk_ret(error_msg)
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__delete", f"ERROR: {error_msg}")
            return _mk_ret(error_msg)

        session.log_tool_response("mcp__proof__delete", response)
        session.log_proof_tree_snapshot("after_delete")
        return _mk_ret(response)
    except Exception as e:
        session.log_tool_response("mcp__proof__delete", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        raise

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

    try:
        if not session.working_interactions:
            error_msg = "No pending interaction to answer"
            session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
            return _mk_ret(error_msg)
        wi = session.working_interactions[-1]  # stack top

        # Find the current (first unfinished non-forking) interaction
        current_idx = None
        for i, inter in enumerate(wi.interactions):
            if wi.result_set[i] is False:
                current_idx = i
                break

        if current_idx is None:
            error_msg = "No pending interaction to answer"
            session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
            return _mk_ret(error_msg)

        current_inter = wi.interactions[current_idx]
        normalized_indexes = normalize_answer(args["indexes"])

        # Process the answer
        try:
            result = current_inter.answer(normalized_indexes)
        except Interaction_BadAnswer as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__answer", f"BAD ANSWER: {error_msg}")
            return _mk_ret(error_msg)
        except RaiseInteraction as e:
            r = await _handle_raise_interaction(session, e, "mcp__proof__answer")
            if isinstance(r, _Prompt):
                return _mk_ret(r.text)
            result = r.value

        # Store the result
        wi.results[current_idx] = result
        wi.result_set[current_idx] = True
        n_done = sum(1 for f in wi.result_set if f is True)
        session.log_interaction("mcp__proof__answer",
            f"answered interaction {current_idx} ({n_done}/{len(wi.interactions)} done)")

        # Find next unfinished non-forking interaction
        for i, inter in enumerate(wi.interactions):
            if wi.result_set[i] is False:
                buffer = StringIO()
                inter.prompt(0, MyIO(buffer))
                session.log_tool_response("mcp__proof__answer", f"[INTERACTION PROMPT]\n{buffer.getvalue()}")
                return _mk_ret(buffer.getvalue())

        # All done — await forks and call continuation
        session.log_interaction("continuation", "all interactions resolved")
        final = await wi.run_continuation()
        session.working_interactions.pop()
        session.log_tool_response("mcp__proof__answer", f"[INTERACTION RESOLVED] {final}")
        if not session.is_major:
            await session.interrupt()
        return _mk_ret(str(final))
    except Exception as e:
        session.log_tool_response("mcp__proof__answer", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        raise

@tool("semantic_search",
      "Search for Isabelle entities by English description using semantic similarity.",
      input_schema=_cc_semantic_search_schema)
async def _semantic_search_tool(args: ToolCall_arg) -> ToolCall_ret:
    from .model import the_session
    session = the_session()
    if not isinstance(session, ClaudeCode):
        raise InternalError(f"Expected ClaudeCode session, got {type(session)}")

    session.log_tool_call("mcp__proof__semantic_search", args)

    try:
        query = args["query"]
        k = args.get("k", 10)
        try:
            kinds = [EntityKind.from_label(label) for label in args["kinds"]]
        except KeyError as e:
            return _mk_ret(f"Invalid entity kind: {e}")

        ml_state = session.root.ml_state
        results = ml_state.semantic_knn(query, k, kinds)

        if not results:
            return _mk_ret("No matching entities found.")

        lines: list[str] = []
        for score, rec in results:
            lines.append(f"- {rec.pretty_print}")
            if rec.interpretation:
                lines.append(f"  {rec.interpretation}")
        return _mk_ret("\n".join(lines))
    except Exception as e:
        session.log_tool_response("mcp__proof__semantic_search", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        raise

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
        'mcp__proof__delete',
        'mcp__proof__answer',
        'mcp__proof__query_by_name',
        'mcp__proof__query_by_position',
        'mcp__proof__semantic_search',
        'ToolSearch'
    ]
    FORK_WHITELIST = [t for t in TOOL_WHITELIST if t not in ('mcp__proof__edit', 'mcp__proof__delete')]
    TOOL_TO_CALL = [
        'TaskCreate',
        'Agent',
        'Skill',
        'Read',
        'Grep',
        'mcp__proof__edit',
        'mcp__proof__delete',
        'mcp__proof__query_by_name',
        'mcp__proof__query_by_position',
        'mcp__proof__semantic_search',
    ]

    working_dir: str
    _fork_counter: int
    _fork_name: str
    _fork_index: int | None

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # Create a fresh, empty temporary working directory for each session
        self.working_dir = tempfile.mkdtemp(prefix="agent_AoA_")
        # Check for both read and write permissions
        if not os.access(self.working_dir, os.R_OK | os.W_OK):
            raise InternalError(f"The working directory {self.working_dir} is not readable and writable. Please ensure the temporary directory is writable.")
        self.YAML_path = os.path.join(self.working_dir, "proof.yaml")
        self._session_id: str | None = None
        self._fork_counter = 0
        self._fork_name = "main"
        self._fork_index = None
        self._client: ClaudeSDKClient | None = None

    @classmethod
    def _make_fork(cls, parent: 'ClaudeCode', name: str | None = None) -> 'ClaudeCode':
        """Create a fork subsession sharing parent's state.
        Must be called from a different contextvars context than the parent."""
        from .model import _session_var
        try:
            current = _session_var.get()
        except LookupError:
            current = None
        if current is not None:
            raise InternalError(
                "_make_fork must be called in a fresh context "
                "(use loop.create_task with context=contextvars.copy_context())")
        fork = object.__new__(cls)
        parent._fork_counter += 1  # type: ignore[attr-defined]
        Session.__init__(fork, parent=parent)
        if name is not None:
            fork._fork_name = f"{parent._fork_name}.{name}"  # type: ignore[attr-defined]
        else:
            fork._fork_name = f"{parent._fork_name}.fork_{parent._fork_counter}"  # type: ignore[attr-defined]
        fork.root = parent.root
        fork.working_dir = parent.working_dir  # type: ignore[attr-defined]
        fork.YAML_path = parent.YAML_path  # type: ignore[attr-defined]
        fork.mcp = parent.mcp  # type: ignore[attr-defined]
        fork._session_id = None
        fork._fork_counter = 0
        fork._fork_index = None
        return fork

    def initialize(self, root: Root):
        super().initialize(root)
        with open(self.YAML_path, "w", encoding="utf-8") as f:
            root.print(0, MyIO(f), update_line=True)
        # Build MCP tools — semantic query tools need the Isabelle connection
        connection = root.ml_state.connection
        tools = [
            _edit_tool, _delete_tool, _answer_tool, _semantic_search_tool,
            mk_query_by_name_tool(connection, []),
            mk_query_by_position_tool(connection, []),
        ]
        self.mcp = create_sdk_mcp_server("proof", tools=tools)
        self.options = ClaudeAgentOptions(
            model="claude-opus-4-6",
            thinking={"type": "adaptive"},
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
        asyncio.run(self._run_with_retry())

    async def interrupt(self):
        if self._client is not None:
            await self._client.interrupt()

    async def _run_with_retry(self):
        import time
        while True:
            try:
                await self._run()
                return
            except self._ReachLimitError:
                self.warn_AoA_opr("Usage limit reached, waiting 20min to retry")
                time.sleep(1200)
            except self._RateLimitError:
                self.warn_AoA_opr("API rate limit, waiting 2s to retry")
                time.sleep(2)

    def close(self):
        """Clean up the session and remove the temporary directory."""
        super().close()
        # Only the main session owns the working directory; forks share it.
        if self.is_major and hasattr(self, 'working_dir') and os.path.exists(self.working_dir):
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

        # Record session_id for forking
        self._session_id = pre_tool_input.get("session_id") or self._session_id

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
            if self.working_interactions:
                # There's a pending interaction - only allow answer tool
                if tool != "mcp__proof__answer":
                    return {
                        "continue_": False,
                        "hookSpecificOutput": {
                            "hookEventName": "PreToolUse",
                            "permissionDecision": "deny",
                            "permissionDecisionReason": "There is a pending interaction that must be answered first. Use the mcp__proof__answer tool.",
                        },
                    }
            else:
                # No pending interaction - reject answer tool
                if tool == "mcp__proof__answer":
                    return {
                        "continue_": False,
                        "hookSpecificOutput": {
                            "hookEventName": "PreToolUse",
                            "permissionDecision": "deny",
                            "permissionDecisionReason": "No pending interaction. The answer tool can only be used when there is an active interaction.",
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

    class _ReachLimitError(Exception):
        pass
    class _RateLimitError(Exception):
        pass

    def _check_error_text(self, text: str) -> None:
        if text.startswith("You've hit your limit"):
            raise self._ReachLimitError()
        if "Rate limit" in text:
            raise self._RateLimitError()

    async def _run(self):
        if self._client is not None:
            raise InternalError("_run called while already running")
        try:
            async with ClaudeSDKClient(options=self.options) as client:
                self._client = client
                await client.query(P.INITIAL_PROMPT)
                while True:
                    # Stream model outputs and log them in debug mode
                    async for message in client.receive_response():
                        content = getattr(message, "content", None)
                        if isinstance(content, list):
                            for block in content:
                                text = getattr(block, "text", None)
                                if isinstance(text, str) and text:
                                    self._check_error_text(text)
                                    self.log_model_output(text)
                                thinking = getattr(block, "thinking", None)
                                if isinstance(thinking, str) and thinking:
                                    self.log_model_thinking(thinking)
                        if isinstance(message, ResultMessage):
                            self._accumulate_cost(message)
                    unfinished_nodes = set()
                    self.root.unfinished_nodes(unfinished_nodes)
                    if unfinished_nodes:
                        retry_prompt = P.RETRY_PROMPT(unfinished_nodes)
                        self.log_retry(unfinished_nodes, retry_prompt)
                        await client.query(retry_prompt)
                    else:
                        self.log_proof()
                        return
        finally:
            self._client = None

    def _accumulate_cost(self, message: ResultMessage) -> None:
        """Accumulate per-turn cost from a ResultMessage."""
        self.debug_info(f"[COST] usage={message.usage} total_cost_usd={message.total_cost_usd}")
        if message.total_cost_usd:
            self.total_cost_usd += message.total_cost_usd
        if message.usage:
            self.total_input_tokens += message.usage.get("input_tokens", 0)
            self.total_output_tokens += message.usage.get("output_tokens", 0)
            self.total_cache_creation_input_tokens += message.usage.get("cache_creation_input_tokens", 0)
            self.total_cache_read_input_tokens += message.usage.get("cache_read_input_tokens", 0)


    def _launch_forks(self, forking: list[tuple[int, Interaction]],
                      wi: Working_Interactions) -> None:
        """Launch forking interactions as background tasks. Results stored via fork_kont."""
        async def run_one(idx: int, interaction: Interaction) -> None:
            from .model import _session_var
            _session_var.set(None)  # Clear the copied parent session so _make_fork succeeds
            fork = ClaudeCode._make_fork(self) # type: ignore[attr-defined]
            fork._fork_index = idx
            # Fork gets its own single-interaction Working_Interactions.
            # The continuation stores the result back into the parent's wi.
            async def fork_kont(results: list[Any]) -> Any:
                result = results[0]
                wi.results[idx] = result
                wi.result_set[idx] = True
                return result
            fork.working_interactions.append(Working_Interactions(
                interactions=[interaction],
                results=[None],
                result_set=[False],
                kontinuation=fork_kont,
            ))
            fork_options = ClaudeAgentOptions(
                model="claude-opus-4-6",
                thinking={"type": "adaptive"},
                resume=self._session_id,
                fork_session=True,
                cwd=self.working_dir,
                permission_mode="default",
                allowed_tools=self.FORK_WHITELIST,
                mcp_servers={"proof": self.mcp},
                hooks={
                    "PreToolUse": [
                        HookMatcher(matcher="*", hooks=[fork.permission_control]),
                    ]
                },
            )
            buffer = StringIO()
            interaction.prompt(0, MyIO(buffer))
            tag = f"[{fork._fork_name}]"
            async with ClaudeSDKClient(options=fork_options) as fork_client:
                fork._client = fork_client
                fork_prompt = (buffer.getvalue() +
                    "\n\nForget the previous instructions. "
                    "Your only task is to answer the question above "
                    "and you MUST terminate immediately once answered.")
                await fork_client.query(fork_prompt)
                async for message in fork_client.receive_response():
                    content = getattr(message, "content", None)
                    if isinstance(content, list):
                        for block in content:
                            text = getattr(block, "text", None)
                            if isinstance(text, str) and text:
                                self._check_error_text(text)
                                fork.log_model_output(f"{tag} {text}")
                            thinking = getattr(block, "thinking", None)
                            if isinstance(thinking, str) and thinking:
                                fork.log_model_thinking(f"{tag} {thinking}")
                    if isinstance(message, ResultMessage):
                        self._accumulate_cost(message)
                        fork.log_interaction("fork", f"{tag} completed: subtype={message.subtype}")
            fork._client = None
            fork.close()

        loop = asyncio.get_running_loop()
        self.log_interaction("fork", f"launching {len(forking)} forking interactions")
        for idx, inter in forking:
            ctx = contextvars.copy_context()
            task = loop.create_task(run_one(idx, inter), context=ctx)
            wi.result_set[idx] = task

    def refresh_YAML(self):
        with open(self.YAML_path, 'w') as f:
            self.root.print(0, MyIO(f), update_line=True)


