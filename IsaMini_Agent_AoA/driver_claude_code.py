from typing import Any, cast
import json
import asyncio
import contextvars
import os
import shlex
import tempfile
import shutil
from .model import *
from . import prompts as P
from .mcp_http_server import ProofMCPHTTPServer
from claude_agent_sdk import ClaudeAgentOptions, ClaudeSDKClient, HookMatcher, ResultMessage

from claude_agent_sdk.types import (
    HookInput,
    HookContext,
    HookJSONOutput,
    PreToolUseHookInput,
)
from io import StringIO
import Isabelle_Semantic_Embedding
from Isabelle_Semantic_Embedding.semantics import mk_query_by_name_tool, mk_query_by_position_tool

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
    working_dir: str
    _fork_counter: int
    _fork_name: str
    _fork_index: int | None

    def __init__(self, *args, parent: 'ClaudeCode | None' = None,
                 interactive_web_terminal: bool = False, **kwargs):
        super().__init__(*args, parent=parent, **kwargs)
        if parent is not None:
            # Fork mode: share parent's state
            self.working_dir = parent.working_dir
            self.YAML_path = parent.YAML_path
            self.root = parent.root
            self._http_server = parent._http_server
            self._interactive_web_terminal = parent._interactive_web_terminal
            parent._fork_counter += 1
            self._fork_name = f"{parent._fork_name}.fork_{parent._fork_counter}"
        else:
            # Normal mode: create fresh state
            self.working_dir = tempfile.mkdtemp(prefix="agent_AoA_")
            if not os.access(self.working_dir, os.R_OK | os.W_OK):
                raise InternalError(
                    f"The working directory {self.working_dir} is not readable and writable.")
            self.YAML_path = os.path.join(self.working_dir, "proof.yaml")
            self._http_server: ProofMCPHTTPServer | None = None
            self._interactive_web_terminal = interactive_web_terminal
            self._fork_name = "main"

        # Common to both modes
        self._session_id: str | None = None       # constant, set in initialize(), used for HTTP server registration
        self._conversation_id: str | None = None   # mutable, set by Agent SDK hook, used for fork resume
        self._fork_counter = 0
        self._fork_index = None
        self._client: ClaudeSDKClient | None = None
        self._mcp_url: str | None = None
        self._proof_complete: asyncio.Event | None = None

    @classmethod
    def _make_fork(cls, parent: 'ClaudeCode') -> 'ClaudeCode':
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
        return cls(parent=parent)

    async def initialize(self, root: Root):
        await super().initialize(root)
        with open(self.YAML_path, "w", encoding="utf-8") as f:
            root.print(0, MyIO(f), update_line=True)

        # Isabelle semantic query tools (SdkMcpTool instances — schemas/handlers extracted by HTTP server)
        connection = root.ml_state.connection
        extra_sdk_tools = [
            mk_query_by_name_tool(connection, []),
            mk_query_by_position_tool(connection, []),
        ]

        # Register with singleton HTTP MCP server
        self._http_server = await ProofMCPHTTPServer.get_or_create()
        self._session_id = self._http_server.allocate_session_id()
        self._mcp_url = await self._http_server.register_session(
            self._session_id, self, extra_sdk_tools=extra_sdk_tools)

        if not self._interactive_web_terminal:
            # Embedded mode: Agent SDK connects to HTTP server via URL
            self.options = ClaudeAgentOptions(
                model="claude-opus-4-6",
                thinking={"type": "adaptive"},
                cwd=self.working_dir,
                permission_mode="default",
                allowed_tools=self.TOOL_WHITELIST,
                mcp_servers={"proof": {"type": "http", "url": self._mcp_url}},
                hooks={
                    "PreToolUse": [
                        HookMatcher(matcher="*", hooks=[self.permission_control]),
                    ]
                },
            )

    async def run(self):
        await self._run_with_retry()

    async def interrupt(self):
        if self._interactive_web_terminal and self._proof_complete is not None:
            self._proof_complete.set()
        if self._client is not None:
            await self._client.interrupt()

    async def _run_with_retry(self):
        if self._interactive_web_terminal:
            await self._run_standalone()
            return
        while True:
            try:
                await self._run_embedded()
                return
            except self._ReachLimitError:
                self.warn_AoA_opr("Usage limit reached, waiting 20min to retry")
                await asyncio.sleep(1200)
            except self._RateLimitError:
                self.warn_AoA_opr("API rate limit, waiting 2s to retry")
                await asyncio.sleep(2)

    async def close(self):
        """Clean up the session and remove the temporary directory."""
        await super().close()
        # Unregister from HTTP server if registered
        if self._http_server is not None and self._session_id is not None:
            await self._http_server.unregister_session(self._session_id)
            self._session_id = None
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

        # Record conversation_id for forking (Agent SDK assigns this)
        self._conversation_id = pre_tool_input.get("session_id") or self._conversation_id

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

    async def _run_embedded(self):
        """Run using the Claude Agent SDK (embedded mode)."""
        if self._client is not None:
            raise InternalError("_run_embedded called while already running")
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

    async def _run_standalone(self):
        """Run Claude Code CLI in a tmux session (standalone/interactive mode)."""
        assert self._session_id is not None, "_run_standalone called before initialize()"
        import uuid
        # Claude CLI requires a UUID for --session-id
        claude_session_id = str(uuid.uuid4())
        self._conversation_id = claude_session_id
        self._proof_complete = asyncio.Event()
        tmux_session = f"proof_{self._session_id}"

        # Write MCP config file
        assert self._http_server is not None
        config_path = os.path.join(self.working_dir, "mcp_config.json")
        with open(config_path, "w") as f:
            json.dump(self._http_server.mcp_config_json(self._session_id), f)

        # Write launcher script with permission settings mirroring embedded mode:
        # - proof.yaml: Read/Grep only (Write/Edit denied — must use mcp__proof__edit)
        # - .claude/plans/: all operations allowed
        # - Bash: denied
        # - Interaction state: handled by _check_tool_permission in mcp_http_server
        yaml_path_abs = os.path.abspath(self.YAML_path)
        settings = json.dumps({
            "permissions": {
                "allow": [
                    f"Read(//{yaml_path_abs})",
                    f"Grep(//{yaml_path_abs})",
                    "Read(//.claude/plans/**)",
                    "Write(//.claude/plans/**)",
                    "Edit(//.claude/plans/**)",
                    "Grep(//.claude/plans/**)",
                ],
                "deny": [
                    "Bash",
                    "Write",
                    "Edit",
                ]
            }
        })
        allowed = ",".join(self.TOOL_WHITELIST)
        launcher_path = os.path.join(self.working_dir, "launch_claude.sh")
        error_log = os.path.join(self.working_dir, "claude_error.log")
        with open(launcher_path, "w") as f:
            f.write("#!/bin/bash\n")
            f.write(f"cd {shlex.quote(self.working_dir)}\n")
            f.write("unset CLAUDECODE\n")  # prevent nesting protection
            f.write(f"claude --session-id {shlex.quote(claude_session_id)} "
                    f"--mcp-config {shlex.quote(config_path)} "
                    f"--strict-mcp-config "
                    f"--allowed-tools {shlex.quote(allowed)} "
                    f"--settings {shlex.quote(settings)} "
                    f"-- {shlex.quote(P.INITIAL_PROMPT)} "
                    f"2>{shlex.quote(error_log)}\n")
            f.write(f"echo \"EXIT CODE: $?\" >> {shlex.quote(error_log)}\n")
        os.chmod(launcher_path, 0o755)

        # Launch tmux session
        proc = await asyncio.create_subprocess_exec(
            'tmux', 'new-session', '-d', '-s', tmux_session, launcher_path,
            stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)
        await proc.wait()
        self.log_AoA_opr(f"Launched tmux session '{tmux_session}'")

        # Start web terminal server and notify Isabelle with the URL
        from .web_terminal import WebTerminalServer
        web_terminal = await WebTerminalServer.get_or_create()
        web_terminal_url = web_terminal.session_url(tmux_session)
        await self.root.ml_state.connection.writeln(
            f"Interactive proof session started. Open web terminal: {web_terminal_url}")

        # Wait for either proof completion or tmux death
        proof_task = asyncio.create_task(self._proof_complete.wait())
        monitor_task = asyncio.create_task(self._monitor_tmux(tmux_session))

        try:
            done, pending = await asyncio.wait(
                [proof_task, monitor_task],
                return_when=asyncio.FIRST_COMPLETED)
            for t in pending:
                t.cancel()
        finally:
            self._proof_complete = None
            # Replace the tmux pane with a result message (instead of just killing it)
            is_proof_done = self.root.is_proof_finished()
            if is_proof_done:
                msg = r"echo -e '\n\033[32m=== Proof completed successfully ===\033[0m\n' && sleep infinity"
            else:
                msg = r"echo -e '\n\033[31m=== Proof session ended (incomplete) ===\033[0m\n' && sleep infinity"
            respawn = await asyncio.create_subprocess_exec(
                'tmux', 'respawn-pane', '-t', tmux_session, '-k',
                'bash', '-c', msg,
                stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)
            await respawn.wait()

        # Read error log if it exists
        error_log = os.path.join(self.working_dir, "claude_error.log")
        if os.path.exists(error_log):
            with open(error_log) as f:
                error_content = f.read().strip()
            if error_content:
                self.warn_AoA_opr(f"Claude error log:\n{error_content}")

        self.log_proof()

    async def _monitor_tmux(self, session_name: str):
        """Poll tmux session status. Returns when session dies."""
        while True:
            await asyncio.sleep(2)
            proc = await asyncio.create_subprocess_exec(
                'tmux', 'has-session', '-t', session_name,
                stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)
            if (await proc.wait()) != 0:
                self.warn_AoA_opr(f"tmux session '{session_name}' exited")
                return

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
            _session_var.set(None)  # type: ignore  # Clear the copied parent session so _make_fork succeeds
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
            # Register fork session with HTTP server → own endpoint
            assert self._http_server is not None
            fork._session_id = self._http_server.allocate_session_id()
            fork_url = await self._http_server.register_session(fork._session_id, fork)
            fork._mcp_url = fork_url

            fork_options = ClaudeAgentOptions(
                model="claude-opus-4-6",
                thinking={"type": "adaptive"},
                resume=self._conversation_id,
                fork_session=True,
                cwd=self.working_dir,
                permission_mode="default",
                allowed_tools=self.FORK_WHITELIST,
                mcp_servers={"proof": {"type": "http", "url": fork_url}},
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
                    "and you MUST use the mcp__proof__answer tool to submit your answer. "
                    "You MUST terminate immediately once answered.")
                await fork_client.query(fork_prompt)
                while True:
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
                    if not fork.working_interactions:
                        break
                    fork.log_interaction("fork", f"{tag} retrying: interaction not answered")
                    await fork_client.query(
                        "You haven't submitted your answer. "
                        "You MUST call the mcp__proof__answer tool to submit it.")
            fork._client = None
            if self._http_server is not None and fork._session_id is not None:
                await self._http_server.unregister_session(fork._session_id)
            await fork.close()

        loop = asyncio.get_running_loop()
        self.log_interaction("fork", f"launching {len(forking)} forking interactions")
        for idx, inter in forking:
            ctx = contextvars.copy_context()
            task = loop.create_task(run_one(idx, inter), context=ctx)
            wi.result_set[idx] = task

    def refresh_YAML(self):
        with open(self.YAML_path, 'w') as f:
            self.root.print(0, MyIO(f), update_line=True)


@agent_driver("ClaudeCode_Interactive")
def _claude_code_interactive(logger, log_dir):
    return ClaudeCode(logger, log_dir, interactive_web_terminal=True)
