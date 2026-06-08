from typing import Any, Callable, cast
import json
import asyncio
import contextvars
import os
import re
from pathlib import Path
import shlex
import tempfile
import shutil
from .model import *
from .language_model_driver import LMDriver, _TransientError, _QuotaError, PRICING, pricing_for, Usage
from . import prompts as P
from .mcp_http_server import ProofMCPHTTPServer
from claude_agent_sdk import ClaudeAgentOptions, ClaudeSDKClient, HookMatcher, ResultMessage
try:
    from claude_agent_sdk import RateLimitEvent
except ImportError:
    RateLimitEvent = None

from claude_agent_sdk.types import (
    HookInput,
    HookContext,
    HookJSONOutput,
    PreToolUseHookInput,
)
from io import StringIO
import Isabelle_Semantic_Embedding

_COMPACT_HEADROOM = 13_000
_DEFAULT_MODEL = "claude-opus-4-6[1m]"

def _derive_cheaper_model(model: str) -> str:
    m = re.match(r'(claude-)(opus)(-[\d\w.-]+)((?:\[.*\])?)', model)
    if m:
        return f"{m.group(1)}sonnet{m.group(3)}{m.group(4)}"
    return model

def _pricing_key(model: str) -> str:
    return re.sub(r'\[.*\]$', '', model)

def _model_context_window(model: str) -> int:
    m = re.search(r'\[(\d+)([mk])\]', model)
    if m:
        num, unit = int(m.group(1)), m.group(2)
        return num * (1_000_000 if unit == 'm' else 1_000)
    return 200_000

def _auto_compact_window(model: str, threshold_pct: float) -> int:
    ctx = _model_context_window(model)
    return max(100_000, min(1_000_000, int(ctx * threshold_pct) + _COMPACT_HEADROOM))


def _serialize_args(args: Any) -> Any:
    """Best-effort JSON-serializable representation of Minilang operation arguments."""
    try:
        json.dumps(args)
        return args
    except (TypeError, ValueError):
        return str(args)

@agent_driver("ClaudeCode")
class ClaudeCode(LMDriver):
    _NON_PROOF_TOOLS = [
        'Read', 'Grep', 'Write', 'Edit', 'Skill', 'Agent',
        'TaskCreate', 'TaskGet', 'TaskList', 'TaskUpdate',
        'WebFetch', 'WebSearch', 'ExitPlanMode', 'MCPSearch', 'ToolSearch',
    ]
    _TOOL_NAME_MAP: dict[str, str] = {
        "query":  "mcp__proof__query",
        "edit":   "mcp__proof__edit",
        "delete": "mcp__proof__delete",
        "recall": "Read",
        "recall_removed": "mcp__proof__recall_removed",
        "request_lemmas": "mcp__proof__request_lemmas",
        "report": "mcp__proof__report",
        "subagent": "mcp__proof__subagent",
        "cancel_subagent": "mcp__proof__cancel_subagent",
        "answer_indexes": "mcp__proof__answer_indexes",
        "answer_index": "mcp__proof__answer_index",
        "answer_indexes_or_name": "mcp__proof__answer_indexes_or_name",
        "answer_indexes_or_spec": "mcp__proof__answer_indexes_or_spec",
        "answer_instantiate": "mcp__proof__answer_instantiate",
        "answer_refutation": "mcp__proof__answer_refutation",
        "answer_struggle_assessment": "mcp__proof__answer_struggle_assessment",
        "refresh": "mcp__proof__refresh",
    }
    TOOL_WHITELIST = _NON_PROOF_TOOLS + list(_TOOL_NAME_MAP.values())
    # subagent/cancel_subagent are dispatch tools (the main agent AND workers); only
    # interaction forks lack them. Precompute that non-dispatcher allow-list
    # (TOOL_WHITELIST minus those two) once at class-definition time. (Statements,
    # not a comprehension, so the class-body name _TOOL_NAME_MAP stays in scope.)
    _WORKER_TOOL_WHITELIST = list(TOOL_WHITELIST)
    _WORKER_TOOL_WHITELIST.remove(_TOOL_NAME_MAP["subagent"])
    _WORKER_TOOL_WHITELIST.remove(_TOOL_NAME_MAP["cancel_subagent"])
    COMPACT_THRESHOLD = 0.85
    FORK_COMPACT_THRESHOLD = 0.99

    def _role_allowed_tools(self) -> list[str]:
        """SDK tool allow-list for this session's role. `subagent`/`cancel_subagent`
        are dispatch tools, allowed for the main agent AND workers (nested
        delegation) but hidden from interaction forks and from a session already at
        the maximum nesting depth (a sub-sub-agent cannot delegate further). Gated by
        `_can_offer_dispatch_tools`, mirroring the MCP tool list (`_tool_schemas_for`)."""
        return (self.TOOL_WHITELIST if self._can_offer_dispatch_tools()
                else self._WORKER_TOOL_WHITELIST)

    def tool_name(self, t: str) -> str:
        return self._TOOL_NAME_MAP.get(t, t)

    def __str__(self) -> str:
        if self._model == _DEFAULT_MODEL:
            return self._driver_name
        return f"{self._driver_name}({self._model})"

    working_dir: str
    _fork_counter: int
    _fork_name: str
    _fork_index: int | None

    def __init__(self, *args, parent: 'ClaudeCode | None' = None,
                 interactive_web_terminal: bool = False,
                 argument: str | None = None, **kwargs):
        super().__init__(*args, parent=parent, **kwargs)
        if parent is not None:
            self._model = parent._model
        else:
            self._model = argument or _DEFAULT_MODEL
        if parent is None:
            self.quickview_line_numbers = True
        if parent is not None:
            # Fork mode: share parent's state
            self.working_dir = parent.working_dir
            self.YAML_path = parent.YAML_path
            self.root = parent.root
            self._http_server = parent._http_server
            self._interactive_web_terminal = False
            self._on_yaml_refresh = parent._on_yaml_refresh
            self._on_operation_status = parent._on_operation_status
            self._on_log_callback = parent._on_log_callback
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
        self._model_time_start: float | None = None
        self._session_id: str | None = None       # constant, set in initialize(), used for HTTP server registration
        self._conversation_id: str | None = None   # mutable, set by Agent SDK hook, used for fork resume
        self._fork_counter = 0
        self._fork_index = None
        self._client: ClaudeSDKClient | None = None
        self._mcp_url: str | None = None
        self._proof_complete: asyncio.Event | None = None
        if parent is None:
            self._on_yaml_refresh: Callable[[str], Any] | None = None
            self._on_operation_status: Callable[[dict], Any] | None = None
            self._on_log_callback: Callable[[dict], Any] | None = None

    @classmethod
    def _make_fork(cls, parent: 'ClaudeCode', role=None) -> 'ClaudeCode':
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
        return cls(parent=parent, role=role)

    _SKILLS = ["isabelle-fun-definition"]

    def _install_skills(self):
        """Copy skill files from assets/ into the working directory's
        .claude/skills/ so Claude Code can discover them."""
        assets = os.path.join(os.path.dirname(__file__), "assets")
        for skill_name in self._SKILLS:
            src = os.path.join(assets, f"{skill_name}.md")
            dst_dir = os.path.join(self.working_dir, ".claude", "skills", skill_name)
            os.makedirs(dst_dir, exist_ok=True)
            shutil.copy2(src, os.path.join(dst_dir, "SKILL.md"))

    async def initialize(self, root: Root):
        await super().initialize(root)
        if self.is_major:
            self._install_skills()

        # Register with singleton HTTP MCP server
        if self._http_server is None:
            self._http_server = await ProofMCPHTTPServer.get_or_create()
        self._session_id = self._http_server.allocate_session_id()
        self._mcp_url = await self._http_server.register_session(
            self._session_id, self)

        # Seed proof.yaml. `refresh_YAML` -> `print_proof_scope`, which renders
        # the full `root` for a major (non-worker) and the scoped view for a
        # worker — so a single call covers both. Interaction forks are neither
        # and intentionally write no YAML. (`_on_yaml_refresh` is still None here
        # — it is set later in `_run_standalone` — so no UI push fires at init.)
        if self.is_major or self.is_worker:
            self.refresh_YAML()

        if not self._interactive_web_terminal:
            # Embedded mode: Agent SDK connects to HTTP server via URL
            main_model = self._model
            self.options = ClaudeAgentOptions(
                model=main_model,
                thinking={"type": "adaptive"},
                system_prompt=self.system_prompt(),
                cwd=self.working_dir,
                permission_mode="default",
                allowed_tools=self._role_allowed_tools(),
                mcp_servers={"proof": {"type": "http", "url": self._mcp_url}},
                env={"CLAUDE_CODE_ATTRIBUTION_HEADER": "0"},
                settings=json.dumps({"autoCompactWindow":
                    _auto_compact_window(main_model, self.COMPACT_THRESHOLD)}),
                extra_args={"exclude-dynamic-system-prompt-sections": None},
                hooks={
                    "PreToolUse": [
                        HookMatcher(matcher="*", hooks=[self.permission_control]),
                    ],
                    "PostToolUse": [
                        HookMatcher(matcher="*", hooks=[self._resume_model_timer]),
                    ],
                    "PostToolUseFailure": [
                        HookMatcher(matcher="*", hooks=[self._resume_model_timer]),
                    ],
                    "PreCompact": [
                        HookMatcher(matcher="*", hooks=[self.on_compact]),
                    ],
                },
            )

    async def interrupt(self):
        if self._interactive_web_terminal and self._proof_complete is not None:
            if self._on_operation_status is not None:
                self._on_operation_status({"type": "proof_complete", "success": True})
            self._proof_complete.set()
        if self._client is not None:
            await self._client.interrupt()

    async def _run_agent_loop(self):
        if self._interactive_web_terminal:
            await self._run_standalone()
            return
        await self._with_retry(self._sdk_loop)

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
                reason += P.edit_tool_use_mcp_for_proof_yaml()
            else:
                reason += P.edit_tool_only_proof_yaml()
        elif tool == "AskUserQuestion":
            reason += P.ASK_USER_QUESTION_REJECTION
        elif tool == "Bash":
            reason += P.BASH_REJECTION

        return reason

    async def on_compact(
        self,
        hook_input: HookInput,
        tool_use_id: str | None,
        context: HookContext,
    ) -> HookJSONOutput:
        """Clear view caches before context compaction so the agent re-discovers entities."""
        self._reset_view_state()
        self._log_meta("COMPACTION")
        return {}

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
        if tool not in self._role_allowed_tools():
            return {
                "continue_": False,
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "deny",
                    "permissionDecisionReason": self._get_tool_not_allowed_reason(tool, tool_input),
                },
            }

        # 2. Check proof MCP tool interaction state.
        # Only forks assigned to answer an interaction may call answer tools.
        is_answer_tool = any(tool == self.tool_name(t) for t in ANSWER_TOOLS)
        if is_answer_tool and (
                self.fork_pending is None or self.fork_pending.answer.done()):
            return {
                "continue_": False,
                "hookSpecificOutput": {
                    "hookEventName": "PreToolUse",
                    "permissionDecision": "deny",
                    "permissionDecisionReason": f"No question pending. The `{tool}` tool can only be used when there is a question for you to answer.",
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
                                "permissionDecisionReason": f"Cannot use `{tool}` on proof.yaml. Use the `{self.tool_name(TOOL_EDIT)}` tool instead.",
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
        if self._model_time_start is not None:
            self.total_model_time += time() - self._model_time_start
            self._model_time_start = None
        self.total_tool_calls += 1
        if not self.is_proof_tool(tool) or tool == self.tool_name(TOOL_READ):
            self.log_tool_call(tool, tool_input)
        return {}

    async def _resume_model_timer(
        self,
        hook_input: HookInput,
        tool_use_id: str | None,
        context: HookContext,
    ) -> HookJSONOutput:
        self._model_time_start = time()
        return {}

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

    def _check_error_text(self, text: str) -> None:
        if text.startswith("You've hit your limit"):
            raise _QuotaError(text)
        if "Rate limit" in text or "Request rejected (429)" in text:
            raise _TransientError(text)

    def _check_rate_limit_event(self, event) -> None:
        if event.rate_limit_info.status == "rejected":
            raise _QuotaError("Rate limit rejected")

    def _check_result_error(self, message: 'ResultMessage') -> None:
        if message.is_error and message.result:
            self._check_error_text(message.result)

    async def _sdk_loop(self):
        """Run using the Claude Agent SDK (embedded mode)."""
        if self._client is not None:
            raise InternalError("_sdk_loop called while already running")
        self._budget_start_time = time()
        while True:
            try:
                async with ClaudeSDKClient(options=self.options) as client:
                    self._client = client
                    self.refresh_YAML()
                    prompt = await self.initial_prompt()
                    if self._refresh_summary is not None:
                        prompt += "\n\nAgent's briefing:\n" + self._refresh_summary
                        self._refresh_summary = None
                    await client.query(prompt)
                    self._model_time_start = time()
                    while True:
                        async for message in client.receive_response():
                            if RateLimitEvent is not None and isinstance(message, RateLimitEvent):
                                self._check_rate_limit_event(message)
                                continue
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
                                if self._model_time_start is not None:
                                    self.total_model_time += time() - self._model_time_start
                                    self._model_time_start = None
                                self._accumulate_cost(message)
                                self._check_result_error(message)
                        if self.check_budget():
                            break
                        unfinished_nodes = self.proof_scope_unfinished_nodes()
                        if unfinished_nodes and self.quit_info is None:
                            self._retry_count += 1
                            if self.check_budget():
                                break
                            retry_prompt = self.retry_prompt(unfinished_nodes)
                            self.log_retry(unfinished_nodes, retry_prompt)
                            await client.query(retry_prompt)
                            self._model_time_start = time()
                        else:
                            break
            finally:
                self._client = None

            if not isinstance(self.quit_info, (Restart, Refresh)):
                break

            if isinstance(self.quit_info, Refresh):
                self._refresh_summary = self.quit_info.briefing
                self.quit_info = None
                self._reset_view_state()
                self.runtime.age += 1
                self._total_calls_at_last_refresh = self.total_tool_calls
                self.log_AoA_opr("Context refreshed")
                self._log_meta("REFRESH", briefing=self._refresh_summary)
                continue

            self.quit_info = None
            self.log_AoA_opr("Context restarted")
            self._log_meta("CONTEXT_RESTART")

        self.log_proof()

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
        # - proof.yaml: Read/Grep only (Write/Edit denied — must use proof edit tool)
        # - .claude/plans/: all operations allowed
        # - Bash: denied
        # - Interaction state: handled by _check_tool_permission in mcp_http_server
        yaml_path_abs = os.path.abspath(self.YAML_path)
        reset_url = f"http://127.0.0.1:{self._http_server.port}/reset_cache/{self._session_id}"
        settings = json.dumps({
            "autoCompactWindow": _auto_compact_window(self._model, self.COMPACT_THRESHOLD),
            "permissions": {
                "allow": [
                    f"Read(//{yaml_path_abs})",
                    f"Grep(//{yaml_path_abs})",
                    "Read(//.claude/plans/**)",
                    "Write(//.claude/plans/**)",
                    "Edit(//.claude/plans/**)",
                    "Grep(//.claude/plans/**)",
                    "Read(//.claude/skills/**)",
                ],
                "deny": [
                    "Bash",
                    "Write",
                    "Edit",
                ]
            },
            "hooks": {
                "PreCompact": [{
                    "matcher": "",
                    "hooks": [{
                        "type": "command",
                        "command": f"curl -s {reset_url}",
                    }],
                }],
            },
        })
        allowed = ",".join(self._role_allowed_tools())
        launcher_path = os.path.join(self.working_dir, "launch_claude.sh")
        error_log = os.path.join(self.working_dir, "claude_error.log")
        initial_prompt = await self.initial_prompt()
        with open(launcher_path, "w") as f:
            f.write("#!/bin/bash\n")
            f.write(f"cd {shlex.quote(self.working_dir)}\n")
            f.write("unset CLAUDECODE\n")  # prevent nesting protection
            f.write(f"claude --session-id {shlex.quote(claude_session_id)} "
                    f"--model {shlex.quote(self._model)} "
                    f"--mcp-config {shlex.quote(config_path)} "
                    f"--strict-mcp-config "
                    f"--allowed-tools {shlex.quote(allowed)} "
                    f"--settings {shlex.quote(settings)} "
                    f"-- {shlex.quote(initial_prompt)} "
                    f"2>{shlex.quote(error_log)}\n")
            f.write(f"echo \"EXIT CODE: $?\" >> {shlex.quote(error_log)}\n")
        os.chmod(launcher_path, 0o755)

        # Kill any stale tmux session with the same name (from a previous run)
        await (await asyncio.create_subprocess_exec(
            'tmux', 'kill-session', '-t', tmux_session,
            stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)).wait()

        # Launch tmux session
        proc = await asyncio.create_subprocess_exec(
            'tmux', 'new-session', '-d', '-x', '300', '-y', '80',
            '-s', tmux_session, launcher_path,
            stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)
        await proc.wait()
        self.log_AoA_opr(f"Launched tmux session '{tmux_session}'")

        # Start web terminal server, register YAML path, and set up push notifications
        from .web_terminal import WebTerminalServer
        web_terminal = await WebTerminalServer.get_or_create()
        web_terminal.register_yaml(tmux_session, self.YAML_path)
        self._on_yaml_refresh = lambda qv: asyncio.create_task(
            web_terminal.notify_yaml_update(tmux_session, qv))
        self._on_operation_status = lambda msg: asyncio.create_task(
            web_terminal.notify_status(tmux_session, msg))
        self._on_log_callback = lambda msg: asyncio.create_task(
            web_terminal.notify_status(tmux_session, msg))
        # Push initial YAML + quickview so the web page shows content before any operation
        self.refresh_YAML()
        web_terminal_url = web_terminal.session_url(tmux_session)
        await self.root.ml_state.connection.writeln(
            f"Interactive proof session started. Open web terminal: {web_terminal_url}")

        # Wait for either proof completion, tmux death, or budget timeout
        self._budget_start_time = time()
        proof_task = asyncio.create_task(self._proof_complete.wait())
        monitor_task = asyncio.create_task(self._monitor_tmux(tmux_session))

        try:
            done, pending = await asyncio.wait(
                [proof_task, monitor_task],
                return_when=asyncio.FIRST_COMPLETED,
                timeout=self.timeout_seconds)
            for t in pending:
                t.cancel()
            if not done:
                self.quit_info = ResourceExhausted(
                    f"timeout ({self.timeout_seconds}s)")
                self.log_budget_exhausted(f"timeout ({self.timeout_seconds}s)")
        finally:
            self._proof_complete = None
            self._on_yaml_refresh = None
            self._on_operation_status = None
            self._on_log_callback = None
            web_terminal.unregister_yaml(tmux_session)
            # Send proof_complete if not already sent (e.g., tmux died)
            if not self.root.is_proof_finished():
                await web_terminal.notify_status(tmux_session,
                    {"type": "proof_complete", "success": False})
            # Kill tmux session
            await (await asyncio.create_subprocess_exec(
                'tmux', 'kill-session', '-t', tmux_session,
                stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.DEVNULL)).wait()

        # Read error log if it exists
        error_log = os.path.join(self.working_dir, "claude_error.log")
        if os.path.exists(error_log):
            with open(error_log) as f:
                error_content = f.read().strip()
            if error_content:
                self.warn_AoA_opr(f"Claude error log:\n{error_content}")

        self._read_cost_from_session_log()
        self.log_proof()

    def _pricing(self) -> dict[str, float]:
        # `_pricing_key` strips a context-window suffix (e.g. `[1m]`); unknown
        # Claude versions fall back to the opus default. See docs/COST_ACCOUNTING.md.
        return pricing_for(_pricing_key(self._model), PRICING["claude-opus-4-6"])

    def _read_cost_from_session_log(self) -> None:
        """Read token usage from Claude Code JSONL session logs (standalone mode).

        Reads ALL .jsonl files in the project directory to capture costs from
        both the main CLI session and any fork sub-sessions (which the Agent SDK
        writes to separate .jsonl files in the same project directory).

        Claude Code writes multiple assistant records per API call (one per
        streamed content block), each carrying the same ``usage`` of that call.
        We deduplicate by ``requestId`` so each API call is counted once, keeping
        the last record (which has the final ``output_tokens``).
        """
        if self._conversation_id is None:
            return
        project_name = re.sub(r'[^a-zA-Z0-9]', '-', self.working_dir)
        project_dir = Path.home() / ".claude" / "projects" / project_name
        if not project_dir.exists():
            self.log_cost(f"Project directory not found: {project_dir}")
            return
        jsonl_files = list(project_dir.glob("*.jsonl"))
        if not jsonl_files:
            self.log_cost(f"No session logs found in: {project_dir}")
            return

        # Deduplicate by requestId alone — fork_session=True copies parent
        # history into the fork JSONL, so the same requestId appears in multiple
        # files.  Keep the last record per requestId (final output_tokens).
        usage_by_request: dict[str, dict] = {}
        for session_log in jsonl_files:
            try:
                with open(session_log) as f:
                    for line in f:
                        line = line.strip()
                        if not line:
                            continue
                        record = json.loads(line)
                        if record.get("type") != "assistant":
                            continue
                        rid = record.get("requestId")
                        usage = (record.get("message") or {}).get("usage")
                        if rid and usage:
                            usage_by_request[rid] = usage
            except Exception as e:
                self.log_cost(f"Failed to read session log {session_log.name}: {e}")

        self.total_input_tokens = 0
        self.total_output_tokens = 0
        self.total_cache_creation_input_tokens = 0
        self.total_cache_read_input_tokens = 0

        # Anthropic-native usage: input_tokens already excludes cache → from_uncached.
        for usage in usage_by_request.values():
            self._accumulate_usage(Usage.from_uncached(
                input_tokens=usage.get("input_tokens", 0),
                output_tokens=usage.get("output_tokens", 0),
                cache_read=usage.get("cache_read_input_tokens", 0),
                cache_creation=usage.get("cache_creation_input_tokens", 0)))

        self._compute_cost()

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
        """Per-turn accounting from a ResultMessage. Cost is the REMOTE-reported
        ``total_cost_usd`` (authoritative); tokens go through the shared
        ``_accumulate_usage`` (Anthropic-native input already excludes cache)."""
        self.log_cost(f"usage={message.usage} total_cost_usd={message.total_cost_usd}")
        if message.total_cost_usd:
            self.total_cost_usd += message.total_cost_usd
        if message.usage:
            self._accumulate_usage(Usage.from_uncached(
                input_tokens=message.usage.get("input_tokens", 0),
                output_tokens=message.usage.get("output_tokens", 0),
                cache_read=message.usage.get("cache_read_input_tokens", 0),
                cache_creation=message.usage.get("cache_creation_input_tokens", 0)))

    async def _do_fork(self, interaction: Interaction,
                       prompt_text: str) -> Any:
        """Spawn a sub-agent to answer ``interaction`` and return its result.

        Runs a forked ``ClaudeCode`` session whose ``answer`` tool resolves
        the interaction. All fork body work runs in a fresh ``contextvars``
        context so the per-call ``_session_var`` does not leak into the caller.
        """
        loop = asyncio.get_running_loop()
        ctx = contextvars.copy_context()
        task = loop.create_task(self._run_fork(interaction, prompt_text), context=ctx)
        return await task

    async def _run_fork(self, interaction: Interaction, prompt_text: str) -> Any:
        """Body of a forked interaction, run in its own contextvars context."""
        from .model import _session_var, Fork_Pending, Role_Interaction
        _session_var.set(None)  # type: ignore  # Clear the copied parent session so _make_fork succeeds
        mode = interaction.forking
        fork = ClaudeCode._make_fork(self, role=Role_Interaction(  # type: ignore[attr-defined]
            pending=Fork_Pending(interaction, asyncio.get_running_loop().create_future()),
            prompt=prompt_text,
            resume_id=self._conversation_id if mode == ForkingMode.FORKING_WITH_CTXT else None,
            mode=mode,
        ))

        await fork.initialize(self.root)
        assert fork._mcp_url is not None
        fork_url = fork._mcp_url

        mode = interaction.forking
        if mode == ForkingMode.FORKING_CHEAPER_NO_CTXT:
            model = _derive_cheaper_model(self._model)
        else:
            model = self._model
        if mode == ForkingMode.FORKING_WITH_CTXT:
            resume = self._conversation_id
            fork_session = True
        else:
            resume = None
            fork_session = False

        fork_options = ClaudeAgentOptions(
            model=model,
            thinking={"type": "adaptive"},
            system_prompt=self.system_prompt(),
            resume=resume,
            fork_session=fork_session,
            cwd=self.working_dir,
            permission_mode="default",
            allowed_tools=self._role_allowed_tools(),
            mcp_servers={"proof": {"type": "http", "url": fork_url}},
            env={"CLAUDE_CODE_ATTRIBUTION_HEADER": "0"},
            settings=json.dumps({"autoCompactWindow":
                _auto_compact_window(model, self.FORK_COMPACT_THRESHOLD)}),
            extra_args={"exclude-dynamic-system-prompt-sections": None},
            hooks={
                "PreToolUse": [
                    HookMatcher(matcher="*", hooks=[fork.permission_control]),
                ],
                "PostToolUse": [
                    HookMatcher(matcher="*", hooks=[fork._resume_model_timer]),
                ],
                "PostToolUseFailure": [
                    HookMatcher(matcher="*", hooks=[fork._resume_model_timer]),
                ],
                "PreCompact": [
                    HookMatcher(matcher="*", hooks=[fork.on_compact]),
                ],
            },
        )
        tag = f"[{fork._fork_name}]"
        try:
          while True:
            try:
              async with ClaudeSDKClient(options=fork_options) as fork_client:
                fork._client = fork_client
                # Wording avoids "Forget the previous instructions" / "MUST" /
                # "only task" — under FORKING_WITH_CTXT the fork resumes the
                # parent conversation, and those phrases trip Claude's anti-
                # injection training, leading the fork to ignore the prompt.
                fork_prompt = prompt_text
                answer_tool = self.tool_name(interaction.answer_tool_name)
                if answer_tool not in prompt_text:
                    fork_prompt += (
                        f"\nAnswer the question above by calling the "
                        f"`{answer_tool}` tool.")
                fork.log_interaction("fork", f"{tag} prompt:\n{prompt_text}")
                await fork_client.query(fork_prompt)
                fork._model_time_start = time()
                while True:
                    async for message in fork_client.receive_response():
                        if RateLimitEvent is not None and isinstance(message, RateLimitEvent):
                            self._check_rate_limit_event(message)
                            continue
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
                            if fork._model_time_start is not None:
                                fork.total_model_time += time() - fork._model_time_start
                                fork._model_time_start = None
                            self._accumulate_cost(message)
                            self._check_result_error(message)
                            fork.log_interaction("fork", f"{tag} completed: subtype={message.subtype}")
                    assert fork.fork_pending is not None
                    if fork.fork_pending.answer.done():
                        break
                    fork.log_interaction("fork", f"{tag} retrying: interaction not answered")
                    await fork_client.query(
                        "It looks like you haven't submitted your answer. "
                        f"Call `{self.tool_name(fork.fork_pending.interaction.answer_tool_name)}` to submit it.")
                    fork._model_time_start = time()
              fork._client = None
              break
            except _QuotaError:
                self.warn_AoA_opr(f"{tag} Quota exhausted, waiting 20min to retry")
                t0 = time()
                await asyncio.sleep(1200)
                self.total_quota_wait_time += time() - t0
            except _TransientError as e:
                self.warn_AoA_opr(f"{tag} Transient API error, retrying in 2s: {e}")
                await asyncio.sleep(2)
        finally:
            if self._http_server is not None and fork._session_id is not None:
                await self._http_server.unregister_session(fork._session_id)
            self.total_isabelle_time += fork.total_isabelle_time
            self.total_model_time += fork.total_model_time
            self.total_quota_wait_time += fork.total_quota_wait_time
            await fork.close()
        assert fork.fork_pending is not None and fork.fork_pending.answer.done()
        return fork.fork_pending.answer.result()

    def refresh_YAML(self):
        with open(self.YAML_path, 'w', encoding="utf-8") as f:
            self.print_proof_scope(0, MyIO(f), update_line=True, show_warnings=True)
        if self._on_yaml_refresh is not None:
            buf = StringIO()
            self.quickview_proof_scope(0, MyIO(buf))
            self._on_yaml_refresh(buf.getvalue())

    _SKIP_STATUS_OPS = frozenset({"SKIP", "SORRY", "NEXT", "END"})

    _SKIP_RETRIEVAL = frozenset({"none selected", "unfound"})

    def log_retrieval(self, query: str, results: list[str], *, quiet: bool = False):
        super().log_retrieval(query, results, quiet=quiet)
        if self._on_operation_status is not None:
            if results and not any(r in self._SKIP_RETRIEVAL for r in results):
                self._on_operation_status({
                    "type": "retrieval", "query": query, "results": results})

    def on_log(self, event_type: str, data: dict[str, Any]):
        if self._on_log_callback is not None:
            self._on_log_callback({
                "type": "log", "event": event_type, **data})

    def on_operation_start(self, step_id: str, operation: str, args: Any):
        if self._on_operation_status is not None and operation not in self._SKIP_STATUS_OPS:
            self._on_operation_status({
                "type": "status", "step": step_id,
                "operation": operation, "args": _serialize_args(args),
                "state": "running"})

    def on_operation_end(self, step_id: str, operation: str, args: Any, status: EvaluationStatus):
        super().on_operation_end(step_id, operation, args, status)
        if self._on_operation_status is not None and operation not in self._SKIP_STATUS_OPS:
            msg: dict[str, Any] = {
                "type": "status", "step": step_id,
                "operation": operation, "args": _serialize_args(args),
                "state": "done",
                "time": status.time,
                "success": status.status == EvaluationStatus.Status.SUCCESS}
            if status.reason is not None:
                msg["error"] = str(status.reason)
            self._on_operation_status(msg)


@agent_driver("ClaudeCode_Interactive")
def _claude_code_interactive(logger, log_dir, *, argument=None, **kwargs):
    return ClaudeCode(logger, log_dir, interactive_web_terminal=True,
                      argument=argument, **kwargs)
