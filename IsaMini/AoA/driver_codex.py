from typing import Any
import asyncio
import contextlib
import contextvars
import glob
import json
import os
import shutil
import shlex
import signal
import sys
import tempfile
from time import time

import platformdirs

from .model import *
from .language_model_driver import LMDriver, _TransientError, _QuotaError, PRICING, pricing_for, _parse_effort_suffix, Usage

from .mcp_http_server import ProofMCPHTTPServer, _cc_edit_schema_flat


# PreToolUse guard hook source (ALLOWLIST). With the OS sandbox disabled
# (`-s danger-full-access`), this hook is the SOLE capability barrier, so it is a
# default-DENY allowlist rather than a denylist: it permits ONLY (a) our proof MCP
# tools — codex flattens them to `mcp__proof__<tool>`, matched by prefix — and
# (b) a small fixed set of benign native tools with no host/file access; EVERY
# other tool is denied. This blocks `apply_patch` (file write), `view_image`
# (file read), and crucially ANY unknown or future native tool — including a
# hypothetical file-read tool — without having to name it (a denylist could not).
# The hook reads the PreToolUse event JSON on stdin and either stays silent (exit
# 0 = allow) or prints the schema-exact deny envelope. It receives the flattened
# name for MCP tools and the bare name for native tools (verified, codex 0.141.0).
# `__ALLOW_PREFIX__` is substituted with the real MCP prefix at write time so it
# can never drift from the configured server name.
_GUARD_HOOK_SOURCE = '''\
import json, sys
ALLOW_PREFIX = "__ALLOW_PREFIX__"
ALLOW_EXACT = {"update_plan", "request_user_input", "list_mcp_resources", "multi_tool_use.parallel"}
try:
    ev = json.loads(sys.stdin.read() or "{}")
except Exception:
    sys.exit(0)
tool = ev.get("tool_name") or ""
if tool.startswith(ALLOW_PREFIX) or tool in ALLOW_EXACT:
    sys.exit(0)
print(json.dumps({"hookSpecificOutput": {
    "hookEventName": "PreToolUse",
    "permissionDecision": "deny",
    "permissionDecisionReason": str(tool) + " is disabled in this session.",
}}))
'''


# Codex exposes every tool from an external MCP server to the model under a single
# flattened name `mcp__<server>__<tool>` (double-underscore delimiter; the `mcp__`
# prefix is present unless `non_prefixed_mcp_tool_names` is set, which we never do).
# All AoA proof tools are served by one MCP server registered under this name, so
# the agent-facing name of abstract tool id `t` is `mcp__proof__<t>`. Verified
# against codex 0.141.0: the model tool-spec `name`, the PreToolUse hook
# `tool_name`, and approval matchers all use this flattened form; the ONLY place
# codex reports a bare name is the `exec --json` event, which splits it into
# separate `server`/`tool` fields (reassembled in `_run_codex_exec`).
_MCP_SERVER_NAME = "proof"
_MCP_TOOL_PREFIX = f"mcp__{_MCP_SERVER_NAME}__"


@agent_driver("Codex")
class Codex_Driver(LMDriver):
    # The full ``model-effort`` string (the codebase convention, e.g. parsed by
    # `_parse_effort_suffix`). The effort suffix is split off and passed to Codex
    # via `-c model_reasoning_effort=<effort>`; the bare model goes to `-m` and
    # drives pricing (so it must be a key in `PRICING`).
    DEFAULT_MODEL = "gpt-5.5-high"
    DEFAULT_EFFORT = "high"
    # Max attempts for an interaction fork to call its answer tool before giving up.
    _FORK_ANSWER_MAX_ATTEMPTS = 4

    # Agent-facing tool-name table. Every AoA proof tool is served by the `proof`
    # MCP server, which codex flattens to `mcp__proof__<id>` (see _MCP_TOOL_PREFIX).
    # Built from ALL_PROOF_TOOLS so it can never drift from the tool set. Note there
    # is NO `recall`->`Read` special case (unlike ClaudeCode): codex has no built-in
    # Read — the native shell is disabled — so `recall` is the MCP tool
    # `mcp__proof__recall`.
    _TOOL_NAME_MAP = {t: _MCP_TOOL_PREFIX + t for t in ALL_PROOF_TOOLS}


    working_dir: str
    _fork_counter: int
    _fork_name: str

    def __init__(self, *args, parent: 'Codex_Driver | None' = None,
                 model: str | None = None, argument: str | None = None, **kwargs):
        super().__init__(*args, parent=parent, **kwargs)
        if parent is not None and model is None:
            # Forks inherit the parent's already-parsed model + effort.
            self._model = parent._model
            self._reasoning_effort = parent._reasoning_effort
        else:
            self._model, self._reasoning_effort = _parse_effort_suffix(
                model or argument or self.DEFAULT_MODEL,
                self.DEFAULT_MODEL, default_effort=self.DEFAULT_EFFORT)
        if parent is not None:
            self.working_dir = parent.working_dir
            self.YAML_path = parent.YAML_path
            self.root = parent.root
            self._http_server = parent._http_server
            self._fork_lock = parent._fork_lock
            self._codex_session_id = parent._codex_session_id
            self._codex_session_jsonl = parent._codex_session_jsonl
            self._codex_home_dir = parent._codex_home_dir
            parent._fork_counter += 1
            self._fork_name = f"{parent._fork_name}.fork_{parent._fork_counter}"
        else:
            self.working_dir = tempfile.mkdtemp(prefix="agent_AoA_codex_")
            if not os.access(self.working_dir, os.R_OK | os.W_OK):
                raise InternalError(
                    f"The working directory {self.working_dir} is not readable and writable.")
            self.YAML_path = os.path.join(self.working_dir, "proof.yaml")
            self._http_server: ProofMCPHTTPServer | None = None
            self._fork_lock = asyncio.Lock()
            self._fork_name = "main"
            self._codex_session_id: str | None = None
            self._codex_session_jsonl: str | None = None
            # Per-proof isolated CODEX_HOME (shared by this proof's forks/workers),
            # kept separate from the agent's cwd (working_dir) so the copied
            # credential does not sit in a directory the agent can read.
            self._codex_home_dir = tempfile.mkdtemp(prefix="agent_AoA_codex_home_")
            src_auth = os.path.join(Codex_Driver._codex_home(), "auth.json")
            if not os.path.exists(src_auth):
                raise InternalError(
                    f"Codex credential not found at {src_auth}; run `codex login` first.")
            shutil.copy2(src_auth, os.path.join(self._codex_home_dir, "auth.json"))

        self._model_time_start: float | None = None
        self._session_id: str | None = None
        self._mcp_url: str | None = None
        self._model_instructions_path: str | None = None
        self._fork_counter = 0
        self._exec_process: asyncio.subprocess.Process | None = None

    def __str__(self) -> str:
        label = f"{self._model}-{self._reasoning_effort}"
        if label == self.DEFAULT_MODEL:
            return self._driver_name
        return f"{self._driver_name}({label})"

    def tool_name(self, t: tool) -> str:
        # Translate an abstract tool id to the flattened codex MCP name the model
        # actually sees (e.g. `recall` -> `mcp__proof__recall`). Falls back to the
        # id unchanged for anything outside the proof-tool set.
        return self._TOOL_NAME_MAP.get(t, t)

    def transform_tool_schema(self, name: str, schema: dict) -> dict:
        # codex-cli DROPS `$ref`/`$defs` when forwarding an MCP tool's inputSchema
        # to the model (verified 0.141.0: the `edit` operation union collapses to
        # `{}`, leaving the model no spec — it just flails). Serve the pre-flattened,
        # `$ref`-free `edit` schema — the SAME flat schema the API drivers feed the
        # model. `edit` is the only proof tool that carries `$ref`.
        return _cc_edit_schema_flat if name == TOOL_EDIT else schema

    @classmethod
    def _make_fork(cls, parent: 'LMDriver', role=None) -> 'Codex_Driver':
        from .model import _session_var
        try:
            current = _session_var.get()
        except LookupError:
            current = None
        if current is not None:
            raise InternalError(
                "_make_fork must be called in a fresh context "
                "(use loop.create_task with context=contextvars.copy_context())")
        if not isinstance(parent, Codex_Driver):
            raise InternalError("Codex_Driver._make_fork got non-Codex parent")
        return cls(parent=parent, role=role)

    # ------------------------------------------------------------------
    # Lifecycle
    # ------------------------------------------------------------------

    async def initialize(self, root: Root):
        await super().initialize(root)
        if self._http_server is None:
            self._http_server = await ProofMCPHTTPServer.get_or_create()
        self._session_id = self._http_server.allocate_session_id()
        self._mcp_url = await self._http_server.register_session(
            self._session_id, self)
        if self.is_major:
            self._write_codex_config()
        # Seed proof.yaml. `refresh_YAML` -> `print_proof_scope`, which renders
        # the full `root` for a major (non-worker) and the scoped view for a
        # worker — so a single call covers both. Interaction forks are neither
        # and intentionally write no YAML.
        if self.is_major or self.is_worker:
            self._write_model_instructions()
            self.refresh_YAML()

    def _write_codex_config(self):
        # config.toml must be at the TOP level of CODEX_HOME to be read. Drop the
        # PreToolUse guard-hook script beside it and wire it in: `features.hooks`
        # must be true (hooks are silent otherwise) and the hook is registered as
        # a single `[[hooks.PreToolUse]]` matcher group (no matcher = matches all
        # tools; the script itself applies the allowlist). The real MCP prefix is
        # substituted in so the allowlist tracks the configured server name.
        hook_path = os.path.join(self._codex_home_dir, "guard_hook.py")
        with open(hook_path, "w", encoding="utf-8") as f:
            f.write(_GUARD_HOOK_SOURCE.replace("__ALLOW_PREFIX__", _MCP_TOOL_PREFIX))
        hook_cmd = f"{shlex.quote(sys.executable)} {shlex.quote(hook_path)}"
        with open(os.path.join(self._codex_home_dir, "config.toml"), "w") as f:
            f.write(
                f"[mcp_servers.{_MCP_SERVER_NAME}]\nurl = {json.dumps(self._mcp_url)}\n\n"
                "[features]\nhooks = true\n\n"
                "[[hooks.PreToolUse]]\n"
                "[[hooks.PreToolUse.hooks]]\n"
                'type = "command"\n'
                f"command = {json.dumps(hook_cmd)}\n")

    def _write_model_instructions(self):
        # Replace Codex's built-in base prompt with the role-aware AoA system
        # prompt, passed via `-c model_instructions_file=`. The native shell is
        # disabled (no file reads), so steer the agent to the `recall` tool.
        text = (self.system_prompt() or "") + (
            "\n\nYou cannot read files from disk. Ignore any instruction to read "
            f"or open `proof.yaml`; obtain the current proof state ONLY by calling "
            f"the `{self.tool_name(TOOL_READ)}` tool.\n")
        path = os.path.join(
            self._codex_home_dir, f"model_instructions_{self._session_id}.md")
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        self._model_instructions_path = path

    async def close(self):
        await super().close()
        if self._http_server is not None and self._session_id is not None:
            await self._http_server.unregister_session(self._session_id)
            self._session_id = None
        if self.is_major:
            # Only the major owns these; forks/workers share them. The rollout
            # jsonl lives under _codex_home_dir, so it goes with the rmtree.
            for d in (getattr(self, 'working_dir', None),
                      getattr(self, '_codex_home_dir', None)):
                if d and os.path.exists(d):
                    try:
                        shutil.rmtree(d)
                        self.debug_info(f"[CLEANUP] Removed temporary directory: {d}")
                    except Exception as e:
                        self.debug_info(f"[CLEANUP] Failed to remove temporary directory {d}: {e}")

    def _on_start_run(self):
        self.log_AoA_opr(f"Working directory: {self.working_dir}, Log directory: {self.log_dir}")

    async def interrupt(self):
        proc = self._exec_process
        if proc is not None:
            # Kill the whole process group (set up via start_new_session) so
            # codex AND its child processes are reaped, not just the leader.
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
            except ProcessLookupError:
                pass

    def refresh_YAML(self):
        with open(self.YAML_path, 'w', encoding="utf-8") as f:
            self.print_proof_scope(0, MyIO(f), update_line=True, show_warnings=True)

    # ------------------------------------------------------------------
    # Session JSONL discovery
    # ------------------------------------------------------------------

    @staticmethod
    def _codex_home() -> str:
        env = os.environ.get("CODEX_HOME")
        if env:
            return env
        candidate = os.path.join(os.path.expanduser("~"), ".codex")
        if os.path.isdir(candidate):
            return candidate
        return platformdirs.user_config_dir("codex", appauthor=False)

    def _find_session_jsonl(self, session_id: str) -> str:
        # Search this proof's own CODEX_HOME (set per-invocation via the
        # subprocess env). A thread_id maps to exactly one rollout file on
        # 0.139.0 (verified: no rotation, resume appends); the mtime tiebreak
        # is a defensive guard. `.fork_bak` backups don't match `*.jsonl`.
        matches = glob.glob(
            os.path.join(self._codex_home_dir, "sessions", "**",
                         f"*{session_id}.jsonl"),
            recursive=True)
        if not matches:
            raise InternalError(f"Codex session JSONL not found for {session_id}")
        return max(matches, key=os.path.getmtime)

    async def _run_agent_loop(self):
        await self._with_retry(self._codex_loop)

    async def _codex_loop(self):
        self._budget_start_time = time()
        prompt: str = await self.initial_prompt()
        codex_session_id: str | None = None

        while True:  # outer restart loop
            if self._refresh_summary is not None:
                prompt = ((await self.initial_prompt())
                          + "\n\nAgent's briefing:\n"
                          + self._refresh_summary)
                self._refresh_summary = None
            while True:
                if codex_session_id is None:
                    cmd = self._build_exec_cmd(prompt)
                else:
                    cmd = self._build_resume_cmd(codex_session_id, prompt)

                self._model_time_start = time()
                events = await self._run_codex_exec(cmd)
                if self._model_time_start is not None:
                    self.total_model_time += time() - self._model_time_start
                    self._model_time_start = None

                if codex_session_id is None:
                    codex_session_id = events.get("thread_id")
                    if codex_session_id is not None:
                        self._codex_session_id = codex_session_id
                        self._codex_session_jsonl = self._find_session_jsonl(
                            codex_session_id)

                self._record_codex_usage(events.get("usage", {}))

                if self.check_budget():
                    break
                unfinished = self.proof_scope_unfinished_nodes()
                if unfinished and self.quit_info is None:
                    self._retry_count += 1
                    if self.check_budget():
                        break
                    prompt = self.retry_prompt(unfinished)
                    self.log_retry(unfinished, prompt)
                else:
                    break

            if not isinstance(self.quit_info, (Restart, Refresh)):
                break

            if isinstance(self.quit_info, Refresh):
                self._refresh_summary = self.quit_info.briefing
                self.quit_info = None
                self._reset_view_state()
                self.runtime.age += 1
                self.refresh_YAML()
                codex_session_id = None
                self._total_calls_at_last_refresh = self.total_tool_calls
                self.log_AoA_opr("Context refreshed")
                self._log_meta("REFRESH", briefing=self._refresh_summary)
                continue

            self.quit_info = None
            self.refresh_YAML()
            codex_session_id = None
            prompt = await self.initial_prompt()
            self.log_AoA_opr("Context restarted")
            self._log_meta("CONTEXT_RESTART")

        self._compute_cost()
        self.log_proof()

    def _codex_common_args(self, mcp_url: str | None = None) -> list[str]:
        url = mcp_url or self._mcp_url
        if url is None:
            raise InternalError("Codex MCP URL is not initialized")
        # Capability lockdown, verified end-to-end against codex-cli 0.141.0.
        #
        # The OS sandbox is DISABLED (`-s danger-full-access`); control is done
        # with a PreToolUse HOOK instead (written by `_write_codex_config`). The
        # hook is an ALLOWLIST: it default-DENIES every tool except our proof MCP
        # tools and a few benign natives, so `apply_patch` (file write),
        # `view_image` (file read), and any unknown/future host-or-file tool are
        # all blocked without being named (the hook firing + a deny were verified
        # in `codex exec`: "Command blocked by PreToolUse hook"). The feature-flag
        # `--disable`s below are kept as a second layer (they remove tools from the
        # offered set entirely). `-s danger-full-access` is used rather than
        # `--dangerously-bypass-approvals-and-sandbox` because the bypass flag
        # may also drop hook enforcement, whereas danger-full-access keeps the
        # hook layer active. `--dangerously-bypass-hook-trust` lets the hook run
        # unattended (a fresh CODEX_HOME has no persisted trust, else the hook is
        # silently skipped). `approval_policy="never"` stops prompts from blocking.
        #
        # MCP note: with approvals active, codex AUTO-CANCELS every MCP tool call
        # unless the server is trusted, so the proof server is auto-approved via
        # `default_tools_approval_mode="approve"` (its only effective value;
        # `auto`/`prompt` still cancel). One server name "proof" covers
        # major/worker/fork (all reuse it).
        #
        # The rest of the surface is stripped via feature flags: shell
        # (`shell_tool`+`unified_exec`), web search (`web_search="disabled"` —
        # the bool `tools.web_search=false` loads but does NOT remove `web.run`),
        # image generation, the codex "apps" site-deploy MCP, goals,
        # browser/computer-use, multi-agent and plugins. Hooks must stay ENABLED
        # (features.hooks=true in config.toml) for the deny-hook to run, so hooks
        # are NOT in the --disable list. Native `update_plan`/`request_user_input`
        # are benign (no host access). `--strict-config` makes a future codex that
        # renames any key fail loudly instead of silently re-enabling it.
        args = [
            "--json",
            "--skip-git-repo-check",
            "-s", "danger-full-access",
            "-m", self._model,
            "-c", 'approval_policy="never"',
            "--dangerously-bypass-hook-trust",
            "-c", f"mcp_servers.{_MCP_SERVER_NAME}.url={json.dumps(url)}",
            "-c", f'mcp_servers.{_MCP_SERVER_NAME}.default_tools_approval_mode="approve"',
            "-c", f"model_reasoning_effort={json.dumps(self._reasoning_effort)}",
            "-c", 'web_search="disabled"',
            "--disable", "shell_tool",
            "--disable", "unified_exec",
            "--disable", "apps",
            "--disable", "image_generation",
            "--disable", "goals",
            "--disable", "multi_agent",
            "--disable", "browser_use",
            "--disable", "browser_use_external",
            "--disable", "computer_use",
            "--disable", "in_app_browser",
            "--disable", "plugins",
            "--disable", "plugin_sharing",
            "--strict-config",
        ]
        if self._model_instructions_path is not None:
            args += ["-c",
                     f"model_instructions_file={json.dumps(self._model_instructions_path)}"]
        return args

    def _build_exec_cmd(self, prompt: str) -> list[str]:
        return [
            "codex", "exec",
            *self._codex_common_args(),
            "-C", self.working_dir,
            prompt,
        ]

    def _build_resume_cmd(self, session_id: str, prompt: str,
                          mcp_url: str | None = None) -> list[str]:
        return [
            "codex", "exec", "resume",
            *self._codex_common_args(mcp_url),
            session_id,
            prompt,
        ]

    # ------------------------------------------------------------------
    # Subprocess execution
    # ------------------------------------------------------------------

    def _raise_codex_failure(self, message: str):
        lower = message.lower()
        if "rate limit" in lower or "429" in lower:
            raise _TransientError(message)
        if ("insufficient_quota" in lower or "quota" in lower
                or "billing" in lower or "402" in lower):
            raise _QuotaError(message)
        if any(marker in lower for marker in (
                "temporarily unavailable", "timeout", "timed out",
                "connection reset", "connection refused", "network error",
                "502", "503", "504")):
            raise _TransientError(message)
        raise InternalError(f"Codex CLI failed: {message}")

    async def _run_codex_exec(self, cmd: list[str]) -> dict:
        try:
            proc = await asyncio.create_subprocess_exec(
                *cmd,
                cwd=self.working_dir,
                env={**os.environ, "CODEX_HOME": self._codex_home_dir},
                # codex 0.141.0 reads stdin (appends it as a <stdin> block) even
                # when the prompt is passed as an argv argument, and blocks until
                # EOF. Hand it an immediate EOF so an inherited, non-EOF stdin in
                # the AoA server process can never hang the codex subprocess.
                stdin=asyncio.subprocess.DEVNULL,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                limit=16 * 1024 * 1024,
                start_new_session=True,
            )
        except FileNotFoundError as e:
            raise InternalError("Codex CLI executable `codex` was not found") from e
        self._exec_process = proc

        events: dict[str, Any] = {}
        stderr_lines: list[str] = []
        turn_failure: str | None = None

        async def drain_stderr():
            assert proc.stderr is not None
            async for line in proc.stderr:
                text = line.decode("utf-8", errors="replace").rstrip()
                if text:
                    stderr_lines.append(text)
                    del stderr_lines[:-50]

        stderr_task = asyncio.create_task(drain_stderr())
        try:
            assert proc.stdout is not None
            async for line in proc.stdout:
                text = line.decode("utf-8", errors="replace").strip()
                if not text:
                    continue
                try:
                    obj = json.loads(text)
                except json.JSONDecodeError:
                    continue
                match obj.get("type"):
                    case "thread.started":
                        events["thread_id"] = obj.get("thread_id")
                    case "turn.completed":
                        events["usage"] = obj.get("usage", {})
                        u = obj.get("usage", {})
                        self.log_cost(
                            f"input={u.get('input_tokens', 0)} "
                            f"cached={u.get('cached_input_tokens', 0)} "
                            f"output={u.get('output_tokens', 0)}")
                    case "item.started":
                        item = obj.get("item", {})
                        if item.get("type") == "mcp_tool_call":
                            self.total_tool_calls += 1
                            if self._model_time_start is not None:
                                self.total_model_time += time() - self._model_time_start
                                self._model_time_start = None
                            # The --json event splits an MCP call into bare
                            # `server`/`tool` fields; codex's canonical name (what
                            # `tool_name`/`is_proof_tool` operate on) is the
                            # flattened mcp__<server>__<tool>, so reassemble it.
                            server = item.get("server", "")
                            bare_tool = item.get("tool", "")
                            qualified = (f"mcp__{server}__{bare_tool}"
                                         if server else bare_tool)
                            tool_args = item.get("arguments", {})
                            if not self.is_proof_tool(qualified):
                                self.log_tool_call(qualified, tool_args)
                    case "item.completed":
                        item = obj.get("item", {})
                        if item.get("type") == "mcp_tool_call":
                            self._model_time_start = time()
                        elif item.get("type") == "agent_message":
                            msg = item.get("text", "")
                            if msg:
                                self.log_model_output(msg)
                    case "error":
                        self.warn_AoA_opr(
                            f"Codex error: {obj.get('message', '')}")
                    case "turn.failed":
                        err = obj.get("error", {}).get("message", "")
                        turn_failure = err or "turn.failed"
                        self.warn_AoA_opr(f"Turn failed: {turn_failure}")
            returncode = await proc.wait()
            await stderr_task
        finally:
            # On cancellation (e.g. Isabelle interrupt) proc.wait() never
            # returned: kill the whole process group so codex and its children
            # are reaped rather than orphaned (and keep burning the API).
            if proc.returncode is None:
                try:
                    os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
                except ProcessLookupError:
                    pass
            self._exec_process = None
            if not stderr_task.done():
                stderr_task.cancel()
                with contextlib.suppress(asyncio.CancelledError):
                    await stderr_task

        if turn_failure is not None:
            self._raise_codex_failure(turn_failure)
        if returncode != 0:
            detail = "\n".join(stderr_lines[-20:]).strip()
            if not detail:
                detail = f"process exited with status {returncode}"
            self._raise_codex_failure(detail)

        return events

    # ------------------------------------------------------------------
    # Cost tracking
    # ------------------------------------------------------------------

    def _record_codex_usage(self, usage: dict):
        # Codex reports input_tokens INCLUSIVE of cached_input_tokens → normalize.
        self._accumulate_usage(Usage.from_inclusive(
            prompt_tokens=usage.get("input_tokens", 0),
            output_tokens=usage.get("output_tokens", 0),
            cached=usage.get("cached_input_tokens", 0)))

    def _pricing(self) -> dict[str, float]:
        return pricing_for(self._model, PRICING["gpt-4.1"])

    # ------------------------------------------------------------------
    # Forking
    # ------------------------------------------------------------------

    async def _do_fork(self, interaction: Interaction,
                       prompt_text: str) -> Any:
        loop = asyncio.get_running_loop()
        ctx = contextvars.copy_context()
        task = loop.create_task(
            self._run_fork(interaction, prompt_text), context=ctx)
        return await task

    async def _run_fork(self, interaction: Interaction, prompt_text: str) -> Any:
        from .model import _session_var, Fork_Pending, Role_Interaction
        _session_var.set(None)  # type: ignore
        fork = Codex_Driver._make_fork(self, role=Role_Interaction(
            pending=Fork_Pending(interaction, asyncio.get_running_loop().create_future()),
            prompt=prompt_text,
            resume_id=None,
            mode=interaction.forking,
        ))
        await fork.initialize(self.root)
        assert fork._mcp_url is not None
        fork_url = fork._mcp_url

        fork_prompt = (
            "Let's consider a sub-task forked from the context:\n"
            + prompt_text)
        answer_tool = self.tool_name(interaction.answer_tool_name)
        if answer_tool not in prompt_text:
            fork_prompt += f"\nAnswer the question above by calling the `{answer_tool}` tool."

        tag = f"[{fork._fork_name}]"
        fork.log_interaction("fork", f"{tag} prompt:\n{prompt_text}")

        try:
          while True:
            try:
                async with self._fork_lock:
                    await self._run_fork_with_backup(
                        fork, fork_url, fork_prompt, tag)
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
                fork._session_id = None
            self.total_input_tokens += fork.total_input_tokens
            self.total_output_tokens += fork.total_output_tokens
            self.total_cache_creation_input_tokens += fork.total_cache_creation_input_tokens
            self.total_cache_read_input_tokens += fork.total_cache_read_input_tokens
            self.total_isabelle_time += fork.total_isabelle_time
            self.total_model_time += fork.total_model_time
            self.total_quota_wait_time += fork.total_quota_wait_time
            await fork.close()

        assert fork.fork_pending is not None and fork.fork_pending.answer.done()
        return fork.fork_pending.answer.result()

    async def _run_fork_with_backup(
        self, fork: 'Codex_Driver', fork_url: str,
        fork_prompt: str, tag: str,
    ) -> None:
        jsonl = self._codex_session_jsonl
        assert jsonl is not None and os.path.exists(jsonl)
        assert self._codex_session_id is not None
        assert fork.fork_pending is not None
        bak = jsonl + ".fork_bak"

        shutil.copy2(jsonl, bak)
        try:
            prompt = fork_prompt
            for attempt in range(self._FORK_ANSWER_MAX_ATTEMPTS):
                if attempt > 0:
                    # Rewind to the parent baseline so each nudge resumes from
                    # the same clean point, then re-snapshot for the next rewind.
                    shutil.copy2(bak, jsonl)
                    shutil.copy2(jsonl, bak)
                cmd = self._build_resume_cmd(
                    self._codex_session_id, prompt, mcp_url=fork_url)

                fork._model_time_start = time()
                events = await fork._run_codex_exec(cmd)
                if fork._model_time_start is not None:
                    fork.total_model_time += time() - fork._model_time_start
                    fork._model_time_start = None

                # Record usage for EVERY resume (including nudges): each emits
                # its own cumulative per-turn usage; missing one drops a whole
                # turn's tokens from accounting.
                fork._record_codex_usage(events.get("usage", {}))

                if fork.fork_pending.answer.done():
                    return
                fork.log_interaction(
                    "fork",
                    f"{tag} answer not received "
                    f"(attempt {attempt + 1}/{self._FORK_ANSWER_MAX_ATTEMPTS})")
                prompt = (
                    "You haven't submitted your answer. Call the "
                    f"`{self.tool_name(fork.fork_pending.interaction.answer_tool_name)}` "
                    "tool to submit it.")
            raise InternalError(
                f"{tag} fork did not submit an answer after "
                f"{self._FORK_ANSWER_MAX_ATTEMPTS} attempts")
        finally:
            shutil.copy2(bak, jsonl)
            try:
                os.unlink(bak)
            except OSError:
                pass
