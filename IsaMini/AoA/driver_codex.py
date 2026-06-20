from typing import Any
import asyncio
import contextlib
import contextvars
import glob
import json
import os
import shutil
import signal
import subprocess
import tempfile
from time import time

import platformdirs

from .model import *
from .language_model_driver import LMDriver, _TransientError, _QuotaError, PRICING, pricing_for, _parse_effort_suffix, Usage

from .mcp_http_server import ProofMCPHTTPServer


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
            self._init_git_repo()
        # Seed proof.yaml. `refresh_YAML` -> `print_proof_scope`, which renders
        # the full `root` for a major (non-worker) and the scoped view for a
        # worker — so a single call covers both. Interaction forks are neither
        # and intentionally write no YAML.
        if self.is_major or self.is_worker:
            self._write_model_instructions()
            self.refresh_YAML()

    def _write_codex_config(self):
        # config.toml must be at the TOP level of CODEX_HOME to be read.
        with open(os.path.join(self._codex_home_dir, "config.toml"), "w") as f:
            f.write(f'[mcp_servers.proof]\nurl = {json.dumps(self._mcp_url)}\n')

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

    def _init_git_repo(self):
        subprocess.run(
            ["git", "init"], cwd=self.working_dir,
            capture_output=True, check=True)
        subprocess.run(
            ["git", "config", "user.email", "aoa-codex@example.invalid"],
            cwd=self.working_dir, capture_output=True, check=True)
        subprocess.run(
            ["git", "config", "user.name", "AoA Codex Driver"],
            cwd=self.working_dir, capture_output=True, check=True)
        subprocess.run(
            ["git", "add", "."], cwd=self.working_dir,
            capture_output=True, check=True)
        subprocess.run(
            ["git", "commit", "-m", "init"],
            cwd=self.working_dir, capture_output=True, check=True)

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
        args = [
            "--json",
            "--dangerously-bypass-approvals-and-sandbox",
            "-m", self._model,
            "-c", f"mcp_servers.proof.url={json.dumps(url)}",
            "-c", f"model_reasoning_effort={json.dumps(self._reasoning_effort)}",
            # Remove the native shell so the agent cannot run arbitrary commands;
            # it operates only through the MCP proof tools. (apply_patch cannot be
            # disabled on 0.139.0 — a known residual under bypass.)
            "-c", "features.unified_exec=false",
            "-c", "features.shell_tool=false",
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
                            tool_name = item.get("tool", "")
                            tool_args = item.get("arguments", {})
                            if not self.is_proof_tool(tool_name):
                                self.log_tool_call(tool_name, tool_args)
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
