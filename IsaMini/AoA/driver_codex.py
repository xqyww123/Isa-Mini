from typing import Any
import asyncio
import contextvars
import glob
import json
import os
import shutil
import subprocess
import tempfile
from datetime import datetime
from io import StringIO
from time import time

import platformdirs

from .model import *
from .language_model_driver import LMDriver, _TransientError, _QuotaError

from .mcp_http_server import ProofMCPHTTPServer


@agent_driver("Codex")
class Codex_Driver(LMDriver):
    DEFAULT_MODEL = "gpt-5.3-codex"

    _PRICING: dict[str, dict[str, float]] = {
        "gpt-5.5":      {"input": 5.00e-6, "cached": 0.50e-6, "output": 15.00e-6},
        "gpt-5.4":      {"input": 2.50e-6, "cached": 0.25e-6, "output": 10.00e-6},
        "gpt-4.1":      {"input": 2.00e-6, "cached": 0.50e-6, "output": 8.00e-6},
        "gpt-4.1-mini": {"input": 0.40e-6, "cached": 0.10e-6, "output": 1.60e-6},
        "gpt-4.1-nano": {"input": 0.10e-6, "cached": 0.025e-6, "output": 0.40e-6},
        "o3":           {"input": 2.00e-6, "cached": 0.50e-6, "output": 8.00e-6},
        "o4-mini":      {"input": 1.10e-6, "cached": 0.275e-6, "output": 4.40e-6},
    }

    working_dir: str
    _fork_counter: int
    _fork_name: str

    def __init__(self, *args, parent: 'Codex_Driver | None' = None,
                 model: str | None = None, argument: str | None = None, **kwargs):
        if argument is not None:
            raise DriverArgumentError(
                f"Driver 'Codex' does not accept arguments, but got '{argument}'")
        super().__init__(*args, parent=parent, **kwargs)
        self._model = model or self.DEFAULT_MODEL
        if parent is not None:
            self.working_dir = parent.working_dir
            self.YAML_path = parent.YAML_path
            self.root = parent.root
            self._http_server = parent._http_server
            self._fork_lock = parent._fork_lock
            self._codex_session_id = parent._codex_session_id
            self._codex_session_jsonl = parent._codex_session_jsonl
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

        self._model_time_start: float | None = None
        self._session_id: str | None = None
        self._mcp_url: str | None = None
        self._fork_counter = 0
        self._exec_process: asyncio.subprocess.Process | None = None

    @classmethod
    def _make_fork(cls, parent: 'Codex_Driver', role=None) -> 'Codex_Driver':
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

    def system_prompt(self) -> str | None:
        return None

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
            self.refresh_YAML()

    def _write_codex_config(self):
        config_dir = os.path.join(self.working_dir, ".codex")
        os.makedirs(config_dir, exist_ok=True)
        with open(os.path.join(config_dir, "config.toml"), "w") as f:
            f.write(f'[mcp_servers.proof]\nurl = "{self._mcp_url}"\n')

    def _init_git_repo(self):
        subprocess.run(
            ["git", "init"], cwd=self.working_dir,
            capture_output=True, check=True)
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
        if self.is_major and hasattr(self, 'working_dir') and os.path.exists(self.working_dir):
            try:
                shutil.rmtree(self.working_dir)
                self.debug_info(f"[CLEANUP] Removed temporary directory: {self.working_dir}")
            except Exception as e:
                self.debug_info(f"[CLEANUP] Failed to remove temporary directory {self.working_dir}: {e}")
        if self.is_major and self._codex_session_jsonl and os.path.exists(self._codex_session_jsonl):
            try:
                os.unlink(self._codex_session_jsonl)
            except OSError:
                pass

    def _on_start_run(self):
        self.log_AoA_opr(f"Working directory: {self.working_dir}, Log directory: {self.log_dir}")

    async def interrupt(self):
        if self._exec_process is not None:
            self._exec_process.terminate()

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
        sessions_dir = os.path.join(self._codex_home(), "sessions")
        now = datetime.now()
        date_dir = os.path.join(
            sessions_dir, str(now.year), f"{now.month:02d}", f"{now.day:02d}")
        matches = glob.glob(os.path.join(date_dir, f"*{session_id}.jsonl"))
        if not matches:
            matches = glob.glob(
                os.path.join(sessions_dir, "**", f"*{session_id}.jsonl"),
                recursive=True)
        if not matches:
            raise InternalError(f"Codex session JSONL not found for {session_id}")
        return matches[0]

    async def _run_agent_loop(self):
        await self._with_retry(self._codex_loop)

    async def _codex_loop(self):
        self._budget_start_time = time()
        prompt = await self.initial_prompt()
        codex_session_id: str | None = None

        while True:  # outer restart loop
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

                self._accumulate_usage(events.get("usage", {}))

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

            if not isinstance(self.quit_info, Restart):
                break
            self.quit_info = None
            self.refresh_YAML()
            codex_session_id = None
            prompt = await self.initial_prompt()
            self.log_AoA_opr("Context restarted")
            self._log_meta("CONTEXT_RESTART")

        self._compute_cost()
        self.log_proof()

    def _build_exec_cmd(self, prompt: str) -> list[str]:
        return [
            "codex", "exec", prompt,
            "--json",
            "--dangerously-bypass-approvals-and-sandbox",
            "-m", self._model,
            "-C", self.working_dir,
        ]

    def _build_resume_cmd(self, session_id: str, prompt: str) -> list[str]:
        return [
            "codex", "exec", "resume", session_id, prompt,
            "--json",
            "-m", self._model,
        ]

    # ------------------------------------------------------------------
    # Subprocess execution
    # ------------------------------------------------------------------

    async def _run_codex_exec(self, cmd: list[str]) -> dict:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            limit=16 * 1024 * 1024,
        )
        self._exec_process = proc

        events: dict[str, Any] = {}
        try:
            assert proc.stdout is not None
            async for line in proc.stdout:
                text = line.strip()
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
                            f"input={u.get('input_tokens',0)} "
                            f"cached={u.get('cached_input_tokens',0)} "
                            f"output={u.get('output_tokens',0)}")
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
                        if "rate limit" in err.lower() or "429" in err:
                            raise _TransientError(err)
                        if "insufficient_quota" in err or "402" in err:
                            raise _QuotaError(err)
                        self.warn_AoA_opr(f"Turn failed: {err}")
            await proc.wait()
        finally:
            self._exec_process = None

        return events

    # ------------------------------------------------------------------
    # Cost tracking
    # ------------------------------------------------------------------

    def _accumulate_usage(self, usage: dict):
        self.total_input_tokens += usage.get("input_tokens", 0)
        self.total_output_tokens += usage.get("output_tokens", 0)
        self.total_cache_read_input_tokens += usage.get("cached_input_tokens", 0)
        self._log_meta("USAGE", **usage)

    def _compute_cost(self):
        p = self._PRICING.get(self._model, self._PRICING["gpt-4.1"])
        non_cached = max(0, self.total_input_tokens - self.total_cache_read_input_tokens)
        self.total_cost_usd = (
            non_cached * p["input"]
            + self.total_cache_read_input_tokens * p["cached"]
            + self.total_output_tokens * p["output"]
        )

    # ------------------------------------------------------------------
    # Forking
    # ------------------------------------------------------------------

    async def fork_interaction(self, interaction: Interaction) -> Any:
        buffer = StringIO()
        try:
            await interaction.prompt(0, MyIO(buffer))
        except ImmediateAnswer as e:
            return e.answer

        loop = asyncio.get_running_loop()
        ctx = contextvars.copy_context()
        task = loop.create_task(
            self._run_fork(interaction, buffer.getvalue()), context=ctx)
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
        bak = jsonl + ".fork_bak"

        shutil.copy2(jsonl, bak)
        try:
            cmd = [
                "codex", "exec", "resume",
                self._codex_session_id, fork_prompt,
                "--json",
                "-m", self._model,
                "-c", f'mcp_servers.proof.url="{fork_url}"',
            ]

            fork._model_time_start = time()
            events = await fork._run_codex_exec(cmd)
            if fork._model_time_start is not None:
                fork.total_model_time += time() - fork._model_time_start
                fork._model_time_start = None

            fork._accumulate_usage(events.get("usage", {}))

            assert fork.fork_pending is not None
            if not fork.fork_pending.answer.done():
                fork.log_interaction("fork", f"{tag} retrying: answer not received")
                shutil.copy2(bak, jsonl)
                shutil.copy2(jsonl, bak)
                retry_cmd = [
                    "codex", "exec", "resume",
                    self._codex_session_id,
                    "You haven't submitted your answer. "
                    f"Call the `{self.tool_name(fork.fork_pending.interaction.answer_tool_name)}` tool to submit it.",
                    "--json",
                    "-m", self._model,
                    "-c", f'mcp_servers.proof.url="{fork_url}"',
                ]
                await fork._run_codex_exec(retry_cmd)
        finally:
            shutil.copy2(bak, jsonl)
            try:
                os.unlink(bak)
            except OSError:
                pass
