from typing import Any
import asyncio
import contextvars
import os
import shutil
import tempfile
import uuid
from io import StringIO
from time import time

from agents import (
    Agent,
    MaxTurnsExceeded,
    ModelSettings,
    RunHooks,
    Runner,
    Usage,
)
from openai.types.shared import Reasoning
from agents.items import ModelResponse
from agents.mcp import MCPServerStreamableHttp
from agents.retry import ModelRetrySettings

from .model import *
from .language_model_driver import LMDriver, _TransientError, _QuotaError, PRICING, pricing_for, Usage as LMUsage

from .mcp_http_server import ProofMCPHTTPServer


@agent_driver("OpenAI")
class OpenAI_Driver(LMDriver):
    DEFAULT_MODEL = "gpt-5.5"
    FORK_CHEAPER_MODEL = "gpt-4.1-mini"

    working_dir: str
    _fork_counter: int
    _fork_name: str

    def __str__(self) -> str:
        return f"{self._driver_name}({self._model})"

    def __init__(self, *args, parent: 'OpenAI_Driver | None' = None,
                 model: str | None = None, argument: str | None = None, **kwargs):
        super().__init__(*args, parent=parent, **kwargs)
        self._model = argument or model or self.DEFAULT_MODEL
        if parent is not None:
            self.working_dir = parent.working_dir
            self.YAML_path = parent.YAML_path
            self.root = parent.root
            self._http_server = parent._http_server
            self._cache_key = parent._cache_key
            parent._fork_counter += 1
            self._fork_name = f"{parent._fork_name}.fork_{parent._fork_counter}"
        else:
            self.working_dir = tempfile.mkdtemp(prefix="agent_AoA_openai_")
            if not os.access(self.working_dir, os.R_OK | os.W_OK):
                raise InternalError(
                    f"The working directory {self.working_dir} is not readable and writable.")
            self.YAML_path = os.path.join(self.working_dir, "proof.yaml")
            self._http_server: ProofMCPHTTPServer | None = None
            self._fork_name = "main"
            self._cache_key = f"proof-{uuid.uuid4().hex[:8]}"

        self._model_time_start: float | None = None
        self._session_id: str | None = None
        self._mcp_url: str | None = None
        self._last_response_id: str | None = None
        self._forkable_response_id: str | None = None
        self._fork_counter = 0
        self._runner_task: asyncio.Task | None = None

    @classmethod
    def _make_fork(cls, parent: 'OpenAI_Driver', role=None) -> 'OpenAI_Driver':
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

    async def initialize(self, root: Root):
        await super().initialize(root)
        if self._http_server is None:
            self._http_server = await ProofMCPHTTPServer.get_or_create()
        self._session_id = self._http_server.allocate_session_id()
        self._mcp_url = await self._http_server.register_session(
            self._session_id, self)
        # Seed proof.yaml. `refresh_YAML` -> `print_proof_scope`, which renders
        # the full `root` for a major (non-worker) and the scoped view for a
        # worker — so a single call covers both. Interaction forks are neither
        # and intentionally write no YAML.
        if self.is_major or self.is_worker:
            self.refresh_YAML()

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

    async def interrupt(self):
        if self._runner_task is not None:
            self._runner_task.cancel()

    def _make_hooks(self) -> '_ProverHooks':
        return OpenAI_Driver._ProverHooks(self)

    def _make_mcp(self, url: str) -> MCPServerStreamableHttp:
        return MCPServerStreamableHttp(
            params={"url": url},
            name="proof",
            cache_tools_list=True,
            client_session_timeout_seconds=300,
        )

    def _make_agent(self, mcp: MCPServerStreamableHttp,
                    model: str | None = None) -> Agent:
        return Agent(
            name="prover",
            model=model or self._model,
            instructions=self.system_prompt(),
            mcp_servers=[mcp],
            model_settings=ModelSettings(
                truncation="auto",
                store=True,
                reasoning=Reasoning(effort="high"),
                prompt_cache_retention="24h",
                extra_body={"prompt_cache_key": self._cache_key},
                retry=ModelRetrySettings(max_retries=3),
            ),
        )

    async def _run_agent_loop(self):
        await self._with_retry(self._openai_loop)

    async def _openai_loop(self):
        assert self._mcp_url is not None
        self._budget_start_time = time()
        mcp = self._make_mcp(self._mcp_url)
        agent = self._make_agent(mcp)
        hooks = self._make_hooks()
        try:
            async with mcp:
                while True:  # outer restart loop (mirrors codex/api re-route)
                    prompt: str | None = await self.initial_prompt()
                    if self._refresh_summary is not None:
                        prompt += "\n\nAgent's briefing:\n" + self._refresh_summary
                        self._refresh_summary = None
                    last_response_id: str | None = None
                    while True:
                        self._model_time_start = time()
                        try:
                            self._runner_task = asyncio.current_task()
                            await Runner.run(
                                agent, prompt,
                                hooks=hooks,
                                max_turns=1000,
                                previous_response_id=last_response_id,
                            )
                        except MaxTurnsExceeded:
                            self.warn_AoA_opr("Max turns exceeded in single run segment")
                        except asyncio.CancelledError:
                            self.log_AoA_opr("Run cancelled (proof complete or interrupt)")
                            if self._model_time_start is not None:
                                self.total_model_time += time() - self._model_time_start
                                self._model_time_start = None
                            break
                        finally:
                            self._runner_task = None

                        if self._model_time_start is not None:
                            self.total_model_time += time() - self._model_time_start
                            self._model_time_start = None

                        last_response_id = self._last_response_id
                        self._forkable_response_id = last_response_id
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

                    # Restart re-route: a pending Restart() exits the inner loop
                    # (via the quit_info guard / check_budget) and is re-entered
                    # here; any other exit (terminal / proof-complete) breaks out.
                    if not isinstance(self.quit_info, (Restart, Refresh)):
                        break

                    if isinstance(self.quit_info, Refresh):
                        self._refresh_summary = self.quit_info.briefing
                        self.quit_info = None
                        self._reset_view_state()
                        self.runtime.age += 1
                        self.refresh_YAML()
                        self._total_calls_at_last_refresh = self.total_tool_calls
                        self.log_AoA_opr("Context refreshed")
                        self._log_meta("REFRESH", briefing=self._refresh_summary)
                        continue

                    self.quit_info = None
                    self.refresh_YAML()
                    self.log_AoA_opr("Context restarted")
                    self._log_meta("CONTEXT_RESTART")
        except Exception as e:
            import openai as _openai
            if isinstance(e, _openai.RateLimitError):
                if "insufficient_quota" in str(e):
                    raise _QuotaError(str(e)) from e
                raise _TransientError(str(e)) from e
            if isinstance(e, _openai.APIError):
                raise _TransientError(str(e)) from e
            raise

        self._compute_cost()
        self.log_proof()

    def _pricing(self) -> dict[str, float]:
        return pricing_for(self._model, PRICING["gpt-4.1"])

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
        mode = interaction.forking
        fork = OpenAI_Driver._make_fork(self, role=Role_Interaction(
            pending=Fork_Pending(interaction, asyncio.get_running_loop().create_future()),
            prompt=prompt_text,
            resume_id=self._forkable_response_id if mode == ForkingMode.FORKING_WITH_CTXT else None,
            mode=mode,
        ))
        await fork.initialize(self.root)
        assert fork._mcp_url is not None
        fork_url = fork._mcp_url

        mode = interaction.forking
        if mode == ForkingMode.FORKING_CHEAPER_NO_CTXT:
            fork_model = self.FORK_CHEAPER_MODEL
        else:
            fork_model = self._model

        if mode == ForkingMode.FORKING_WITH_CTXT:
            previous_response_id = self._forkable_response_id
        else:
            previous_response_id = None

        fork_mcp = self._make_mcp(fork_url)
        fork_agent = self._make_agent(fork_mcp, model=fork_model)
        fork_hooks = fork._make_hooks()

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
              async with fork_mcp:
                while True:
                    fork._model_time_start = time()
                    try:
                        await Runner.run(
                            fork_agent,
                            fork_prompt,
                            hooks=fork_hooks,
                            max_turns=30,
                            previous_response_id=previous_response_id,
                        )
                    except MaxTurnsExceeded:
                        fork.log_interaction("fork", f"{tag} max turns exceeded")
                    except asyncio.CancelledError:
                        break

                    if fork._model_time_start is not None:
                        fork.total_model_time += time() - fork._model_time_start
                        fork._model_time_start = None

                    assert fork.fork_pending is not None
                    if fork.fork_pending.answer.done():
                        fork.log_interaction(
                            "fork", f"{tag} completed")
                        break

                    fork.log_interaction("fork", f"{tag} retrying: interaction not answered")
                    fork_prompt = (
                        "You haven't submitted your answer. "
                        f"Call the `{self.tool_name(fork.fork_pending.interaction.answer_tool_name)}` tool to submit it.")
                    previous_response_id = fork._last_response_id
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

    # ------------------------------------------------------------------
    # YAML refresh
    # ------------------------------------------------------------------

    def refresh_YAML(self):
        with open(self.YAML_path, 'w', encoding="utf-8") as f:
            self.print_proof_scope(0, MyIO(f), update_line=True, show_warnings=True)

    # ------------------------------------------------------------------
    # RunHooks
    # ------------------------------------------------------------------

    class _ProverHooks(RunHooks):
        def __init__(self, session: 'OpenAI_Driver'):
            self.session = session

        async def on_tool_start(self, context, agent, tool):
            s = self.session
            if s._model_time_start is not None:
                s.total_model_time += time() - s._model_time_start
                s._model_time_start = None
            s.total_tool_calls += 1

        async def on_tool_end(self, context, agent, tool, result):
            self.session._model_time_start = time()

        async def on_llm_end(self, context, agent, response: ModelResponse):
            s = self.session
            u: Usage = response.usage  # the agents-SDK Usage (input_tokens INCLUDES cache)
            cached = u.input_tokens_details.cached_tokens if u.input_tokens_details else 0
            s._accumulate_usage(LMUsage.from_inclusive(
                prompt_tokens=u.input_tokens, output_tokens=u.output_tokens, cached=cached))
            if response.response_id:
                s._last_response_id = response.response_id
