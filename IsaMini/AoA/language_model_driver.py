"""Base class and error types for LLM-backed AoA drivers."""

from __future__ import annotations

import asyncio
import contextvars
from dataclasses import dataclass
from time import time
from typing import Awaitable, Callable, Literal, TypeVar

from .model import (
    AoA_Error, EvaluationStatus, Interaction_Finishing, NonLeaf_Node,
    PlanStage, Role_Plan, Role_Worker, Session, _session_var,
)

_T = TypeVar("_T")


class _TransientError(AoA_Error):
    """Transient failure (5xx, connection drop, timeout, 429 rate limit).
    Retried with exponential backoff at the per-call layer."""
    pass


class _QuotaError(AoA_Error):
    """Quota / billing exhausted.  Long wait then retry at the outer layer."""
    pass


class LMDriver(Session):
    """Session subclass that adds unified retry logic for LLM drivers.

    Subclasses implement ``_run_agent_loop()`` (the agent loop) and optionally
    ``_run_fork()`` (for fork interactions).
    """

    def _on_start_run(self):
        """Called at the start of ``run()``.  Override to customise logging."""
        self.log_AoA_opr(
            f"Driver {self}, Working directory: {getattr(self, 'working_dir', '?')}, "
            f"Log directory: {self.log_dir}")

    async def run(self):
        self._on_start_run()
        try:
            match self.role:
                case Role_Plan():
                    await self._run_planning()
                case _:
                    await self._run_agent_loop()
        except asyncio.CancelledError:
            self.warn_AoA_opr("Cancelled (Isabelle interrupted)")
            raise

    async def _run_planning(self):
        while True:
            await self._run_agent_loop()

            if not (isinstance(self.role, Role_Plan)
                    and self.role.stage == PlanStage.PLANNING):
                break
            if self.proof_scope_unfinished_nodes():
                break

            self.role.stage = PlanStage.FINISHING
            await self.root._refresh_me_alone(auto_intro=False)

            failed_parents = self._collect_failed_obvious_parents()
            if not failed_parents:
                break

            self.refresh_YAML()
            interaction = Interaction_Finishing(list(failed_parents), self)
            result = await self.fork_interaction(interaction)

            match result:
                case "all_proved":
                    break
                case ("surrender", _):
                    self.role.stage = PlanStage.PLANNING
                    continue
                case ("refute_accepted", _):
                    self.role.stage = PlanStage.PLANNING
                    continue
                case _:
                    break

    async def _with_retry(self, fn: Callable[[], Awaitable]):
        """Retry *fn()* on quota exhaustion or transient API errors."""
        while True:
            try:
                return await fn()
            except _QuotaError:
                self.warn_AoA_opr("Quota exhausted, waiting 20min to retry")
                t0 = time()
                await asyncio.sleep(1200)
                self.total_quota_wait_time += time() - t0
            except _TransientError as e:
                self.warn_AoA_opr(f"Transient API error, retrying in 2s: {e}")
                await asyncio.sleep(2)

    async def _run_agent_loop(self):
        raise NotImplementedError

    async def _retry_transient(self, fn: Callable[[], Awaitable[_T]]) -> _T:
        """Inner retry layer: call *fn()*, retrying ``_TransientError``
        with 1.5^n-second exponential backoff up to 10 attempts."""
        for attempt in range(10):
            try:
                return await fn()
            except _TransientError as e:
                if attempt < 9:
                    wait = 1.5 ** attempt
                    self.warn_AoA_opr(
                        f"Transient API error (attempt {attempt + 1}/10, "
                        f"retry in {wait:.1f}s): {e}")
                    await asyncio.sleep(wait)
                else:
                    raise
        assert False  # unreachable

    # --- Worker spawning ---

    def _accumulate_subagent_costs(self, sub: 'LMDriver'):
        self.total_input_tokens += sub.total_input_tokens
        self.total_output_tokens += sub.total_output_tokens
        self.total_cache_creation_input_tokens += sub.total_cache_creation_input_tokens
        self.total_cache_read_input_tokens += sub.total_cache_read_input_tokens
        self.total_cost_usd += sub.total_cost_usd
        self.total_isabelle_time += sub.total_isabelle_time
        self.total_model_time += sub.total_model_time
        self.total_quota_wait_time += sub.total_quota_wait_time

    async def spawn_worker(self, target: NonLeaf_Node) -> WorkerResult:
        ctx = contextvars.copy_context()
        loop = asyncio.get_running_loop()
        task = loop.create_task(self._run_worker(target), context=ctx)
        result = await task
        self.refresh_YAML()
        return result

    async def _run_worker(self, target: NonLeaf_Node) -> WorkerResult:
        _session_var.set(None)  # type: ignore
        sub = self.__class__._make_fork(self, role=Role_Worker(target=target))
        sub._fork_name = f"{self._fork_name}.worker_{target.id}"
        await sub.initialize(self.root)

        tag = f"[{sub._fork_name}]"
        self.log_interaction("worker", f"{tag} spawned")

        try:
            await sub.run()
        except asyncio.CancelledError:
            self.warn_AoA_opr(f"{tag} cancelled")
        except Exception as e:
            self.warn_AoA_opr(f"{tag} failed: {type(e).__name__}: {e}")
        finally:
            raw = self.root.quit_info
            self.root.quit_info = None
            self._accumulate_subagent_costs(sub)
            await sub.close()

        complaint = None
        if raw is not None and len(raw) >= 2 and raw[0] in ("refute", "surrender"):
            suggested = raw[2] if len(raw) > 2 else None
            complaint = WorkerComplaint(kind=raw[0], detail=raw[1],
                                        suggested_lemmas=suggested)

        return WorkerResult(
            success=target.status.status == EvaluationStatus.Status.SUCCESS,
            complaint=complaint,
        )


@dataclass
class WorkerComplaint:
    kind: Literal["refute", "surrender"]
    detail: str
    suggested_lemmas: list | None = None

@dataclass
class WorkerResult:
    success: bool
    complaint: WorkerComplaint | None = None
