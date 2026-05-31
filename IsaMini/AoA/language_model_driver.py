"""Base class and error types for LLM-backed AoA drivers."""

from __future__ import annotations

import asyncio
import contextvars
from dataclasses import dataclass
from time import time
from typing import Awaitable, Callable, Literal, TypeVar

from .model import (
    AoA_Error, ContinuingInteraction,
    Interaction_ChooseTarget, Interaction_ReviewRefutation,
    NonLeaf_Node, Role_Plan, Role_Worker, Session, _session_var,
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
        # The FINISHING flow (target selection, worker dispatch, refutation
        # review) is now driven from inside the agent loop via
        # ``Session.complete_proof`` (called by the edit/delete tools when the
        # proof structure is complete). This keeps the planning agent's
        # conversation context intact across the whole proof.
        await self._run_agent_loop()

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


@dataclass
class WorkerComplaint:
    kind: Literal["refute", "surrender", "resource_exhausted"]
    detail: str
    suggested_lemmas: list | None = None


# --- Worker events ---------------------------------------------------------
# A live worker communicates with the planning agent through its
# ``WorkerHandle``'s event queue instead of dying and leaving a ``quit_info``
# behind. This lets the worker block (and later resume) while the planning
# agent reviews a refutation, preserving the worker's conversation context.

@dataclass
class WorkerRefute:
    """Worker claims the goal is unprovable and awaits the planning agent's
    review. ``response_future`` is resolved with ``(accepted, reason)`` by
    ``WorkerHandle.resolve_review``; the worker blocks on it inside the
    ``complain`` tool until then."""
    detail: str
    suggested_lemmas: list | None
    response_future: 'asyncio.Future[tuple[bool, str | None]]'

@dataclass
class WorkerSurrender:
    """Worker gives up (no viable strategy / needs help). Terminal — the
    worker interrupts itself right after emitting this."""
    detail: str
    suggested_lemmas: list | None

@dataclass
class WorkerDone:
    """The worker task finished. ``success`` reflects whether the target goal
    is proved. Synthesised by ``WorkerHandle`` when the task completes without
    a pending event."""
    success: bool


class WorkerHandle:
    """Owns a running worker sub-session and mediates between it and the
    planning agent's FINISHING interactions.

    The worker runs as its own asyncio task. Its lifecycle events arrive
    either through ``_event_queue`` (refute / surrender, pushed by the
    ``complain`` tool) or as task completion (mapped to ``WorkerDone``).
    ``process`` consumes one event and either returns a planning-agent-facing
    string, returns ``None`` (all targets proved), or raises
    ``ContinuingInteraction`` to chain the next FINISHING interaction without
    breaking the planning agent's context."""

    def __init__(self, target: NonLeaf_Node, session: 'LMDriver'):
        self.target = target
        self.session = session
        self._event_queue: 'asyncio.Queue' = asyncio.Queue()
        self._task: 'asyncio.Task | None' = None
        self._sub: 'LMDriver | None' = None
        self._pending_review: 'asyncio.Future[tuple[bool, str | None]] | None' = None

    def start(self, suggestions: str = "",
              useful_lemmas: list[str] | None = None) -> None:
        ctx = contextvars.copy_context()
        loop = asyncio.get_running_loop()
        self._task = loop.create_task(
            self._run(suggestions, useful_lemmas or []), context=ctx)

    async def _run(self, suggestions: str, useful_lemmas: list[str]) -> None:
        _session_var.set(None)  # type: ignore
        session = self.session
        try:
            sub = session.__class__._make_fork(
                session, role=Role_Worker(target=self.target,
                                          suggestions=suggestions,
                                          useful_lemmas=useful_lemmas,
                                          worker_handle=self))
            sub._fork_name = f"{session._fork_name}.worker_{self.target.id}"
            self._sub = sub
            await sub.initialize(session.root)
        except Exception as e:
            session.warn_AoA_opr(f"Worker init failed for {self.target.id}: {e}")
            return

        tag = f"[{sub._fork_name}]"
        session.log_interaction("worker", f"{tag} spawned")
        try:
            await sub.run()
        except asyncio.CancelledError:
            session.warn_AoA_opr(f"{tag} cancelled")
            raise
        except Exception as e:
            session.warn_AoA_opr(f"{tag} failed: {type(e).__name__}: {e}")
        finally:
            session._accumulate_subagent_costs(sub)
            try:
                await sub.close()
            except Exception as e:
                session.warn_AoA_opr(f"{tag} close failed: {e}")

    async def _wait_next_event(self):
        """Return the next worker event. A queued event (refute/surrender)
        always wins over task completion: ``put_nowait`` synchronously
        resolves the pending ``queue.get()`` future, and FIFO callback
        ordering guarantees we observe it before the task's completion."""
        assert self._task is not None
        queue_get = asyncio.ensure_future(self._event_queue.get())
        done, _pending = await asyncio.wait(
            {self._task, queue_get},
            return_when=asyncio.FIRST_COMPLETED)
        if queue_get in done:
            return queue_get.result()
        queue_get.cancel()
        exc = self._task.exception()
        if exc is not None:
            raise exc
        # Worker succeeded iff the target's subtree has NO unfinished nodes.
        # `target.status` alone is NOT sufficient: for a NonLeaf_Node it
        # reflects only the node's own declaration/goal, not whether the proof
        # below it is complete — child steps may still be unproved. This is the
        # same criterion the worker's own loop uses to decide it is done
        # (proof_scope_unfinished_nodes → target.unfinished_nodes).
        unfinished: set = set()
        self.target.unfinished_nodes(unfinished)
        return WorkerDone(success=not unfinished)

    async def process(self, choose_target: 'Interaction_ChooseTarget'):
        """Consume worker events until a terminal one, then either return a
        planning-agent-facing string / ``None`` or raise
        ``ContinuingInteraction``. ``choose_target`` is the originating
        ``Interaction_ChooseTarget`` whose ``failed_parents`` set is updated."""
        event = await self._wait_next_event()
        match event:
            case WorkerRefute():
                self._pending_review = event.response_future
                complaint = WorkerComplaint(
                    kind="refute", detail=event.detail,
                    suggested_lemmas=event.suggested_lemmas)
                raise ContinuingInteraction(
                    new_interaction=Interaction_ReviewRefutation(
                        self.target, complaint, self, choose_target))
            case WorkerSurrender():
                await self.wait_finish()
                self.session.refresh_YAML()
                return (f"Worker on {self.target.id} surrendered: "
                        f"{event.detail}\n"
                        f"Reconsider the proof plan for this step.")
            case WorkerDone(success=True):
                await self.wait_finish()
                self.session.refresh_YAML()
                choose_target.failed_parents.discard(self.target)
                if not choose_target.failed_parents:
                    return None
                choose_target.is_first_entry = False
                raise ContinuingInteraction(new_interaction=choose_target)
            case _:  # WorkerDone(success=False)
                await self.wait_finish()
                self.session.refresh_YAML()
                return (f"Worker on {self.target.id} could not prove the goal. "
                        f"Reconsider the proof plan for this step.")

    def resolve_review(self, accepted: bool, reason: str | None = None) -> None:
        fut = self._pending_review
        self._pending_review = None
        if fut is not None and not fut.done():
            fut.set_result((accepted, reason))

    async def wait_finish(self) -> None:
        if self._task is not None:
            try:
                await self._task
            except asyncio.CancelledError:
                pass

    def cancel(self) -> None:
        """Best-effort synchronous teardown: unblock a worker waiting on its
        review (so its ``await fut`` raises) and cancel the worker task. Does
        NOT await the task — use ``aclose`` for guaranteed cleanup."""
        if self._pending_review is not None and not self._pending_review.done():
            self._pending_review.cancel()
        self._pending_review = None
        if self._task is not None and not self._task.done():
            self._task.cancel()

    async def aclose(self) -> None:
        """Idempotent teardown that GUARANTEES the worker is gone: cancel it,
        then await the task (swallowing ``CancelledError``). Safe to call when
        the worker already finished. Used by ``Session.complete_proof`` in a
        ``finally`` so a worker can never leak if the review fork exits without
        an answer (e.g. fork-loop exhaustion → the worker would otherwise stay
        blocked forever on its review future)."""
        self.cancel()
        await self.wait_finish()
