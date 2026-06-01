"""Base class and error types for LLM-backed AoA drivers."""

from __future__ import annotations

import asyncio
import contextvars
from dataclasses import dataclass
from time import time
from typing import Any, Awaitable, Callable, Literal, TypeVar

from .model import (
    AoA_Error, ContinuingInteraction, ResourceExhausted,
    Interaction_ChooseTarget, Interaction_ReviewRefutation,
    Interaction_ReviewLemmaRequest, WORKER_NESTING_LIMIT,
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
    ``refute_or_surrender`` tool until then."""
    detail: str
    response_future: 'asyncio.Future[tuple[bool, str | None]]'

@dataclass
class WorkerSurrender:
    """Worker gives up (no viable strategy / needs help). Terminal — the
    worker interrupts itself right after emitting this."""
    detail: str

@dataclass
class WorkerRequestLemmas:
    """Worker asks the planning agent to author + prove helper lemmas, then
    resume. NON-terminal (the worker keeps working afterwards, like a rejected
    refutation). ``lemmas`` is the worker's *loose* wish-list
    (``{name, english, isabelle_statement}`` items); the planner re-authors them
    precisely. ``response_future`` is resolved with a feedback STRING by
    ``WorkerHandle.resolve_lemma_request``; the worker blocks on it inside the
    ``request_lemmas`` tool until then."""
    detail: str
    lemmas: list | None
    response_future: 'asyncio.Future[str]'

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
    ``refute_or_surrender`` tool) or as task completion (mapped to ``WorkerDone``).
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
        # Pending lemma-request review (resolved with a feedback STRING — a
        # distinct result type from _pending_review's (accepted, reason) tuple).
        self._pending_lemma_request: 'asyncio.Future[str] | None' = None
        # What to chain when THIS worker finishes / how its reviews resume:
        # the originating Interaction_ChooseTarget for a FINISHING worker, or a
        # LemmaDrive for a lemma sub-agent (None until set by the spawner).
        self.continuation: Any = None

    def start(self, suggestions: str = "",
              useful_lemmas: list[str] | None = None) -> None:
        ctx = contextvars.copy_context()
        loop = asyncio.get_running_loop()
        # Track live nesting depth: pushed here, popped at the terminal outcome
        # in process_core (and idempotently in aclose as a safety net).
        self.session.runtime.worker_stack.append(self)
        self._task = loop.create_task(
            self._run(suggestions, useful_lemmas or []), context=ctx)

    def _pop_from_stack(self) -> None:
        stack = self.session.runtime.worker_stack
        if self in stack:
            stack.remove(self)

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

    async def process_core(self) -> 'str | None':
        """Generic event consumer shared by the FINISHING worker and lemma
        sub-agents. Consumes ONE worker event:

        - ``WorkerRefute`` / ``WorkerRequestLemmas`` (non-terminal): store the
          pending future and ``raise ContinuingInteraction`` with the review
          interaction, carrying ``self.continuation`` (the originating
          ``Interaction_ChooseTarget`` for a FINISHING worker, or a
          ``LemmaDrive`` for a lemma sub-agent). The review's ``answer`` is
          responsible for the post-review resume.
        - ``WorkerSurrender`` / ``WorkerDone(success=False)`` (terminal): pop the
          nesting stack, return a planner-facing string.
        - ``WorkerDone(success=True)`` (terminal): pop the stack, return ``None``.

        Does NOT do FINISHING multi-target chaining — that is ``process``'s job.
        ``None`` always means "this worker succeeded" (see M4)."""
        event = await self._wait_next_event()
        match event:
            case WorkerRefute():
                self._pending_review = event.response_future
                complaint = WorkerComplaint(
                    kind="refute", detail=event.detail)
                raise ContinuingInteraction(
                    new_interaction=Interaction_ReviewRefutation(
                        self.target, complaint, self, self.continuation))
            case WorkerRequestLemmas():
                self._pending_lemma_request = event.response_future
                raise ContinuingInteraction(
                    new_interaction=Interaction_ReviewLemmaRequest(
                        self.target, event.detail, event.lemmas, self,
                        self.continuation))
            case WorkerSurrender():
                await self.wait_finish()
                self._pop_from_stack()
                self.session.refresh_YAML()
                return (f"Worker on {self.target.id} surrendered: "
                        f"{event.detail}\n"
                        f"Reconsider the proof plan for this step.")
            case WorkerDone(success=True):
                await self.wait_finish()
                self._pop_from_stack()
                self.session.refresh_YAML()
                return None
            case _:  # WorkerDone(success=False)
                await self.wait_finish()
                self._pop_from_stack()
                self.session.refresh_YAML()
                return (f"Worker on {self.target.id} could not prove the goal. "
                        f"Reconsider the proof plan for this step.")

    async def process(self, choose_target: 'Interaction_ChooseTarget'):
        """FINISHING-stage wrapper over ``process_core``: records the
        continuation and, on worker success (``None``), applies the
        ``Interaction_ChooseTarget`` multi-target chaining
        (``failed_parents.discard`` + re-raise to pick the next target)."""
        self.continuation = choose_target
        result = await self.process_core()
        if result is None:                       # WorkerDone(success=True)
            choose_target.failed_parents.discard(self.target)
            if not choose_target.failed_parents:
                return None
            choose_target.is_first_entry = False
            raise ContinuingInteraction(new_interaction=choose_target)
        return result                            # surrender / failure string

    def resolve_review(self, accepted: bool, reason: str | None = None) -> None:
        fut = self._pending_review
        self._pending_review = None
        if fut is not None and not fut.done():
            fut.set_result((accepted, reason))

    def resolve_lemma_request(self, feedback: str) -> None:
        """Wake a worker blocked in a ``request_lemmas`` complaint, handing it
        the planner's feedback string (mirrors ``resolve_review`` but with a
        plain-string result)."""
        fut = self._pending_lemma_request
        self._pending_lemma_request = None
        if fut is not None and not fut.done():
            fut.set_result(feedback)

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
        for fut in (self._pending_review, self._pending_lemma_request):
            if fut is not None and not fut.done():
                fut.cancel()
        self._pending_review = None
        self._pending_lemma_request = None
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
        self._pop_from_stack()


async def aclose_all(handles: list['WorkerHandle']) -> None:
    """``aclose`` every handle on a nesting stack, deepest-first. Snapshots the
    list (each ``aclose`` mutates ``worker_stack``) and swallows errors so one
    failing teardown can't strand the rest."""
    for h in list(reversed(handles)):
        try:
            await h.aclose()
        except Exception:
            pass


async def _abort_to_planning(planner: 'LMDriver') -> str:
    """proof-failure unwind (plan decision 5): a planner-authored lemma could
    not be proved. Keep ALL nodes (no rollback — decision 4), tear down the
    whole nesting stack, and return a re-plan message that collapses the review
    fork back to ``complete_proof`` (which restores PLANNING). Abandons any other
    in-flight FINISHING targets, exactly like accepting a refutation."""
    await aclose_all(planner.runtime.worker_stack)
    planner.refresh_YAML()
    # DRAFT wording (pending user review — see plan §"User-facing text").
    return ("A helper lemma could not be proved. The relevant Have node(s) have "
            "been kept in place; returning to planning so you can revise the "
            "proof strategy (fix or remove the unproved lemma, or take a "
            "different approach).")


async def _abort_nesting(planner: 'LMDriver') -> str:
    """Nesting backstop (plan decision 7): the live worker stack reached
    WORKER_NESTING_LIMIT. End the whole ``by aoa`` as resource_exhausted — set
    the MAJOR session's terminal quit_info, tear down the stack, interrupt the
    major so its run loop stops promptly, and return (collapsing the fork back to
    ``complete_proof``; the loop then breaks on the terminal quit_info)."""
    major = planner
    while major.parent is not None:
        major = major.parent
    major.quit_info = ResourceExhausted(
        f"lemma-request nesting exceeded depth {WORKER_NESTING_LIMIT}")
    await aclose_all(planner.runtime.worker_stack)
    await major.interrupt()
    # DRAFT wording (pending user review).
    return (f"Lemma-request nesting exceeded the limit of {WORKER_NESTING_LIMIT}; "
            f"aborting the proof.")


async def _resume_worker(handle: 'WorkerHandle'):
    """Resume a worker whose review just resolved its pending future. The resume
    STYLE depends on the worker's continuation:

    - ``Interaction_ChooseTarget`` (a FINISHING worker): drive it via the
      FINISHING wrapper ``process`` so multi-target chaining still applies.
    - ``LemmaDrive`` (a lemma sub-agent): re-drive it to its terminal outcome
      with ``process_core`` (may itself raise ``ContinuingInteraction`` for a
      further nested request), then continue the owning drive's queue via
      ``advance`` (which finalises this worker at its loop top). A non-``None``
      terminal here means the sub-agent could not prove its lemma → abort."""
    cont = handle.continuation
    if isinstance(cont, Interaction_ChooseTarget):
        return await handle.process(cont)
    if isinstance(cont, LemmaDrive):
        result = await handle.process_core()
        if result is not None:
            return await _abort_to_planning(cont.planner)
        return await cont.advance()
    # No continuation recorded — nothing sensible to chain to.
    return None


class LemmaDrive:
    """Drives sequential proving of a batch of planner-authored helper lemmas for
    one requesting worker, surviving nested requests via a re-entrant ``advance``.

    It is the lemma-flow analogue of ``Interaction_ChooseTarget``: the queue and
    bookkeeping live on this object (NOT on an ``answer()`` stack frame, which the
    ``ContinuingInteraction`` trampoline would destroy on a nested request), so
    ``advance`` can be re-entered after a nested excursion and pick up where it
    left off."""

    def __init__(self, planner: 'LMDriver', queue: list,
                 requester: 'WorkerHandle', requester_continuation: Any,
                 feedback: str):
        self.planner = planner
        self.queue = queue                         # list[(have_node, name)] remaining
        self.requester = requester                 # worker to wake when queue empties
        self.requester_continuation = requester_continuation
        self.feedback = feedback
        self.current: 'WorkerHandle | None' = None  # handle proving queue[0], if live

    async def advance(self):
        """Prove the remaining queue one sub-agent at a time, then wake + resume
        the requesting worker. Re-entrant: also the resume point after a nested
        review (see ``_resume_worker``). No planner re-prompt happens between
        lemmas — only an actual nested request re-prompts (for that request)."""
        while True:
            # Finalise a worker just driven to terminal — either by our own
            # process_core below (no-nested case) or by a nested review that
            # re-drove it (_resume_worker). `current is None` on first entry.
            if self.current is not None:
                have_node = self.queue[0][0]
                self.current = None
                if have_node.is_proof_finished():
                    self.queue.pop(0)
                else:
                    return await _abort_to_planning(self.planner)
            if not self.queue:
                break
            # Backstop BEFORE spawning the next sub-agent (before the push that
            # would reach the limit).
            if len(self.planner.runtime.worker_stack) >= WORKER_NESTING_LIMIT:
                return await _abort_nesting(self.planner)
            have_node, _name = self.queue[0]
            sub = WorkerHandle(have_node, self.planner)
            sub.continuation = self
            self.current = sub
            sub.start()
            result = await sub.process_core()   # may raise ContinuingInteraction
            if result is not None:
                # surrender / failure → lemma not proved → terminate (decision 5)
                return await _abort_to_planning(self.planner)
            # result is None → proved; loop top finalises (pops the queue).
        # Queue drained — all requested lemmas proved. Wake the requester with
        # the planner's feedback and resume it.
        self.requester.resolve_lemma_request(self.feedback)
        return await _resume_worker(self.requester)
