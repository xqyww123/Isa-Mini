"""Base class and error types for LLM-backed AoA drivers."""

from __future__ import annotations

import asyncio
from time import time
from typing import Awaitable, Callable, TypeVar

from .model import AoA_Error, Session

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

    Subclasses implement ``_run_main()`` (the agent loop) and optionally
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
            await self._run_with_retry()
        except asyncio.CancelledError:
            self.warn_AoA_opr("Cancelled (Isabelle interrupted)")
            raise

    async def _run_with_retry(self):
        """Outer retry layer: restarts ``_run_main`` on quota exhaustion
        or uncaught transient errors."""
        while True:
            try:
                await self._run_main()
                return
            except _QuotaError:
                self.warn_AoA_opr("Quota exhausted, waiting 20min to retry")
                t0 = time()
                await asyncio.sleep(1200)
                self.total_quota_wait_time += time() - t0
            except _TransientError as e:
                self.warn_AoA_opr(f"Transient API error, retrying in 2s: {e}")
                await asyncio.sleep(2)

    async def _run_main(self):
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
