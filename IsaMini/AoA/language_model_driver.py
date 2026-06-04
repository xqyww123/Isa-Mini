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


# --- Cost accounting (shared by every driver / provider) ---

# Per-model token prices in USD *per token* (= published price-per-1M ÷ 1e6),
# keyed by model name across all providers. Names do not collide between
# providers (``gpt-*``/``o*`` vs ``claude-*`` vs ``gemini-*``), so one table
# serves them all. The optional ``cache_write`` rate applies only to providers
# that bill cache *creation* (Anthropic); when absent, ``compute_cost`` falls
# back to the ``input`` rate. Verified against published pricing 2026-06.
PRICING: dict[str, dict[str, float]] = {
    # OpenAI
    "gpt-5.5-pro":  {"input": 30.00e-6, "cached": 30.00e-6, "output": 180.00e-6},
    "gpt-5.5":      {"input": 5.00e-6,  "cached": 0.50e-6,  "output": 30.00e-6},
    "gpt-5.4":      {"input": 2.50e-6,  "cached": 0.25e-6,  "output": 15.00e-6},
    "gpt-4.1":      {"input": 2.00e-6,  "cached": 0.50e-6,  "output": 8.00e-6},
    "gpt-4.1-mini": {"input": 0.40e-6,  "cached": 0.10e-6,  "output": 1.60e-6},
    "gpt-4.1-nano": {"input": 0.10e-6,  "cached": 0.025e-6, "output": 0.40e-6},
    "o3":           {"input": 2.00e-6,  "cached": 0.50e-6,  "output": 8.00e-6},
    "o4-mini":      {"input": 1.10e-6,  "cached": 0.275e-6, "output": 4.40e-6},
    # Anthropic
    "claude-opus-4-6":   {"input": 5.00e-6, "cache_write": 10.00e-6, "cached": 0.50e-6, "output": 25.00e-6},
    "claude-sonnet-4-6": {"input": 3.00e-6, "cache_write": 3.75e-6,  "cached": 0.30e-6, "output": 15.00e-6},
    # Gemini
    "gemini-2.5-pro":         {"input": 1.25e-6, "cached": 0.3125e-6, "output": 10.00e-6},
    "gemini-2.5-flash":       {"input": 0.15e-6, "cached": 0.0375e-6, "output": 0.60e-6},
    "gemini-3.1-pro-preview": {"input": 2.00e-6, "cached": 0.20e-6,   "output": 12.00e-6},
    "gemini-3-flash-preview": {"input": 0.50e-6, "cached": 0.05e-6,   "output": 3.00e-6},
}


def pricing_for(model: str, default: dict[str, float]) -> dict[str, float]:
    """Per-token price dict for *model*, or *default* (the caller's family
    flagship, e.g. ``PRICING["gpt-4.1"]``) when the model is unknown."""
    return PRICING.get(model, default)


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
            # Single continuous agent loop for every role. The main (planner)
            # agent runs real proofs throughout and delegates hard sub-goals on
            # demand via the `subagent` tool; workers run the same loop scoped to
            # their target. There is no separate FINISHING stage anymore.
            await self._run_agent_loop()
        except asyncio.CancelledError:
            self.warn_AoA_opr("Cancelled (Isabelle interrupted)")
            raise

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

    def _cost_from(self, p: dict[str, float]) -> float:
        """Total USD cost of this session's token usage under price dict *p*.
        Generalises every driver: providers that do not bill cache *creation*
        leave ``total_cache_creation_input_tokens`` at 0 and pass a *p* without
        ``cache_write``, so both the subtraction and the cache-write term vanish."""
        non_cached = max(0, self.total_input_tokens
                         - self.total_cache_read_input_tokens
                         - self.total_cache_creation_input_tokens)
        return (
            non_cached * p["input"]
            + self.total_cache_creation_input_tokens * p.get("cache_write", p["input"])
            + self.total_cache_read_input_tokens * p["cached"]
            + self.total_output_tokens * p["output"]
        )

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

    @classmethod
    def _make_fork(cls, parent: 'LMDriver', role=None) -> 'LMDriver':
        """Create a fork sub-session sharing the parent's state. Concrete
        drivers implement the construction; the worker plumbing in
        ``model.py`` calls this via ``session.__class__._make_fork``."""
        raise NotImplementedError
