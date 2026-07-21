"""Base class and error types for LLM-backed AoA drivers."""

from __future__ import annotations

import asyncio
import os
from dataclasses import dataclass
from time import time
from typing import Awaitable, Callable, ClassVar, TypeVar, overload

from .model import AoA_Error, Session

_T = TypeVar("_T")


@overload
def env_get(env: 'dict[str, str] | None', name: str, default: str) -> str: ...
@overload
def env_get(env: 'dict[str, str] | None', name: str, default: None = None) -> 'str | None': ...
def env_get(env: 'dict[str, str] | None', name: str, default: 'str | None' = None) -> 'str | None':
    """One driver-config variable: the resolved overlay, else this process's env.

    ``env`` is the per-invocation overlay toplevel builds by resolving the
    driver's ``ENV_VARS`` through the connected Isabelle (Connection.getenv):
    the RPC host is a long-lived daemon whose own os.environ is frozen at
    server start, while the Isabelle process re-sources etc/settings at every
    restart -- so settings edits only reach drivers through this overlay.
    The os.environ fallback keeps connection-less paths (tests, scripts)
    behaving exactly as before.
    """
    v = (env or {}).get(name)
    if v:
        return v
    return os.environ.get(name, default)


class _TransientError(AoA_Error):
    """Transient failure (5xx, connection drop, timeout, 429 rate limit).
    Retried with exponential backoff at the per-call layer."""
    pass


class _QuotaError(AoA_Error):
    """Quota / billing exhausted.  Long wait then retry at the outer layer."""
    pass


# --- Cost accounting (shared by every driver / provider) ---
# Token-accounting standard for this package: docs/COST_ACCOUNTING.md.

# Per-model token prices in USD *per token* (= published price-per-1M ÷ 1e6),
# keyed by model name across all providers. Names do not collide between
# providers (``gpt-*``/``o*`` vs ``claude-*`` vs ``gemini-*``), so one table
# serves them all. ``cached`` is the cache-READ rate; the optional ``cache_write``
# rate applies only to providers that bill cache *creation* (Anthropic) — when
# absent, ``_compute_cost`` falls back to the ``input`` rate. For Claude the cache
# convention is the 5-min ephemeral TTL: cache_write = 1.25× input, cache read =
# 0.1× input. Verified against published pricing 2026-06.
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
    # Anthropic (cache_write = 5-min TTL = 1.25× input; cached = 0.1× input)
    "claude-opus-4-6":   {"input": 5.00e-6,  "cache_write": 6.25e-6,  "cached": 0.50e-6, "output": 25.00e-6},
    "claude-opus-4-5":   {"input": 15.00e-6, "cache_write": 18.75e-6, "cached": 1.50e-6, "output": 75.00e-6},
    "claude-sonnet-4-6": {"input": 3.00e-6,  "cache_write": 3.75e-6,  "cached": 0.30e-6, "output": 15.00e-6},
    "claude-sonnet-4-5": {"input": 3.00e-6,  "cache_write": 3.75e-6,  "cached": 0.30e-6, "output": 15.00e-6},
    # Gemini
    "gemini-2.5-pro":         {"input": 1.25e-6, "cached": 0.3125e-6, "output": 10.00e-6},
    "gemini-2.5-flash":       {"input": 0.15e-6, "cached": 0.0375e-6, "output": 0.60e-6},
    "gemini-3.1-pro-preview": {"input": 2.00e-6, "cached": 0.20e-6,   "output": 12.00e-6},
    "gemini-3-flash-preview": {"input": 0.50e-6, "cached": 0.05e-6,   "output": 3.00e-6},
    # DeepSeek V4 — official api.deepseek.com rates (per api-docs.deepseek.com
    # /quick_start/pricing, fetched 2026-06-06). "input" = cache-miss,
    # "cached" = cache-hit; thinking-mode output is billed at the output rate.
    # NOTE: only the official bare model ids match — proxy ids like
    # "deepseek/deepseek-v4-flash" (openai-next) bill differently and fall back.
    # (A third-party promo claim of $1.74/$3.48 standard for v4-pro is NOT on the
    # official page, which still lists the rates below; revisit if that changes.)
    "deepseek-v4-flash": {"input": 0.14e-6,  "cached": 0.0028e-6,   "output": 0.28e-6},
    "deepseek-v4-pro":   {"input": 0.435e-6, "cached": 0.003625e-6, "output": 0.87e-6},
}


def pricing_for(model: str, default: dict[str, float]) -> dict[str, float]:
    """Per-token price dict for *model*, or *default* (the caller's family
    flagship, e.g. ``PRICING["gpt-4.1"]``) when the model is unknown."""
    return PRICING.get(model, default)


def _parse_effort_suffix(argument: str | None, default_model: str,
                         default_effort: str = "medium",
                         ) -> tuple[str, str]:
    """Parse ``"model-effort"`` into ``(model, effort)``.

    Recognised suffixes: ``-low``, ``-medium``, ``-high``, ``-xhigh``, ``-max``.
    *default_effort* is returned when no suffix is present.
    """
    raw = argument or default_model
    for suffix in ("-xhigh", "-medium", "-high", "-low", "-max"):
        if raw.endswith(suffix):
            return raw[: -len(suffix)], suffix[1:]
    return raw, default_effort


@dataclass
class Usage:
    """Canonical per-call token usage (see docs/COST_ACCOUNTING.md).

    INVARIANT: ``input_tokens`` is UNCACHED-only. Cache reads/writes are the
    separate, mutually-exclusive ``cached_tokens`` / ``cache_creation_tokens``
    partitions, so ``total_prompt = input + cached + cache_creation``. Always
    build via the factories below — they encode each provider's convention so
    the invariant holds by construction rather than by remembering to subtract.
    """
    input_tokens: int
    output_tokens: int
    cached_tokens: int
    cache_creation_tokens: int = 0

    @classmethod
    def from_uncached(cls, input_tokens: int, output_tokens: int,
                      cache_read: int, cache_creation: int = 0) -> 'Usage':
        """Provider whose reported input ALREADY excludes cache (Anthropic /
        Claude Code) — pass straight through."""
        return cls(input_tokens, output_tokens, cache_read, cache_creation)

    @classmethod
    def from_inclusive(cls, prompt_tokens: int, output_tokens: int,
                       cached: int, cache_creation: int = 0) -> 'Usage':
        """Provider whose reported prompt count INCLUDES cache (OpenAI / Gemini /
        Codex) — subtract the cache share once to recover uncached input."""
        return cls(max(0, prompt_tokens - cached - cache_creation),
                   output_tokens, cached, cache_creation)


class LMDriver(Session):
    """Session subclass that adds unified retry logic for LLM drivers.

    Subclasses implement ``_run_agent_loop()`` (the agent loop) and optionally
    ``_run_fork()`` (for fork interactions).
    """

    # Environment variables this driver's configuration comes from (keys,
    # endpoints, model overrides). toplevel resolves each through the connected
    # Isabelle (Connection.getenv) before construction and passes the result as
    # the ``env`` overlay, so a user's etc/settings edit takes effect on the
    # next `by aoa` after an Isabelle restart -- no RPC-host restart needed.
    # Constructors read these ONLY via ``env_get(env, ...)``, never a bare
    # os.environ lookup.
    ENV_VARS: ClassVar[tuple[str, ...]] = ()

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
            except _QuotaError as e:
                self.warn_AoA_opr("Quota exhausted, waiting 20min to retry"
                                  + (f" ({e})" if str(e) else ""), to_isabelle=True)
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

    def _pricing(self) -> dict[str, float]:
        """Price dict for this driver's model. Each concrete driver supplies it —
        a provider lookup (``self._provider.pricing()``) or
        ``pricing_for(self._model, <family default>)``."""
        raise NotImplementedError

    def _compute_cost(self) -> None:
        """Recompute ``total_cost_usd`` from the canonical token partition and the
        driver's pricing (see docs/COST_ACCOUNTING.md). Partition sum with NO
        subtraction — ``total_input_tokens`` is already uncached. ``cache_write``
        falls back to the input rate for providers that don't bill cache creation."""
        p = self._pricing()
        self.total_cost_usd = (
            self.total_input_tokens * p["input"]
            + self.total_cache_creation_input_tokens * p.get("cache_write", p["input"])
            + self.total_cache_read_input_tokens * p["cached"]
            + self.total_output_tokens * p["output"]
        )

    def _accumulate_usage(self, usage: Usage) -> None:
        """Add one call's canonical ``Usage`` into the running token totals (and log
        it). Touches ONLY the token counters — never ``total_cost_usd`` — so it is
        safe alongside drivers that take a remote-reported cost (e.g. Claude Code)."""
        self.total_input_tokens += usage.input_tokens
        self.total_output_tokens += usage.output_tokens
        self.total_cache_read_input_tokens += usage.cached_tokens
        self.total_cache_creation_input_tokens += usage.cache_creation_tokens
        self._log_meta("USAGE",
                       input_tokens=usage.input_tokens,
                       output_tokens=usage.output_tokens,
                       cached_tokens=usage.cached_tokens,
                       cache_creation_tokens=usage.cache_creation_tokens)

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
