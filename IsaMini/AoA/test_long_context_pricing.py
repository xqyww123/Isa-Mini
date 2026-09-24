#!/usr/bin/env python3
"""Standalone unit test for the OpenAI API driver's two-tier (short / long
context) cost accounting, the OpenAI rows of ``PRICING`` and the Responses
usage ingestion (cached and cache-written tokens).

OpenAI bills a request whose prompt exceeds the model's long-context threshold
(272K input tokens: input + cached + cache write) at the long rates for the
whole request. ``APIDriver_OpenAI`` keeps two disjoint ``Usage`` tallies and
adds each call to exactly one of them; ``_compute_cost`` bills each tally at
its tier. Drivers that report per-turn sums (Codex CLI, Claude Code) stay on
the flat formula and never see a tier.

No Isabelle / no REPL / no LLM / no network. Run directly:
``python test_long_context_pricing.py``. Exits non-zero on any failure.
"""
import os
import sys
from types import SimpleNamespace

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA.language_model_driver import (
    LMDriver, PRICING, OPENAI_LONG_CONTEXT_THRESHOLD, Usage)
from IsaMini.AoA.driver_openai_api import APIDriver_OpenAICodex, _responses_usage

failures = []


def check(cond, msg):
    if not cond:
        failures.append(msg)
        print(f"FAIL: {msg}")
    else:
        print(f"ok:   {msg}")


def approx(a, b):
    return abs(a - b) < 1e-12


class _StubProvider:
    """The provider surface the driver touches without a network: pricing and
    the Layer-2 log hook APIDriver.__init__ installs."""
    def __init__(self, model):
        self.model_name = model
        self._reasoning_effort = None
        self._log = None

    def pricing(self):
        return PRICING[self.model_name]


def make_driver(model):
    """A real Codex-API driver through the real constructor chain (Session ->
    LMDriver -> APIDriver -> APIDriver_OpenAI -> APIDriver_OpenAICodex); only
    the provider is a stub and the meta log is captured."""
    d = APIDriver_OpenAICodex(None, "", provider=_StubProvider(model))
    d.meta = []
    d._log_meta = lambda event, **kw: d.meta.append((event, kw))
    return d


def flat(d):
    """The single-tier formula over the four Session totals (LMDriver's own)."""
    return Usage(d.total_input_tokens, d.total_output_tokens,
                 d.total_cache_read_input_tokens,
                 d.total_cache_creation_input_tokens).cost(d._pricing())


def main():
    # --- the OpenAI rows: every tiered row is 2x / 2x / 2x / 1.5x its base row
    #     with the same rate keys, at the shared threshold
    tiered = [m for m, p in PRICING.items() if "long" in p]
    check(len(tiered) >= 9, f"{len(tiered)} tiered rows")
    for m in tiered:
        p = PRICING[m]; l = p["long"]
        check(set(l) - {"threshold"} == set(p) - {"long"}, f"{m}: long tier has exactly the base rate keys")
        check(l["threshold"] == OPENAI_LONG_CONTEXT_THRESHOLD == 272_000, f"{m}: threshold 272K")
        ratios = {k: (2.0 if k != "output" else 1.5) for k in l if k != "threshold"}
        check(all(approx(l[k], p[k] * r) for k, r in ratios.items()), f"{m}: long = 2x input/cached/cache_write, 1.5x output")
    # spot-check the two families' luna rows verbatim against the page (per 1M)
    check((PRICING["gpt-5.6-luna"]["input"], PRICING["gpt-5.6-luna"]["cached"], PRICING["gpt-5.6-luna"]["cache_write"], PRICING["gpt-5.6-luna"]["output"]) == (0.20e-6, 0.02e-6, 0.25e-6, 1.20e-6), "gpt-5.6-luna: $0.20 / $0.02 / $0.25 / $1.20")
    check((PRICING["gpt-6-luna"]["input"], PRICING["gpt-6-luna"]["cached"], PRICING["gpt-6-luna"]["cache_write"], PRICING["gpt-6-luna"]["output"]) == (0.10e-6, 0.01e-6, 0.125e-6, 0.50e-6), "gpt-6-luna: $0.10 / $0.01 / $0.125 / $0.50")

    # --- Usage helpers
    u = Usage(10, 40, 30, 20)
    check(u.prompt_tokens == 60, "prompt_tokens = input + cached + cache_creation")
    check(u + Usage(1, 2, 3, 4) == Usage(11, 42, 33, 24), "Usage addition is field-wise")
    check(approx(u.cost(PRICING["gpt-6-luna"]), 10 * 0.10e-6 + 20 * 0.125e-6 + 30 * 0.01e-6 + 40 * 0.50e-6), "Usage.cost partition sum")
    check(approx(Usage(0, 0, 0, 7).cost(PRICING["gpt-5.5"]), 7 * 5.00e-6), "cache_write falls back to the input rate when a row has none")

    # --- short-context calls only: identical to the flat formula
    d = make_driver("gpt-5.6-luna")
    d._accumulate_usage(Usage(6_000, 300, 0))
    d._accumulate_usage(Usage(1_000, 200, 5_760))
    d._compute_cost()
    check(approx(d.total_cost_usd, flat(d)), "two short calls: two-tier cost equals the flat formula")
    check(d.long_context_usage == Usage() and d.meta[-1][1]["long_context"] is False,
          "short calls leave the long tally empty and log long_context=False")

    # --- one long call among short ones: only ITS tokens are billed at long rates
    long_call = Usage(250_000, 4_000, 30_000, 1_000)
    d._accumulate_usage(long_call)
    d._compute_cost()
    p = PRICING["gpt-5.6-luna"]
    check(approx(d.total_cost_usd, d.short_context_usage.cost(p) + long_call.cost(p["long"])), "a 281K-prompt call is billed at the long rates, the rest stays short")
    check(d.meta[-1][1]["long_context"] is True, "the long call is logged long_context=True")
    check(d.short_context_usage + d.long_context_usage == Usage(d.total_input_tokens, d.total_output_tokens, d.total_cache_read_input_tokens, d.total_cache_creation_input_tokens),
          "the two tallies sum to the four Session totals (the exported fields)")
    before = d.total_cost_usd
    d._compute_cost()
    check(approx(d.total_cost_usd, before), "_compute_cost is an assignment: recomputing changes nothing")

    # --- the boundary: exactly 272K is short, one more token is long
    for prompt, is_long in ((272_000, False), (272_001, True)):
        d2 = make_driver("gpt-5.6-sol")
        d2._accumulate_usage(Usage(prompt - 100, 10, 100))
        check((d2.long_context_usage != Usage()) is is_long and d2.meta[-1][1]["long_context"] is is_long,
              f"prompt of {prompt:,} tokens is {'long' if is_long else 'short'} context")

    # --- a model without a long tier: never long, billed flat whatever the size
    d3 = make_driver("gpt-4.1")
    d3._accumulate_usage(Usage(300_000, 1_000, 0))
    d3._compute_cost()
    check(d3.long_context_usage == Usage() and d3.meta[-1][1]["long_context"] is False and approx(d3.total_cost_usd, flat(d3)),
          "gpt-4.1 (no long tier): a 300K call stays short and is billed at the flat rate")

    # --- worker merge: the tallies travel with the totals, so a recompute agrees
    parent = make_driver("gpt-5.6-luna")
    worker = make_driver("gpt-5.6-luna")
    worker._accumulate_usage(Usage(300_000, 2_000, 20_000, 5_000))
    worker._compute_cost()
    parent._accumulate_usage(Usage(1_000, 100, 0))
    parent._compute_cost()
    parent._accumulate_subagent_costs(worker)
    merged_cost = parent.total_cost_usd
    parent._compute_cost()
    check(approx(parent.total_cost_usd, merged_cost), "after merging a worker, recomputing the parent reproduces the merged cost")
    check(approx(parent.total_cost_usd, Usage(1_000, 100, 0).cost(p) + Usage(300_000, 2_000, 20_000, 5_000).cost(p["long"])), "and it bills the worker's long call at the long rates")

    # --- a per-turn driver (Codex CLI) has no tiers: its 300K turn is billed flat
    from IsaMini.AoA.driver_codex import Codex_Driver
    check(Codex_Driver._accumulate_usage is LMDriver._accumulate_usage and Codex_Driver._compute_cost is LMDriver._compute_cost,
          "Codex CLI driver keeps LMDriver's flat accounting")

    # --- Responses usage ingestion: cached and cache-written tokens leave `input`
    details = SimpleNamespace(cached_tokens=40, cache_write_tokens=12)
    um = SimpleNamespace(input_tokens=100, output_tokens=5, input_tokens_details=details)
    check(_responses_usage(um) == Usage(48, 5, 40, 12), "cache_write_tokens -> cache_creation, subtracted from the inclusive input")
    check(_responses_usage(SimpleNamespace(input_tokens=100, output_tokens=5, input_tokens_details=SimpleNamespace(cached_tokens=40))) == Usage(60, 5, 40, 0),
          "a backend without cache_write_tokens ingests as before")
    check(_responses_usage(None) == Usage(), "a response without usage ingests as zero")

    if failures:
        print(f"\n{len(failures)} failure(s)")
        sys.exit(1)
    print("\nall checks passed")


if __name__ == "__main__":
    main()
