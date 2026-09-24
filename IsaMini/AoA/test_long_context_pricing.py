#!/usr/bin/env python3
"""Standalone unit test for the OpenAI API driver's two-tier (short / long
context) cost accounting, the OpenAI rows of ``PRICING`` and the Responses
usage ingestion (cached and cache-written tokens).

``APIDriver_OpenAI`` bills each call at the short or the long rates by the
rule in docs/COST_ACCOUNTING.md §4 (strict ``>`` on ``prompt_tokens`` against
the model's ``long.threshold``): it keeps two disjoint ``Usage`` tallies, adds
each call to exactly one of them, and ``_compute_cost`` bills each tally at its
tier. Drivers that report per-turn sums (Codex CLI, Claude Code) stay on the
flat formula and never see a tier. The AOA_ASSUME_PERFECT_CACHE rewrite must
change only how a prompt is split, never its size.

No Isabelle / no REPL / no LLM / no network. Run directly:
``python test_long_context_pricing.py``. Exits non-zero on any failure.
"""
import os
import shutil
import sys
import tempfile
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


def capture(d):
    """Replace the driver's meta log with an in-memory list."""
    d.meta = []
    d._log_meta = lambda event, **kw: d.meta.append((event, kw))
    return d


def make_driver(model):
    """A real Codex-API driver through the real constructor chain (Session ->
    LMDriver -> APIDriver -> APIDriver_OpenAI -> APIDriver_OpenAICodex); only
    the provider is a stub and the meta log is captured."""
    return capture(APIDriver_OpenAICodex(None, "", provider=_StubProvider(model)))


def flat(d):
    """What LMDriver's own single-tier ``_compute_cost`` would bill for the
    four Session totals (run on the driver, then restored)."""
    saved = d.total_cost_usd
    LMDriver._compute_cost(d)
    cost = d.total_cost_usd
    d.total_cost_usd = saved
    return cost


def totals(d):
    return Usage(input_tokens=d.total_input_tokens,
                 output_tokens=d.total_output_tokens,
                 cached_tokens=d.total_cache_read_input_tokens,
                 cache_creation_tokens=d.total_cache_creation_input_tokens)


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
    check(d.short_context_usage + d.long_context_usage == totals(d),
          "the two tallies sum to the four Session totals (the exported fields)")
    before = d.total_cost_usd
    d._compute_cost()
    check(approx(d.total_cost_usd, before), "_compute_cost is an assignment: recomputing changes nothing")

    # --- the boundary: exactly 272K is short, one more token is long
    for prompt, is_long in ((272_000, False), (272_001, True)):
        d2 = make_driver("gpt-5.6-sol")
        d2._accumulate_usage(Usage(prompt - 200, 10, 100, 100))   # all three prompt terms
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

    # --- a per-turn driver (Codex CLI, default model gpt-5.5-high): a turn whose
    #     summed prompt is 300K is billed at the flat short rates ($1.50), not
    #     at the long rates ($2.955) -- its Usage is a sum over many requests
    from IsaMini.AoA.driver_codex import Codex_Driver
    old_home = os.environ.get("CODEX_HOME")
    with tempfile.TemporaryDirectory() as home:
        open(os.path.join(home, "auth.json"), "w").close()
        os.environ["CODEX_HOME"] = home
        try:
            c = capture(Codex_Driver(None, ""))
        finally:
            if old_home is None:
                os.environ.pop("CODEX_HOME", None)
            else:
                os.environ["CODEX_HOME"] = old_home
    try:
        c._record_codex_usage({"input_tokens": 300_000, "cached_input_tokens": 20_000, "output_tokens": 3_000})
        c._compute_cost()
        check(approx(c.total_cost_usd, Usage(280_000, 3_000, 20_000).cost(PRICING["gpt-5.5"])),
              "Codex CLI: a 300K-prompt turn on gpt-5.5 is billed at the flat short rates")
    finally:
        shutil.rmtree(c.working_dir, ignore_errors=True)
        shutil.rmtree(c._codex_home_dir, ignore_errors=True)

    # --- the AOA_ASSUME_PERFECT_CACHE rewrite never changes a call's prompt size,
    #     now that reported cache writes can be non-zero (a full-rewrite miss)
    d5 = make_driver("gpt-5.6-luna")
    d5._assume_perfect_cache = True
    sizes = set()
    for _ in range(300):   # the model is random by design: exercise every branch
        adj, prompt_total = d5._cache_assumed_usage(Usage(0, 1_000, 0, 200_000), 195_000, 2_000)
        sizes.add((adj.prompt_tokens, prompt_total))
    check(sizes == {(200_000, 200_000)}, "a 200K full-rewrite call keeps prompt_tokens = 200,000 on every random branch")
    adj, _ = d5._cache_assumed_usage(Usage(0, 1_000, 0, 100_000), 95_000, 2_000)
    check(adj.prompt_tokens == 100_000 and adj.cached_tokens + adj.cache_creation_tokens <= 100_000,
          "a 100K full-rewrite miss after a 95K prompt stays 100K and is split, not doubled")
    d5._accumulate_usage(adj)
    check(d5.long_context_usage == Usage(), "and it stays short context")

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
