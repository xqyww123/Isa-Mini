#!/usr/bin/env python3
"""Standalone unit test for ClaudeCode._accumulate_cost's dollar accounting.

``ResultMessage.total_cost_usd`` is a RUNNING TOTAL within one CLI session
(official SDK docs: "read the latest result rather than summing across
results"); the old ``+=`` double-counted earlier turns whenever one session
emitted several ResultMessages (retry prompts, fork nudges — the incident
session's 8 identical rejections were summed to 8x the true cost). The fix
takes the per-session increment over the highest value seen, keeping
``total_cost_usd`` an accumulator so ``_settle_costs``-style worker merges
survive.

No Isabelle / no REPL. Run directly: ``python test_cost_accumulation.py``.
Exits non-zero on any failure.
"""
import os
import sys
from types import SimpleNamespace

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA.driver_claude_code import ClaudeCode

failures = []


def check(cond, msg):
    if not cond:
        failures.append(msg)
        print(f"FAIL: {msg}")
    else:
        print(f"ok:   {msg}")


def make_driver():
    d = object.__new__(ClaudeCode)
    d._cost_by_session = {}
    d.total_cost_usd = 0.0
    d.cost_lines = []
    d.log_cost = d.cost_lines.append
    d._accumulate_usage = lambda usage: None
    return d


def msg(session_id, total, usage=None):
    return SimpleNamespace(session_id=session_id, total_cost_usd=total,
                           usage=usage)


def approx(a, b):
    return abs(a - b) < 1e-9


def main():
    # Case 1: single-turn session — increment equals the full amount
    # (identical to the old behaviour, which was correct for 99% of runs).
    d = make_driver()
    d._accumulate_cost(msg("s1", 0.30))
    check(approx(d.total_cost_usd, 0.30), "single turn: full amount")

    # Case 2: follow-up turn in the same session — only the delta is added.
    d._accumulate_cost(msg("s1", 0.50))
    check(approx(d.total_cost_usd, 0.50), "second turn: only the increment")

    # Case 3: repeated identical running total (the incident's 8 rejected
    # turns, each 0 marginal tokens) — increment 0.
    d._accumulate_cost(msg("s1", 0.50))
    d._accumulate_cost(msg("s1", 0.50))
    check(approx(d.total_cost_usd, 0.50), "repeated same total: no double count")

    # Case 4: a new session (context restart / fork) starts its own tally
    # from 0 — full first amount added on top.
    d._accumulate_cost(msg("s2", 0.20))
    check(approx(d.total_cost_usd, 0.70), "new session id: fresh tally")

    # Worker settle: total_cost_usd stays an accumulator — an external +=
    # (as _settle_costs does) must survive later messages untouched.
    d.total_cost_usd += 1.00
    d._accumulate_cost(msg("s2", 0.25))
    check(approx(d.total_cost_usd, 1.75), "external worker settle not erased")

    # None cost (CLI omits the field) — no crash, no change.
    d._accumulate_cost(msg("s2", None))
    check(approx(d.total_cost_usd, 1.75), "None total_cost_usd is a no-op")

    # The log line carries the session id for post-hoc auditing.
    check(all(line.startswith("session=") for line in d.cost_lines),
          "log_cost lines carry session=")

    if failures:
        print(f"\n{len(failures)} FAILURE(S)")
        sys.exit(1)
    print("\nall passed")


if __name__ == "__main__":
    main()
