#!/usr/bin/env python3
"""Standalone unit tests for the budget-exempt span mechanism
(``Runtime.budget_exempt`` / ``Runtime.elapsed_working_time``): overlapping
spans record their union, nested spans count once, the clock freezes while a
span is open, the depth returns to zero after exceptions and cancellation,
and the accessor's ``float | None`` contract holds.

No Isabelle / no REPL / no LLM. Run directly:
``python test_budget_exempt.py``. Exits non-zero on any failure.
"""
import asyncio
import os
import sys
from time import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA.model import Runtime

TOL = 0.04


def check(cond, msg):
    if not cond:
        print(f"FAIL: {msg}")
        sys.exit(1)


def started_runtime():
    rt = Runtime()
    rt._budget_start_time = time()
    return rt


def test_none_before_the_clock_starts():
    rt = Runtime()
    check(rt.elapsed_working_time() is None,
          "elapsed_working_time must be None before the budget clock starts")
    with rt.budget_exempt():
        pass
    check(rt.elapsed_working_time() is None,
          "an exempt span before the clock starts must not invent a clock")


async def test_overlapping_spans_record_their_union():
    rt = started_runtime()

    async def hold(delay_before, span_len):
        await asyncio.sleep(delay_before)
        with rt.budget_exempt():
            await asyncio.sleep(span_len)

    # Span A [0, 0.10], span B [0.05, 0.15]: union = 0.15, sum = 0.20.
    await asyncio.gather(hold(0.0, 0.10), hold(0.05, 0.10))
    check(abs(rt._total_exempt_time - 0.15) < TOL,
          f"overlap must record the UNION (~0.15s), got {rt._total_exempt_time:.3f}")
    check(rt._exempt_depth == 0, "depth must return to 0")


def test_nested_spans_count_once():
    rt = started_runtime()
    import time as _t
    with rt.budget_exempt():
        with rt.budget_exempt():
            _t.sleep(0.06)
    check(abs(rt._total_exempt_time - 0.06) < TOL,
          f"nesting must count once (~0.06s), got {rt._total_exempt_time:.3f}")
    check(rt._exempt_depth == 0, "depth must return to 0 after nesting")


async def test_open_span_freezes_the_clock():
    rt = started_runtime()
    with rt.budget_exempt():
        before = rt.elapsed_working_time()
        await asyncio.sleep(0.08)
        after = rt.elapsed_working_time()
    check(before is not None and after is not None
          and abs(after - before) < TOL,
          f"the clock must be frozen inside an open span "
          f"(moved {after - before:.3f}s)")
    check(rt._budget_start_time is not None
          and abs(time() - rt._budget_start_time
                  - (rt.elapsed_working_time() + rt._total_exempt_time)) < TOL,
          "start stamp is immutable; exemption lives in the accumulator")


def test_depth_zero_after_exception():
    rt = started_runtime()
    try:
        with rt.budget_exempt():
            raise RuntimeError("boom")
    except RuntimeError:
        pass
    check(rt._exempt_depth == 0 and rt._exempt_t0 is None,
          "depth must be 0 and no span open after an exception")


async def test_depth_zero_after_cancellation():
    rt = started_runtime()

    async def waiter():
        with rt.budget_exempt():
            await asyncio.sleep(30)

    task = asyncio.get_running_loop().create_task(waiter())
    await asyncio.sleep(0.05)
    task.cancel()
    try:
        await task
    except asyncio.CancelledError:
        pass
    check(rt._exempt_depth == 0 and rt._exempt_t0 is None,
          "depth must be 0 after CancelledError out of the inner await "
          "(else the clock freezes forever)")
    check(rt._total_exempt_time > 0.0,
          "the partial wait before cancellation still counts as exempt")


def main():
    test_none_before_the_clock_starts()
    asyncio.run(test_overlapping_spans_record_their_union())
    test_nested_spans_count_once()
    asyncio.run(test_open_span_freezes_the_clock())
    test_depth_zero_after_exception()
    asyncio.run(test_depth_zero_after_cancellation())
    print("OK — all budget-exempt tests passed")


if __name__ == "__main__":
    main()
