#!/usr/bin/env python3
"""Property test for `helper.local_step_between` — the fractional-id primitive
that mints a new local-step strictly between two adjacent siblings.

This is a PURE unit test (no Isabelle / no REPL): run it directly with
`python test_local_step_between.py`; it exits non-zero on any failure.

It pins two invariants that the live model relies on:

  1. BYTE-COMPATIBILITY (golden stability): wherever the historical inline
     formula already produced a strictly-between id, `local_step_between` returns
     the IDENTICAL id. This is what guarantees the fractional-id fix moves zero
     goldens. It also guards the fast-path branch inside `local_step_between`
     against a future "this looks redundant" deletion — delete it and this test
     fails loudly (and goldens would have moved).

  2. CORRECTNESS: `local_step_between` is ALWAYS strictly between its arguments
     (the historical formula was not — it collided, returning `before` itself,
     when `before` had no fractional gap above its predecessor, e.g.
     prev=`0A`, before=`0A1` -> `0A1`). The sole exception is the degenerate
     `before == prev + [0,...,0]` (no key exists), which the id scheme never
     generates and which the primitive handles without raising.
"""
import sys
from helper import (split_id_into_segs, cat_segs_into_id, local_step_between)


def historical(prev_segs, before_segs):
    """The exact pre-fix inline arithmetic from `_insert_before_child` /
    `_auto_Intro_after_child` (the 'has predecessor' branch)."""
    if len(prev_segs) > len(before_segs):
        segs = prev_segs[:len(before_segs) + 1]
        segs[-1] += 1
        return segs
    return prev_segs + [1]


def enum_segment_lists(max_len, vals):
    out, frontier = [], [[]]
    for _ in range(max_len):
        frontier = [base + [v] for base in frontier for v in vals]
        out += frontier
    return out


def is_zero_tail(prev, before):
    """before == prev + [0,...,0]: structurally no id exists strictly between
    (unreachable — the id scheme never emits a zero-tailed id)."""
    return (before[:len(prev)] == prev
            and len(before) > len(prev)
            and all(v == 0 for v in before[len(prev):]))


def main():
    domains = [
        ("vals 0..3, len<=5", enum_segment_lists(5, [0, 1, 2, 3])),
        ("vals incl multi-digit, len<=4", enum_segment_lists(4, [0, 1, 2, 9, 10, 11])),
    ]
    n_pairs = n_bytediff = n_invalid = n_rt = n_collide = 0
    fails = []
    for label, lists in domains:
        for prev in lists:
            for before in lists:
                if not (prev < before):
                    continue
                n_pairs += 1
                got = local_step_between(cat_segs_into_id(prev),
                                         cat_segs_into_id(before))
                got_segs = split_id_into_segs(got)

                # roundtrip
                if cat_segs_into_id(got_segs) != got:
                    n_rt += 1
                    if len(fails) < 10:
                        fails.append(("roundtrip", prev, before, got))

                # byte-compat where the historical formula was already valid
                cand = historical(list(prev), list(before))
                if prev < cand < before:
                    if cat_segs_into_id(cand) != got:
                        n_bytediff += 1
                        if len(fails) < 10:
                            fails.append(("byte-diff", prev, before,
                                          cat_segs_into_id(cand), got))

                # always strictly between (except the unreachable zero-tail case)
                if not (prev < got_segs < before):
                    if not is_zero_tail(prev, before):
                        n_invalid += 1
                        if len(fails) < 10:
                            fails.append(("not-between", prev, before, got))

                # never collide with either endpoint
                if got_segs == prev or got_segs == before:
                    if not is_zero_tail(prev, before):
                        n_collide += 1
                        if len(fails) < 10:
                            fails.append(("collision", prev, before, got))
        print(f"  [{label}] checked pairs so far: {n_pairs}")

    # the exact production collision must now be resolved
    prod = local_step_between("0A", "0A1")
    prod_ok = prod != "0A1" and split_id_into_segs("0A") < split_id_into_segs(prod) < split_id_into_segs("0A1")

    print(f"pairs={n_pairs}  byte-diff(fast-path drift)={n_bytediff}  "
          f"not-strictly-between={n_invalid}  collisions={n_collide}  roundtrip-fail={n_rt}")
    print(f"production case  local_step_between('0A','0A1') = {prod!r}  (fixed: {prod_ok})")
    for f in fails:
        print("  FAIL:", f)

    ok = (n_bytediff == 0 and n_invalid == 0 and n_collide == 0
          and n_rt == 0 and prod_ok)
    print("RESULT:", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
