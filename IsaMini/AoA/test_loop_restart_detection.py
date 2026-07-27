#!/usr/bin/env python3
"""Standalone unit test for the runaway-loop guard's pure decision logic:
``Session._note_repeat`` and ``ToolExecutor._should_loop_restart``.

No Isabelle / no REPL. Run directly from anywhere (it puts the package root on
``sys.path``):  ``python test_loop_restart_detection.py``. Exits non-zero on any
failure.

Covers:
  - N-1 identical calls do NOT fire; the Nth does; the counter resets after.
  - A different call (args or tool name) restarts the run at 1.
  - Gating disables detection entirely (no fire, no counting): non-major
    session, a pending ``quit_info``, a parked non-forking interaction
    (``_nf_pending_interaction``), and a suspended executor task
    (``_suspended_task``).
  - The raw ``_note_repeat`` counter fires exactly at the threshold.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA.model import Session, LOOP_REPEAT_THRESHOLD, Restart
from IsaMini.AoA.mcp_http_server import ToolExecutor

N = LOOP_REPEAT_THRESHOLD


def make_session(*, is_major=True, nf=None, quit_info=None):
    """A bare Session with only the fields the guard reads (bypasses __init__)."""
    s = Session.__new__(Session)
    # is_major := parent is None; a non-major session just needs some parent.
    s.parent = None if is_major else Session.__new__(Session)
    s._nf_pending_interaction = nf
    s.quit_info = quit_info
    s._repeat_sig = None
    s._repeat_count = 0
    return s


def make_executor(session, *, suspended=None):
    ex = ToolExecutor.__new__(ToolExecutor)
    ex._session = session
    ex._suspended_task = suspended
    return ex


def check(cond, msg):
    if not cond:
        print(f"FAIL: {msg}")
        sys.exit(1)


def test_basic_fire_and_reset():
    s = make_session()
    ex = make_executor(s)
    args = {"queries": [{"term_patterns": ["x"]}]}
    for i in range(N - 1):
        check(not ex._should_loop_restart(s, "query", args),
              f"call {i + 1} must not fire")
    check(ex._should_loop_restart(s, "query", args), f"call {N} must fire")
    check(s._repeat_count == 0 and s._repeat_sig is None,
          "counter must reset after firing")
    # a fresh run must take another full N
    for i in range(N - 1):
        check(not ex._should_loop_restart(s, "query", args),
              f"post-reset call {i + 1} must not fire")
    check(ex._should_loop_restart(s, "query", args),
          "post-reset Nth must fire")


def test_different_call_resets():
    s = make_session()
    ex = make_executor(s)
    a = {"q": 1}
    b = {"q": 2}
    for _ in range(N - 1):
        ex._should_loop_restart(s, "query", a)
    check(s._repeat_count == N - 1, "count accumulated")
    check(not ex._should_loop_restart(s, "query", b),
          "different args must not fire")
    check(s._repeat_count == 1, "different args reset to 1")
    for _ in range(N - 1):
        ex._should_loop_restart(s, "query", a)
    check(not ex._should_loop_restart(s, "edit", a),
          "different tool must not fire")
    check(s._repeat_count == 1, "different tool reset to 1")


def test_gating_disables():
    args = {"q": 1}
    cases = []
    s1 = make_session(is_major=False)
    cases.append(("non-major", s1, make_executor(s1)))
    # A real QuitInfo, not a bare object(): assigning quit_info goes through a
    # property whose setter reads `.is_terminal`. Restart is non-terminal, so
    # the setter short-circuits there; the guard under test only asks whether
    # quit_info is not None.
    s2 = make_session(quit_info=Restart())
    cases.append(("quit pending", s2, make_executor(s2)))
    s3 = make_session(nf=object())
    cases.append(("nf parked", s3, make_executor(s3)))
    for label, s, ex in cases:
        for _ in range(N + 2):
            check(not ex._should_loop_restart(s, "query", args),
                  f"{label}: must never fire")
        check(s._repeat_count == 0, f"{label}: must not even count")
    # suspended executor task
    s4 = make_session()
    ex4 = make_executor(s4, suspended=object())
    for _ in range(N + 2):
        check(not ex4._should_loop_restart(s4, "query", args),
              "suspended: must never fire")
    check(s4._repeat_count == 0, "suspended: must not count")


def test_note_repeat_direct():
    s = make_session()
    for i in range(N - 1):
        check(not s._note_repeat("sig-A"), f"_note_repeat call {i + 1}")
    check(s._note_repeat("sig-A"), "_note_repeat Nth fires")
    check(s._repeat_count == 0, "reset after fire")


def main():
    test_basic_fire_and_reset()
    test_different_call_resets()
    test_gating_disables()
    test_note_repeat_direct()
    print(f"OK — all loop-restart detection tests passed (threshold={N})")


if __name__ == "__main__":
    main()
