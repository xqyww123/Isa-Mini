#!/usr/bin/env python3
"""Standalone unit test for the lone-surrogate corruption gate at the tool
dispatch chokepoint: ``_find_lone_surrogate`` and the rejection at the top of
``ToolExecutor.execute``.

Background: a Claude Code CLI streaming bug can halve a non-BMP character in
tool-call input, leaving a lone UTF-16 surrogate that passes JSON-Schema's
``"type": "string"``. The gate keeps it out of the proof tree (a corrupted
Statement would poison proof.yaml on every later render); recovery is the
driver's _CorruptedHistoryError branch, not this gate's job.

No Isabelle / no REPL. Run directly:
``python test_lone_surrogate_rejection.py``. Exits non-zero on any failure.
"""
import asyncio
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA.mcp_http_server import ToolExecutor, _find_lone_surrogate

# 𝗏 = U+1D5CF (surrogate pair D835/DDCF); the incident kept only the high half.
PAIRED = "args := φarg.dest \U0001D5CF0"
LONE_HIGH = "args := φarg.dest \ud835≿0"
LONE_LOW = "tail \uddcf alone"

failures = []


def check(cond, msg):
    if not cond:
        failures.append(msg)
        print(f"FAIL: {msg}")
    else:
        print(f"ok:   {msg}")


def test_find_lone_surrogate():
    check(_find_lone_surrogate({"thought": PAIRED}) is None,
          "paired surrogates merged into a real non-BMP char -> None")
    check(_find_lone_surrogate({"a": 1, "b": [True, None, 2.5]}) is None,
          "non-string leaves -> None")

    hit = _find_lone_surrogate({"thought": LONE_HIGH})
    check(hit is not None and hit[0] == ".thought" and hit[1] == LONE_HIGH,
          "lone high surrogate found at .thought")

    hit = _find_lone_surrogate(
        {"proof_operations": [{"operation": "Have",
                               "statement": {"english": LONE_LOW}}]})
    check(hit is not None
          and hit[0] == ".proof_operations[0].statement.english",
          "lone low surrogate found at nested path")

    hit = _find_lone_surrogate({LONE_HIGH: "clean"})
    check(hit is not None and hit[0].endswith("(key)"),
          "corrupted dict KEY is caught too")

    check(_find_lone_surrogate(LONE_HIGH) == ("$", LONE_HIGH),
          "bare string root gets path $")


class _StubRuntime:
    connection = None


class _StubSession:
    """Only what execute() touches up to (and just past) the corruption gate."""
    def __init__(self):
        self.runtime = _StubRuntime()
        self.meta_events = []

    def _log_meta(self, event, **fields):
        self.meta_events.append((event, fields))

    def check_budget(self):
        # Sentinel: control reaching here proves the gate let the call through.
        raise _PassedGate


class _PassedGate(Exception):
    pass


def make_executor(session):
    ex = ToolExecutor.__new__(ToolExecutor)
    ex._session = session
    return ex


def test_execute_gate():
    session = _StubSession()
    ex = make_executor(session)

    corrupt_args = {"proof_operations": [{"operation": "Obvious",
                                          "thought": LONE_HIGH, "facts": []}]}
    result, is_error = asyncio.run(ex.execute("edit", corrupt_args))
    check(is_error is True, "corrupted input -> is_error")
    check("unpaired UTF-16 surrogate" in result, "rejection wording")
    check(session.meta_events
          and session.meta_events[0][0] == "CORRUPTED_TOOL_INPUT"
          and session.meta_events[0][1]["tool"] == "edit"
          and "\\ud835" in session.meta_events[0][1]["value"],
          "CORRUPTED_TOOL_INPUT meta event with ascii-escaped value")
    check(not any("\ud835" in str(v) for _, f in session.meta_events
                  for v in f.values()),
          "no raw surrogate leaks into the meta event fields")

    # Clean input passes the gate: the stub's check_budget sentinel fires,
    # proving execute proceeded beyond the corruption check.
    try:
        asyncio.run(ex.execute("edit", {"proof_operations": [
            {"operation": "Obvious", "thought": PAIRED, "facts": []}]}))
        check(False, "clean input should reach check_budget (sentinel)")
    except _PassedGate:
        check(True, "clean input passes the gate untouched")


def main():
    test_find_lone_surrogate()
    test_execute_gate()
    if failures:
        print(f"\n{len(failures)} FAILURE(S)")
        sys.exit(1)
    print("\nall passed")


if __name__ == "__main__":
    main()
