"""Tests for warn_AoA_opr(to_isabelle=True).

This path shipped in 8ef3ef0 having never been executed: it called
`self.trace_to_isabelle_nowait(...)` from Session, but the panel helpers live on
Root and Session is not a Root, so it raised AttributeError -- from inside the very
`except` handlers that set the flag, turning a 20-minute quota wait or a clean
LMUnreachable give-up into a crashed `by aoa`, exactly when the message mattered
most.  These tests execute the branch instead of reasoning about it.
"""
import asyncio
import types

import pytest

from IsaMini.AoA.model import Session, Root


class _StubConn:
    class LogType:
        TRACING, WARNING, WRITELN = 0, 1, 2

    def __init__(self):
        self.sent = []

    async def callback(self, name, arg):
        self.sent.append((name, arg))


def _session():
    """A Session wired up with just what warn_AoA_opr touches. `role_label` is a
    read-only property, so `logger` stays None (it is the only reader)."""
    sess = object.__new__(Session)
    root = object.__new__(Root)
    conn = _StubConn()
    root.ml_state = types.SimpleNamespace(connection=conn)
    root._tracing_tasks = set()
    sess.root = root
    sess.interaction_log_file = None
    sess.logger = None
    sess._log = lambda *a, **k: None
    return sess, conn


def test_to_isabelle_reaches_the_panel_on_the_warning_channel():
    async def go():
        sess, conn = _session()
        sess.warn_AoA_opr("Quota exhausted, waiting 20min to retry (resets at 14:00)",
                          to_isabelle=True)
        await asyncio.sleep(0.05)   # the send is fire-and-forget
        assert conn.sent, "nothing reached Isabelle"
        name, (level, msg) = conn.sent[0]
        assert name == "log"
        assert level == _StubConn.LogType.WARNING
        assert msg.startswith("[AoA] ") and "Quota exhausted" in msg
    asyncio.run(go())


def test_default_stays_out_of_the_panel():
    """Opt-in matters: 21 of the 27 warn_AoA_opr sites are 2-second retry notices
    and cleanup failures, and routing them all would bury the ones that matter."""
    async def go():
        sess, conn = _session()
        sess.warn_AoA_opr("a routine transient-retry notice")
        await asyncio.sleep(0.05)
        assert not conn.sent, f"default leaked to the panel: {conn.sent}"
    asyncio.run(go())
