"""Unit tests for `_ensure_semantic_db` -- the L19 empty-DB check.

The hook is a pure check now (SEMANTIC_DB_LAYERED_PLAN L19): when the layered
semantic database is empty it emits ONE warning per process -- whose wording
branches on whether the environment is conda-managed -- and AoA runs bare;
when the DB is present it does nothing at all.  No download, no heartbeat.

snapshot_sync is mocked, so no LMDB is touched.  `_ensure_semantic_db` does
`from ...snapshot_sync import semantic_db_is_empty` at call time, so patching
the attribute on the snapshot_sync module is what the function actually sees.
"""
import asyncio
import logging
import os
import sys
import types

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from IsaMini.AoA import toplevel               # noqa: E402
import Isabelle_Semantic_Embedding.snapshot_sync as snap   # noqa: E402


class _Conn:
    """A Connection stub with just what _ensure_semantic_db touches: the host
    logger and the warning channel.  `msgs` records (channel, text) so tests can
    pin not only what was said but where it surfaced."""

    def __init__(self):
        self.msgs = []
        self.server = types.SimpleNamespace(logger=logging.getLogger("_ensure_test"))

    async def warning(self, m):
        self.msgs.append(("warning", m))

    async def writeln(self, m):
        self.msgs.append(("writeln", m))


def _run(coro):
    loop = asyncio.new_event_loop()
    try:
        return loop.run_until_complete(coro)
    finally:
        loop.close()


@pytest.fixture(autouse=True)
def _defaults(monkeypatch, tmp_path):
    """A present DB and a non-conda prefix by default; the once-per-process
    flag is reset so every test starts from a fresh process's point of view."""
    monkeypatch.setattr(snap, "semantic_db_is_empty", lambda: False)
    monkeypatch.setattr(sys, "prefix", str(tmp_path / "prefix"))
    monkeypatch.setattr(toplevel, "_warned_empty_semantic_db", False)


def test_present_db_is_silent():
    conn = _Conn()
    _run(toplevel._ensure_semantic_db(conn))
    assert conn.msgs == []


def test_empty_db_warns_with_the_pull_hint(monkeypatch):
    monkeypatch.setattr(snap, "semantic_db_is_empty", lambda: True)
    conn = _Conn()
    _run(toplevel._ensure_semantic_db(conn))
    [(channel, msg)] = conn.msgs
    assert channel == "warning"
    assert "AoA will run without it" in msg
    assert "isabelle-semantics pull" in msg
    assert "conda install" not in msg


def test_empty_db_in_a_conda_env_suggests_conda_install(monkeypatch, tmp_path):
    monkeypatch.setattr(snap, "semantic_db_is_empty", lambda: True)
    os.makedirs(tmp_path / "prefix" / "conda-meta")
    conn = _Conn()
    _run(toplevel._ensure_semantic_db(conn))
    [(channel, msg)] = conn.msgs
    assert channel == "warning"
    assert "conda install -c https://conda.qiyuan.me isabelle-semantic-data" in msg
    assert "isabelle-semantics pull" not in msg


def test_warns_only_once_per_process(monkeypatch):
    monkeypatch.setattr(snap, "semantic_db_is_empty", lambda: True)
    conn = _Conn()
    _run(toplevel._ensure_semantic_db(conn))
    _run(toplevel._ensure_semantic_db(conn))
    other = _Conn()
    _run(toplevel._ensure_semantic_db(other))
    assert len(conn.msgs) == 1
    assert other.msgs == []


def test_check_runs_again_while_db_stays_present(monkeypatch):
    """The cheap check itself is per-call; only the WARNING is once-per-process."""
    calls = []
    monkeypatch.setattr(snap, "semantic_db_is_empty",
                        lambda: calls.append(1) or False)
    conn = _Conn()
    _run(toplevel._ensure_semantic_db(conn))
    _run(toplevel._ensure_semantic_db(conn))
    assert len(calls) == 2 and conn.msgs == []


def test_unreadable_db_degrades_to_a_warning_and_never_raises(monkeypatch):
    def boom():
        raise RuntimeError("MDB_CORRUPTED")
    monkeypatch.setattr(snap, "semantic_db_is_empty", boom)
    conn = _Conn()
    _run(toplevel._ensure_semantic_db(conn))       # must not raise
    [(channel, msg)] = conn.msgs
    assert channel == "warning"
    assert "MDB_CORRUPTED" in msg and "isabelle-semantics fsck" in msg


def test_a_dead_warning_callback_never_breaks_the_flow(monkeypatch):
    monkeypatch.setattr(snap, "semantic_db_is_empty", lambda: True)
    conn = _Conn()

    async def dead(_m):
        raise ConnectionError("panel gone")
    conn.warning = dead
    _run(toplevel._ensure_semantic_db(conn))       # must not raise
