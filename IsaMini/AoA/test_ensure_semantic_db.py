"""Unit tests for `_ensure_semantic_db` -- the empty/incomplete-DB auto-pull control
flow: the forced pull, the progress heartbeat, and every degrade-to-bare-run path.
r2_sync is mocked, so no network and no LMDB are touched.

`_ensure_semantic_db` does `from ...r2_sync import <names>` at call time, so patching
attributes on the r2_sync module is what the function actually sees.
"""
import asyncio
import os
import sys
import time as _time

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from IsaMini.AoA import toplevel               # noqa: E402
import Isabelle_Semantic_Embedding.r2_sync as r2   # noqa: E402


class _Log:
    def __init__(self):
        self.msgs = []

    def warning(self, m):
        self.msgs.append(m)


def _run(coro):
    loop = asyncio.new_event_loop()
    try:
        return loop.run_until_complete(coro)
    finally:
        loop.close()


@pytest.fixture(autouse=True)
def _defaults(monkeypatch):
    """A present, whole DB by default; each test overrides what it exercises."""
    monkeypatch.setattr(r2, "semantic_db_is_empty", lambda: False)
    monkeypatch.setattr(r2, "pull_was_interrupted", lambda: False)
    monkeypatch.setattr(r2, "semantic_db_record_count", lambda: 123)


def test_present_db_returns_true_and_is_silent():
    lg = _Log()
    assert _run(toplevel._ensure_semantic_db(lg)) is True
    assert lg.msgs == []


def test_empty_db_pulls_forced_and_announces_ready(monkeypatch):
    monkeypatch.setattr(r2, "semantic_db_is_empty", lambda: True)
    captured = {}

    def fake_pull(**kw):
        captured.update(kw)
        return True
    monkeypatch.setattr(r2, "pull_snapshot", fake_pull)

    lg = _Log()
    assert _run(toplevel._ensure_semantic_db(lg)) is False
    assert captured.get("force") is True, "an empty DB must force past the ETag short-circuit"
    assert captured.get("require_idle") is False and captured.get("backup") is False
    assert any("Downloading it now" in m for m in lg.msgs)
    assert any("Semantic database ready (123 records)" in m for m in lg.msgs)


def test_a_leftover_sentinel_triggers_a_repull_even_when_not_empty(monkeypatch):
    monkeypatch.setattr(r2, "semantic_db_is_empty", lambda: False)
    monkeypatch.setattr(r2, "pull_was_interrupted", lambda: True)
    calls = {"n": 0}

    def fake_pull(**kw):
        calls["n"] += 1
        return True
    monkeypatch.setattr(r2, "pull_snapshot", fake_pull)

    assert _run(toplevel._ensure_semantic_db(_Log())) is False
    assert calls["n"] == 1, "a surviving .pull_incomplete must force a re-pull"


def test_lock_held_elsewhere_runs_bare(monkeypatch):
    monkeypatch.setattr(r2, "semantic_db_is_empty", lambda: True)

    def busy(**kw):
        raise r2.R2Busy("held")
    monkeypatch.setattr(r2, "pull_snapshot", busy)

    lg = _Log()
    assert _run(toplevel._ensure_semantic_db(lg)) is False
    assert any("Another process is already downloading" in m for m in lg.msgs)


def test_any_pull_failure_degrades_and_never_raises(monkeypatch):
    monkeypatch.setattr(r2, "semantic_db_is_empty", lambda: True)

    def boom(**kw):
        raise OSError("disk full")          # NOT an R2Error subclass
    monkeypatch.setattr(r2, "pull_snapshot", boom)

    lg = _Log()
    assert _run(toplevel._ensure_semantic_db(lg)) is False   # degraded, did not crash by-aoa
    assert any("Failed to prepare the semantic database" in m for m in lg.msgs)


def test_a_corrupt_local_db_probe_runs_bare(monkeypatch):
    def corrupt():
        raise Exception("MDB_CORRUPTED")
    monkeypatch.setattr(r2, "semantic_db_is_empty", corrupt)

    lg = _Log()
    assert _run(toplevel._ensure_semantic_db(lg)) is False
    assert any("may be corrupt" in m for m in lg.msgs)


def test_progress_heartbeat_fires_and_names_the_phase(monkeypatch):
    monkeypatch.setattr(r2, "semantic_db_is_empty", lambda: True)
    monkeypatch.setattr(toplevel, "_DB_PULL_HEARTBEAT_SECS", 0.05)

    def slow(**kw):
        on = kw.get("on_phase")
        if on:
            on("downloading")
        _time.sleep(0.12)
        if on:
            on("merging")
        _time.sleep(0.12)
        return True
    monkeypatch.setattr(r2, "pull_snapshot", slow)

    lg = _Log()
    _run(toplevel._ensure_semantic_db(lg))
    hb = [m for m in lg.msgs if "Preparing the semantic database" in m]
    assert hb, "no heartbeat fired during a slow pull"
    assert any("downloading" in m for m in hb) and any("merging" in m for m in hb)
