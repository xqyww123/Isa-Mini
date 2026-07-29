"""Unit tests for `usage_count` -- the anonymous per-execution usage report.

Two properties matter more than the reporting itself, and both are tested here:
the report can never affect a proof (no exception escapes, whatever the network
does), and the off switch really switches it off.

`usage_count` reads its environment ONCE at import, so every test that cares
about the switch reloads the module under a patched environment.  It also imports
httpx from inside the coroutine, which is what lets these tests substitute a fake
one through `sys.modules` without any network.
"""
import asyncio
import importlib
import os
import sys
import types

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from IsaMini.AoA import usage_count as uc               # noqa: E402


# --- a fake httpx, installed into sys.modules for the duration of a test -------

class _FakeClient:
    """Records the posts it is given, or raises whatever it was handed."""

    def __init__(self, sent, exc, **kwargs):
        self._sent = sent
        self._exc = exc
        self.kwargs = kwargs

    async def __aenter__(self):
        return self

    async def __aexit__(self, *exc_info):
        return False

    async def post(self, url, json=None):
        if self._exc is not None:
            raise self._exc
        self._sent.append((url, json))
        return types.SimpleNamespace(status_code=204)


def _install_fake_httpx(monkeypatch, exc=None):
    """Put a fake `httpx` in sys.modules; return the list of posts it records."""
    sent = []
    mod = types.ModuleType("httpx")
    mod.AsyncClient = lambda **kw: _FakeClient(sent, exc, **kw)   # type: ignore[attr-defined]
    monkeypatch.setitem(sys.modules, "httpx", mod)
    return sent


def _reload(monkeypatch, switch):
    """Reload usage_count with AOA_DISABLE_USAGE_COUNT set to `switch` (None = unset)."""
    if switch is None:
        monkeypatch.delenv("AOA_DISABLE_USAGE_COUNT", raising=False)
    else:
        monkeypatch.setenv("AOA_DISABLE_USAGE_COUNT", switch)
    return importlib.reload(uc)


async def _drain(mod):
    """Wait for the fire-and-forget tasks the module has in flight."""
    while mod._in_flight:
        await asyncio.gather(*list(mod._in_flight), return_exceptions=True)


# --- what gets sent -----------------------------------------------------------

def test_payload_carries_exactly_three_fields(monkeypatch):
    """The wire format is the disclosure: event, version, platform, and NOTHING
    else.  A new field here would silently break the promise in the Readme."""
    mod = _reload(monkeypatch, None)
    sent = _install_fake_httpx(monkeypatch)

    async def go():
        mod.report(mod.EVENT_AGENT)
        await _drain(mod)

    asyncio.run(go())

    assert len(sent) == 1
    url, payload = sent[0]
    assert url == mod.ENDPOINT
    assert set(payload) == {"event", "version", "platform"}
    assert payload["event"] == "agent"
    assert payload["platform"] == sys.platform
    assert isinstance(payload["version"], str) and payload["version"]


def test_event_names_match_the_worker_allow_list():
    """These two strings are a contract with the Worker's EVENTS map; drift would
    turn every report into a 400 that the client silently swallows."""
    assert uc.EVENT_CACHE == "cache"
    assert uc.EVENT_AGENT == "agent"


# --- the off switch -----------------------------------------------------------

@pytest.mark.parametrize("switch", ["1", "true", "yes", " 1 "])
def test_switch_off_sends_nothing(monkeypatch, switch):
    mod = _reload(monkeypatch, switch)
    sent = _install_fake_httpx(monkeypatch)

    async def go():
        mod.report(mod.EVENT_AGENT)
        mod.report(mod.EVENT_CACHE)
        await _drain(mod)

    asyncio.run(go())
    assert sent == []


@pytest.mark.parametrize("switch", [None, "", "0"])
def test_switch_absent_or_zero_keeps_reporting(monkeypatch, switch):
    mod = _reload(monkeypatch, switch)
    sent = _install_fake_httpx(monkeypatch)

    async def go():
        mod.report(mod.EVENT_CACHE)
        await _drain(mod)

    asyncio.run(go())
    assert len(sent) == 1


# --- it can never affect a proof ---------------------------------------------

@pytest.mark.parametrize("exc", [
    asyncio.TimeoutError(),
    ConnectionRefusedError("no route"),
    OSError("network unreachable"),
    RuntimeError("some httpx internal"),
])
def test_network_failures_never_escape(monkeypatch, exc):
    """Whatever the network does, `report` and the task it spawns stay silent."""
    mod = _reload(monkeypatch, None)
    _install_fake_httpx(monkeypatch, exc=exc)

    async def go():
        mod.report(mod.EVENT_AGENT)          # must not raise
        results = await asyncio.gather(*list(mod._in_flight), return_exceptions=True)
        # The task completes normally -- the exception is swallowed inside _send,
        # not merely re-raised into a place nobody looks.
        assert all(not isinstance(r, BaseException) for r in results)

    asyncio.run(go())


def test_missing_httpx_is_survivable(monkeypatch):
    """httpx is a declared dependency, but its absence must degrade to a silent
    non-report -- never to a broken `by aoa`."""
    mod = _reload(monkeypatch, None)
    monkeypatch.setitem(sys.modules, "httpx", None)   # import httpx -> ImportError

    async def go():
        mod.report(mod.EVENT_AGENT)
        await _drain(mod)

    asyncio.run(go())        # the assertion is that this does not raise


def test_report_outside_an_event_loop_is_a_no_op(monkeypatch):
    """Nothing calls it this way today, but a counter must not be the thing that
    raises when someone does."""
    mod = _reload(monkeypatch, None)
    _install_fake_httpx(monkeypatch)
    assert mod.report(mod.EVENT_CACHE) is None


def test_caller_is_not_delayed(monkeypatch):
    """`report` returns before the request is made -- it schedules, it does not
    await.  A slow endpoint must not slow a proof down."""
    mod = _reload(monkeypatch, None)
    sent = _install_fake_httpx(monkeypatch)

    async def go():
        mod.report(mod.EVENT_AGENT)
        # The task has not been given a chance to run yet, so nothing is sent.
        assert sent == []
        await _drain(mod)
        assert len(sent) == 1

    asyncio.run(go())


# --- the fire-and-forget task must not be garbage-collected -------------------

def test_task_is_strongly_referenced_until_it_finishes(monkeypatch):
    """asyncio keeps only weak references to tasks; without the module's own set
    a report can vanish mid-flight."""
    mod = _reload(monkeypatch, None)
    _install_fake_httpx(monkeypatch)

    async def go():
        assert mod._in_flight == set()
        mod.report(mod.EVENT_AGENT)
        assert len(mod._in_flight) == 1          # held while in flight
        await _drain(mod)
        assert mod._in_flight == set()           # and released afterwards

    asyncio.run(go())
