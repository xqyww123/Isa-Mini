"""Usage count -- how often `by aoa` is used.

One anonymous HTTP report per execution of the `by aoa` proof method, sent to a
Cloudflare Worker that keeps a per-day tally.  No identifier of any kind is sent:
the payload is the event kind, the AoA version and `sys.platform`, and nothing
else.  See ../../../AOA_USAGE_COUNT_PLAN.md for the design.

Two rules govern everything here:

1. It can never affect a proof.  Reporting is fire-and-forget -- the caller does
   not await it -- and every failure (DNS, TLS, proxy, timeout, 5xx, a machine
   with no network at all) is swallowed at debug level.  A user behind a firewall
   must not notice that this module exists.
2. It must never raise at import.  This module is imported by `toplevel.py`, so
   an exception here would take down `IsaMini.AoA` itself and every `by aoa`
   would fail with `Unknown procedure IsaMini.AoA`.
"""

import asyncio
import logging
import os
import sys

_logger = logging.getLogger(__name__)

ENDPOINT = "https://aoa.qiyuan.me/usage_counter"

# Generous enough for a slow link, short enough that nothing piles up.  Nobody
# waits on this, so the only thing the timeout bounds is how long a doomed task
# sits in `_in_flight`.
_TIMEOUT = 3.0

# The two event kinds, mirroring the Worker's allow-list.  `cache` is a `by aoa`
# served by replaying the proof cache; `agent` is one that got past the cache and
# entered the agent.  The server increments both columns for `agent`, because
# every agent run is also one execution of the method.
EVENT_CACHE = "cache"
EVENT_AGENT = "agent"


def _disabled() -> bool:
    """Whether the user has switched reporting off.

    `AOA_DISABLE_USAGE_COUNT`: any non-empty value other than "0" disables.  Read
    ONCE, at import -- the RPC host process is started by Isabelle and lives as
    long as the session, so changing the variable takes effect on the next
    Isabelle start.  That is the documented behaviour, and it is why the Readme
    tells users to put the line in `$ISABELLE_HOME_USER/etc/settings` rather than
    "in your environment".
    """
    v = os.environ.get("AOA_DISABLE_USAGE_COUNT", "").strip()
    return bool(v) and v != "0"


def _version() -> str:
    """The AoA version, or "unknown" when there is no installed distribution.

    Note this reports the version of the INSTALLED distribution, which on a
    development checkout may differ from the code actually being imported.  End
    users have exactly one of each, so for them the two always agree.
    """
    try:
        from importlib.metadata import version
        return version("IsaMini")
    except Exception:
        return "unknown"


DISABLED = _disabled()
VERSION = _version()
PLATFORM = sys.platform

# Strong references to the in-flight report tasks.  asyncio's task registry holds
# only WEAK references, so a task nobody keeps can be garbage-collected while it
# is still running -- losing the report and printing "Task was destroyed but it
# is pending!".  The done-callback empties the set again.
_in_flight: "set[asyncio.Task]" = set()


async def _send(event: str) -> None:
    """Post one report.  Never raises."""
    try:
        # Imported here, not at module level: `httpx` is a declared dependency,
        # but an import failure inside this module would break `toplevel.py` and
        # therefore every `by aoa`.  Inside the coroutine the worst case is a
        # swallowed failure of the counter alone.
        import httpx
        async with httpx.AsyncClient(timeout=_TIMEOUT) as client:
            await client.post(ENDPOINT, json={
                "event": event,
                "version": VERSION,
                "platform": PLATFORM,
            })
    except Exception as e:
        # Debug, never warning: a user with no network must see nothing.
        _logger.debug("usage count not sent (%s): %r", event, e)


def report(event: str) -> None:
    """Report one `by aoa` execution.  Returns immediately; never raises.

    Fire-and-forget by design: the report is not awaited and is not retried, so a
    process that exits first simply loses it.  The attached RPC host dies by
    `os._exit`, which runs no atexit handler and drains no event loop, so there
    is no shutdown hook that could flush anything anyway -- and a lost count is
    an acceptable price for never delaying a proof.
    """
    if DISABLED:
        return
    try:
        task = asyncio.get_running_loop().create_task(_send(event))
    except RuntimeError:
        # No running loop (nobody calls this outside the RPC handler, but a
        # counter must not be the thing that raises).
        return
    _in_flight.add(task)
    task.add_done_callback(_in_flight.discard)
