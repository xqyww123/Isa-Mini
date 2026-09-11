#!/usr/bin/env python3
"""Inside one of AoA's RPC procedures an interrupted Isabelle callback is a
cancellation (`interrupts_are_cancellations`): whoever calls back through
the connection -- AoA directly, a helper of the connection's own such as
`config_lookup`, or a vector store built on the connection before or during
the procedure -- gets `asyncio.CancelledError` with the interrupt as its
cause; a result and an ordinary `IsabelleError` pass through unchanged; and
once the procedure has returned or raised the connection is as it was.

No Isabelle / no REPL / no LLM.  Run directly
(``python test_interrupt_is_cancellation.py``) or under pytest.
"""
import asyncio
import os
import sys
from typing import Any, cast

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from Isabelle_RPC_Host import Connection, IsabelleError, IsabelleInterrupt
from IsaMini.AoA.model import interrupts_are_cancellations


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)


class Fake_Connection(Connection):
    """A real Connection but for the wire: only `callback` is replaced, so
    the helpers under test (`config_lookup`) are the library's own."""
    def __init__(self):
        pass

    async def callback(self, name, arg):
        if name == "echo":
            return arg
        if name == "boom":
            raise IsabelleError(["boom"], None)
        raise IsabelleInterrupt(["Interrupt"], None)


class Fake_Store:
    """Keeps the connection it was built with and calls back through it, as
    Semantic_Vector_Store does."""
    def __init__(self, connection):
        self.connection = connection

    async def lookup(self):
        return await self.connection.callback("lookup", None)


async def expect_cancellation(awaitable) -> None:
    try:
        await awaitable
    except asyncio.CancelledError as e:
        check(isinstance(e.__cause__, IsabelleInterrupt), "the cancellation must carry the interrupt as its cause")
        check("Interrupt" in str(e), f"the cancellation names the interrupt: {e!r}")
        return
    check(False, "expected asyncio.CancelledError")


async def main() -> None:
    connection = Fake_Connection()
    store_before = Fake_Store(connection)          # cached on the connection before the procedure

    @interrupts_are_cancellations
    async def procedure(arg, connection):
        check(await connection.callback("echo", arg) == arg, "a result passes through the shadow unchanged")
        try:
            await connection.callback("boom", None)
        except IsabelleError as e:
            check(not isinstance(e, IsabelleInterrupt) and e.errors == ["boom"], "an ordinary error passes through as itself")
        else:
            check(False, "expected IsabelleError")
        await expect_cancellation(connection.callback("IsaMini.proof_opr", arg))
        await expect_cancellation(connection.config_lookup("AoA_Debug"))
        await expect_cancellation(store_before.lookup())
        await expect_cancellation(Fake_Store(connection).lookup())
        return "done"

    check(await procedure(41, connection) == "done", "the procedure's result passes through")
    check("callback" not in vars(connection), "the shadow is removed once the procedure returns")
    try:
        await store_before.lookup()
    except IsabelleInterrupt:
        pass
    else:
        check(False, "after the procedure the connection is as it was: the interrupt is raised again")

    @interrupts_are_cancellations
    async def failing(arg, connection):
        raise ValueError("boom")

    try:
        await failing(None, connection)
    except ValueError:
        pass
    check("callback" not in vars(connection), "the shadow is removed when the procedure raises")

    @interrupts_are_cancellations
    async def outer(arg, connection):
        await procedure(arg, connection)
        await expect_cancellation(connection.callback("x", None))
        return "callback" in vars(connection)

    check(await outer(41, connection), "a nested procedure restores the outer shadow, not the class method")
    check("callback" not in vars(connection), "and the outermost exit removes it")
    await aclose_is_total()


async def aclose_is_total() -> None:
    """A worker that ended in a converted interrupt: `WorkerHandle.aclose`
    still tears it down (twice, idempotently), while `wait_finish` alone
    still re-raises the cancellation to the planner."""
    from types import SimpleNamespace
    from IsaMini.AoA.model import WorkerHandle

    async def interrupted():
        raise asyncio.CancelledError("Isabelle interrupted: Interrupt")
    task = asyncio.ensure_future(interrupted())
    try:
        await task
    except asyncio.CancelledError:
        pass
    handle = WorkerHandle.__new__(WorkerHandle)
    handle._task = task
    handle._pending_review = handle._pending_resume = None
    handle._cancelled_by_us = False
    handle.target = cast(Any, SimpleNamespace(worker_handle=handle))
    settled = []
    handle._settle_costs = lambda: settled.append(True)

    await handle.aclose()
    await handle.aclose()
    check(handle.target.worker_handle is None and settled, "aclose tears an interrupted worker down and is idempotent")
    try:
        await handle.wait_finish()
    except asyncio.CancelledError:
        pass
    else:
        check(False, "wait_finish alone still re-raises the converted interrupt")


def test_interrupts_are_cancellations():
    asyncio.run(main())


if __name__ == "__main__":
    asyncio.run(main())
    print("test_interrupt_is_cancellation: all checks passed")
