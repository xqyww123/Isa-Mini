"""
Test: can Python detect when Isabelle interrupts a tactic?

"test_sleep_forever" sleeps in a loop, logging each iteration.
When ML catches the interrupt, it sends an error "Isabelle_Interrupt"
before closing the connection.  The reader loop receives it and
pushes it onto _user_channel, which we monitor alongside the sleep.
"""

import asyncio
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection


@isabelle_remote_procedure("test_sleep_forever")
async def test_sleep_forever(arg, connection: Connection):
    logger = connection.server.logger
    logger.warning("[test_interrupt] RPC started, sleeping forever...")

    try:
        i = 0
        while True:
            reader = connection._reader_task
            sleep = asyncio.ensure_future(asyncio.sleep(2))

            if reader is not None and not reader.done():
                done, _ = await asyncio.wait(
                    [sleep, reader],
                    return_when=asyncio.FIRST_COMPLETED,
                )
                if reader in done:
                    sleep.cancel()
                    logger.warning(
                        f"[test_interrupt] READER DIED at iteration {i} "
                        f"— interrupt detected!")
                    return None
            else:
                await sleep

            i += 1
            logger.warning(f"[test_interrupt] alive, iteration {i}")

    except asyncio.CancelledError:
        logger.warning("[test_interrupt] CancelledError")
        raise
    except Exception as e:
        logger.warning(f"[test_interrupt] {type(e).__name__}: {e}")
        raise
    finally:
        logger.warning("[test_interrupt] handler exiting")
