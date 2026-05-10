"""
Test: does handle_client cancel the RPC handler when the connection drops?

"test_sleep_forever" just sleeps. When ML interrupts and closes the
connection, handle_client detects _reader_task death and cancels us.
We log what we receive.
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
            await asyncio.sleep(2)
            i += 1
            logger.warning(f"[test_interrupt] alive, iteration {i}")
    except asyncio.CancelledError:
        logger.warning("[test_interrupt] GOT CancelledError — interrupt propagated!")
        raise
    finally:
        logger.warning("[test_interrupt] handler exiting")
