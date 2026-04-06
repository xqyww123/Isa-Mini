from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import *
from typing import Any
from . import driver_claude_code
import sys
import io
import os
import tempfile
import subprocess

class UnknownDriver(AoA_Error):
    def __init__(self, driver: str):
        super().__init__(f"Unknown driver: {driver}")

@isabelle_remote_procedure("IsaMini.AoA")
async def IsaMini_AoA(data: tuple[Any, Any, str, str, str, str, str], connection: Connection):
    (global_context, ptree, driver, log_dir, invocation_id,
     retrieval_forking_str, interactive_retrieval_str) = data

    # Environment variable AoA_LOG_DIR overrides user-provided log_dir
    env_log_dir = os.environ.get('AoA_LOG_DIR')
    if env_log_dir:
        log_dir = env_log_dir

    # Construct actual log path: log_dir/invocation_id
    if log_dir != "":
        actual_log_path = os.path.join(log_dir, invocation_id)
    else:
        actual_log_path = ""

    global_context = Context.unpack(global_context)
    ptree = unpack_MLPT(ptree)
    if driver.startswith("test."):
        # Run specific test associated with the driver
        from .test import TESTS
        test_name = driver[len("test."):]
        if test_name not in TESTS:
            raise ValueError(f"Test Not Found on '{test_name}'")
        case = TESTS[test_name]
        root = await case.run(connection, actual_log_path, global_context, ptree)
        cost = (0, 0, 0, 0, 0.0)
    else:
        drv = Session.Driver.get(driver)
        if drv is None:
            raise UnknownDriver(driver)
        retrieval_forking = FORKING_MODE_MAP.get(
            retrieval_forking_str, ForkingMode.FORKING_WITH_CTXT)
        interactive_retrieval = INTERACTIVE_RETRIEVAL_MAP.get(
            interactive_retrieval_str, InteractiveRetrievalMode.YES_WITH_RECURSIVE_RETRIEVAL)
        async with drv(connection.server.logger, actual_log_path,
                       retrieval_forking_mode=retrieval_forking,
                       interactive_retrieval=interactive_retrieval) as session:
            root = Root((global_context, ptree), connection, session)
            await session.initialize(root)
            await session.run()
            cost = (session.total_input_tokens,
                    session.total_cache_creation_input_tokens,
                    session.total_cache_read_input_tokens,
                    session.total_output_tokens,
                    session.total_cost_usd)

    if root.is_proof_finished():
        return ([x.pack() for x in root.assemble()], root.final_ml_state.name, cost)
    else:
        return ([x.pack() for x in root.assemble()], None, cost)
    # Finally, we return the constructed proof



