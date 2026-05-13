from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import *
from typing import Any
import logging as _logging
_logger = _logging.getLogger(__name__)

def _try_import_driver(name: str):
    try:
        __import__(f"{__package__}.{name}")
    except ImportError as e:
        _logger.info(f"Driver {name} not loaded (missing dependency: {e.name})")

from . import driver_claude_code
_try_import_driver("driver_openai")
_try_import_driver("driver_codex")
_try_import_driver("driver_api")
import sys
import io
import os
import tempfile
import subprocess

class UnknownDriver(AoA_Error):
    def __init__(self, driver: str):
        super().__init__(f"Unknown driver: {driver}")

_test_driver = object()
Session.Driver["test"] = _test_driver  # type: ignore[assignment]


@isabelle_remote_procedure("IsaMini.query_by_name")
async def _query_by_name_rpc(arg: tuple[int, str], connection: Connection) -> tuple[str, bool]:
    """Query entity by kind and name — reuses the core of the MCP query tool."""
    from .retrieval import _query_entity_core
    from Isabelle_RPC_Host.universal_key import EntityKind
    kind_int, name = arg
    tag = EntityKind(kind_int)
    text, is_error, _uk = await _query_entity_core(connection, tag, name)
    return (text, is_error)

@isabelle_remote_procedure("IsaMini.AoA")
async def IsaMini_AoA(data: tuple[Any, Any, str, str, str, str, str, tuple[int, int, int]], connection: Connection):
    (global_context, ptree, driver, log_dir, invocation_id,
     retrieval_forking_str, interactive_retrieval_str, budget_tuple) = data
    timeout_seconds, max_tool_calls, max_retries = budget_tuple

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
    ptree = Minilang_State._unpack_flat_goal(ptree)
    if "." in driver:
        driver_name, argument = driver.split(".", 1)
        argument = argument or None
    else:
        driver_name = driver
        argument = None

    drv = Session.Driver.get(driver_name)
    if drv is None:
        raise UnknownDriver(driver)

    if drv is _test_driver:
        from .test import TESTS
        if argument is None or argument not in TESTS:
            raise ValueError(f"Test Not Found on '{argument}'")
        case = TESTS[argument]
        root = await case.run(connection, actual_log_path, global_context, ptree)
        cost = (0, 0, 0, 0, 0.0, 0, 0.0, 0.0, 0.0)
        is_test = True
    else:
        is_test = False
        logger = connection.server.logger
        retrieval_forking = FORKING_MODE_MAP.get(retrieval_forking_str)
        if retrieval_forking is None:
            if retrieval_forking_str:
                logger.warning(
                    f"Unknown retrieval_forking '{retrieval_forking_str}', "
                    f"falling back to 'with_ctxt'. Known: {sorted(FORKING_MODE_MAP)}")
            retrieval_forking = ForkingMode.FORKING_WITH_CTXT
        interactive_retrieval = INTERACTIVE_RETRIEVAL_MAP.get(interactive_retrieval_str)
        if interactive_retrieval is None:
            if interactive_retrieval_str:
                logger.warning(
                    f"Unknown interactive_retrieval '{interactive_retrieval_str}', "
                    f"falling back to 'no'. "
                    f"Known: {sorted(INTERACTIVE_RETRIEVAL_MAP)}")
            interactive_retrieval = InteractiveRetrievalMode.NO
        async with drv(connection.server.logger, actual_log_path,
                       argument=argument,
                       retrieval_forking_mode=retrieval_forking,
                       interactive_retrieval=interactive_retrieval,
                       timeout_seconds=timeout_seconds,
                       max_tool_calls=max_tool_calls,
                       max_retries=max_retries) as session:
            root = Root((global_context, ptree), connection, session)
            await session.initialize(root)
            await session.run()
            cost = (session.total_input_tokens,
                    session.total_cache_creation_input_tokens,
                    session.total_cache_read_input_tokens,
                    session.total_output_tokens,
                    session.total_cost_usd,
                    session.total_tool_calls,
                    session.total_isabelle_time,
                    session.total_model_time,
                    session.total_quota_wait_time)

    try:
        assembled = [x.pack() for x in root.assemble()]
    except InternalError:
        if not is_test:
            raise
        assembled = []
    if root.is_proof_finished():
        return (assembled, root.final_ml_state.name, cost, None, None)
    else:
        reason, detail = root.quit_info or ("resource_exhausted", None)
        return (assembled, None, cost, reason, detail)
    # Finally, we return the constructed proof



