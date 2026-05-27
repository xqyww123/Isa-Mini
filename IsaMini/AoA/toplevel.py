from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import *
from typing import Any
import json
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
_try_import_driver("driver_gemini")
_try_import_driver("driver_anthropic")
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

async def _replay_cached_proof(connection: Connection, packed_ops: list[Any],
                               cache_source: str = "") -> tuple[bool, str | None]:
    """Replay a cached proof by feeding operations through proof_opr callbacks.
    Returns (success, final_state_name)."""
    await connection.callback("IsaMini.set_replay_mode", True)
    try:
        state_name = "$init"
        for i, packed_op in enumerate(packed_ops):
            dest_name = f"$replay_{i+1}"
            await connection.callback("IsaMini.proof_opr",
                (state_name, dest_name, packed_op))
            state_name = dest_name
        return (True, state_name)
    except Exception as e:
        _logger.info(f"Proof replay failed ({cache_source}): {e}")
        return (False, None)
    finally:
        await connection.callback("IsaMini.set_replay_mode", False)

@isabelle_remote_procedure("IsaMini.AoA")
async def IsaMini_AoA(data: tuple, connection: Connection):
    (global_context, ptree, driver, log_dir, invocation_id,
     retrieval_forking_str, interactive_retrieval_str, budget_tuple,
     goal_hash, cached_xcmd_json) = data
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

    # --- Multi-level cache check ---
    from .proof_cache import get_proof_cache
    zero_cost = (0, 0, 0, 0, 0.0, 0, 0.0, 0.0, 0.0)

    # Level 1: Python SQLite
    cached_ops = get_proof_cache().lookup(goal_hash)

    # Level 2: Phi_Cache_DB (from ML)
    if cached_ops is None and cached_xcmd_json:
        try:
            cached_ops = json.loads(cached_xcmd_json)
        except (json.JSONDecodeError, TypeError):
            cached_ops = None

    if cached_ops is not None:
        cache_source = "SQLite" if not cached_xcmd_json or get_proof_cache().lookup(goal_hash) is not None else "Phi_Cache_DB"
        ok, final_state = await _replay_cached_proof(connection, cached_ops, cache_source)
        if ok:
            proof_json = json.dumps(cached_ops)
            return (cached_ops, final_state, zero_cost, None, None, proof_json)
        # replay failed — fall through to agent

    # --- Level 3: Full agent run ---
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
        cost = zero_cost
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
            root = Root((global_context, ptree), connection)
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
        proof_json = json.dumps(assembled)
        # Store in Python SQLite cache
        get_proof_cache().store(goal_hash, assembled)
        # Write to log directory
        if actual_log_path:
            try:
                os.makedirs(actual_log_path, exist_ok=True)
                with open(os.path.join(actual_log_path, "proof.json"), "w") as f:
                    f.write(proof_json)
            except Exception as e:
                _logger.warning(f"Failed to write proof.json: {e}")
        return (assembled, root.final_ml_state.name, cost, None, None, proof_json)
    else:
        reason, detail = root.quit_info or ("resource_exhausted", None)
        return (assembled, None, cost, reason, detail, None)



