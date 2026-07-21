from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import *
from typing import Any
import json
import logging as _logging
_logger = _logging.getLogger(__name__)

# Why a driver failed to load, so `Unknown driver: X` can say so instead of leaving
# the user to guess.  Populated by _try_import_driver.
_driver_import_errors: dict[str, str] = {}

def _try_import_driver(name: str):
    """Import a driver module, tolerating ONLY a missing optional third-party dep.

    An ImportError raised INSIDE the driver -- a typo'd import, a renamed sibling --
    is a bug in our code, not an absent extra.  Swallowing it made the driver vanish
    from Session.Driver with an INFO line, and the user met it much later as
    `Unknown driver: X` with no mention of an import.  Same rule, same reason, as
    IsaMini/__init__.py's IsaREPL guard: decide on the ROOT of the missing module.
    """
    try:
        __import__(f"{__package__}.{name}")
    except ImportError as e:
        root = (e.name or "").split(".")[0]
        if root == "" or root == __package__.split(".")[0]:
            raise
        _driver_import_errors[name] = e.name or str(e)
        _logger.info(f"Driver {name} not loaded (missing dependency: {e.name})")

from . import driver_claude_code
_try_import_driver("driver_codex")
_try_import_driver("driver_api")
_try_import_driver("driver_openai_api")
# driver_gemini is not registered: GeminiProvider implements the whole Provider
# interface and rides along with refactorings (the 2026-06-04 cost accounting unified
# its cached-token handling), but the driver has never been exercised against the live
# API. The file stays; uncomment to try it, and install google-genai yourself -- the
# `gemini` extra is gone too.
# _try_import_driver("driver_gemini")
_try_import_driver("driver_anthropic")
import sys
import io
import os
import tempfile
import subprocess
import asyncio
import time

async def _resolve_isa_env(connection, name: str) -> 'str | None':
    """One env variable: the connected Isabelle's env -> this process's env -> None.

    Thin wrapper over Semantic_Embedding's _resolve_env. This host is a
    long-lived daemon whose os.environ is frozen at server start, while the
    Isabelle process re-sources etc/settings at every restart -- so user
    configuration (driver API keys above all) must be read through the
    connection to be fresh. The import is deferred per this module's style,
    not guarded: AoA hard-depends on Isabelle_Semantic_Embedding (model.py
    imports it at module top), so an absent-package fallback would protect a
    deployment that cannot exist.
    """
    from Isabelle_Semantic_Embedding.semantic_embedding import _resolve_env
    return await _resolve_env(connection, name)


async def _resolve_driver_env(connection, drv) -> 'dict[str, str]':
    """Resolve the driver's declared ENV_VARS (see LMDriver.ENV_VARS) into the
    overlay its constructor reads via env_get. Empty/unset vars are omitted so
    constructor defaults stay in charge."""
    env: dict[str, str] = {}
    for var in getattr(drv, "ENV_VARS", ()):
        val = await _resolve_isa_env(connection, var)
        if val:
            env[var] = val
    return env


class UnknownDriver(AoA_Error):
    def __init__(self, driver: str):
        # Name the reason when we have one.  A driver absent because its optional
        # dependency is missing is indistinguishable, at this point, from a driver
        # that never existed -- and that ambiguity is the whole complaint.
        msg = f"Unknown driver: {driver}"
        if _driver_import_errors:
            unloaded = ", ".join(f"{d} (needs {m})" for d, m in sorted(_driver_import_errors.items()))
            msg += f". Drivers not loaded for want of a dependency: {unloaded}"
        super().__init__(msg)

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
                               cache_source: str = "") -> tuple[bool, str | None, str | None]:
    """Replay a proof by feeding its operations through proof_opr callbacks.

    Used for BOTH a cache hit and a freshly found proof: it is the only path whose
    resulting state the Isabelle kernel has actually derived from the proof, so it
    is what the returned theorem must be concluded from.

    Returns (success, final_state_name, error).
    """
    await connection.callback("IsaMini.set_replay_mode", True)
    try:
        state_name = "$init"
        for i, packed_op in enumerate(packed_ops):
            dest_name = f"$replay_{i+1}"
            await connection.callback("IsaMini.proof_opr",
                (state_name, dest_name, packed_op))
            state_name = dest_name
        return (True, state_name, None)
    except Exception as e:
        connection.server.logger.info(f"[AoA-cache] Proof replay failed ({cache_source}): {e}")
        return (False, None, f"{type(e).__name__}: {e}")
    finally:
        await connection.callback("IsaMini.set_replay_mode", False)

_DB_PULL_HEARTBEAT_SECS = 10   # cadence of the "still preparing..." progress line


async def _ensure_semantic_db(logger) -> bool:
    """When the local semantic database is missing or a previous pull was
    interrupted, block AoA and (re-)pull it once, reporting progress; return
    whether the caller should still run `check_update`.

    AoA retrieves from this database, so with none present there is nothing to run
    against -- we download it before starting rather than proceed blind.  The
    filelock inside `pull_snapshot` serialises this across coroutines AND processes:
    the winner downloads and reports; everyone else fails fast (R2Busy) and runs
    this one proof bare.  `require_idle=False` keeps a sibling RPC host's open (and,
    while empty, useless) handle from refusing the pull; `backup=False` because an
    empty cache has nothing worth saving; `force=True` because the DB is empty or
    incomplete regardless of what a stale marker's ETag claims, so the ETag
    short-circuit must not skip the download.

    This never raises: an unreadable/corrupt DB, a lock held elsewhere, or any
    download/extract/merge error all degrade to a loud warning and a bare run -- a
    missing DB must never take down the proof RPC.

    Returns True only when the DB was already present and whole -- then
    `check_update` still runs its weekly staleness warning.  Returns False otherwise
    (we just pulled, or ran bare): no point checking staleness.
    """
    from Isabelle_Semantic_Embedding.r2_sync import (
        semantic_db_is_empty, semantic_db_record_count, pull_was_interrupted,
        pull_snapshot, R2Busy)
    try:
        needs_pull = semantic_db_is_empty() or pull_was_interrupted()
    except Exception as e:
        logger.warning(
            f"Could not read the local semantic database ({e}) — it may be corrupt. "
            "Running this proof without it; check with 'semantics_manage.py fsck' or "
            "delete it and re-pull.")
        return False
    if not needs_pull:
        return True

    logger.warning(
        "AoA cannot start without the semantic embedding database, which is not "
        "present on this machine. Downloading it now (~0.7 GB, one-time setup) — "
        "this may take a few minutes. AoA will begin automatically when it is ready.")
    phase = {"now": "starting"}
    started = time.monotonic()
    task = asyncio.create_task(asyncio.to_thread(
        pull_snapshot, require_idle=False, backup=False, force=True,
        on_phase=lambda p: phase.__setitem__("now", p)))
    # asyncio.to_thread cannot cancel its worker: if this by-aoa is cancelled during
    # the wait, the pull thread runs on (holding the filelock) until it finishes --
    # harmless, and the download is not wasted, it just benefits the next run.
    while True:
        done, _ = await asyncio.wait({task}, timeout=_DB_PULL_HEARTBEAT_SECS)
        if task in done:
            break
        logger.warning(
            f"Preparing the semantic database — {phase['now']}… "
            f"({int(time.monotonic() - started)}s elapsed). AoA is waiting.")
    try:
        task.result()
    except R2Busy:
        logger.warning(
            "Another process is already downloading the semantic database; "
            "running this proof without it for now.")
    except Exception as e:
        logger.warning(
            f"Failed to prepare the semantic database ({e}); running this proof "
            "without it for now.")
    else:
        try:
            ready = (f"Semantic database ready ({semantic_db_record_count()} "
                     "records). Starting AoA.")
        except Exception:
            ready = "Semantic database ready. Starting AoA."
        logger.warning(ready)
    return False


@isabelle_remote_procedure("IsaMini.AoA")
async def IsaMini_AoA(data: tuple, connection: Connection):
    (global_context, ptree, driver, log_dir, invocation_id,
     retrieval_forking_str, interactive_retrieval_str, budget_tuple,
     goal_hash, cache_flags, task_info, enable_write_memory) = data
    # ML pairs the read-cache toggle with the L2 (Phi_Cache_DB) payload and the
    # store toggle.
    use_cache, cached_xcmd_json, store_cache = cache_flags
    # Task = (kind, payload); "usual" (empty payload) or "learning" (Isar proof).
    task_kind, task_payload = task_info
    # AoA_enable_write_memory (Isabelle declaration): when False, the write_memory
    # tool is dropped from every advertised tool set and memorize is a no-op.
    timeout_seconds, max_tool_calls, max_retries = budget_tuple

    # Environment variable AoA_LOG_DIR overrides user-provided log_dir.
    # Resolved through the connected Isabelle first: this host's os.environ is
    # frozen at server start, so an etc/settings edit only arrives this way.
    env_log_dir = await _resolve_isa_env(connection, 'AoA_LOG_DIR')
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

    logger = connection.server.logger
    pc = get_proof_cache()

    # Cache READING is gated by the AoA_use_proof_cache config (passed from ML)
    # AND skipped entirely for the test driver: snapshot tests must run the
    # model by hand (`case.run`), never short-circuit to a replayed cached proof.
    # Replaying would (a) bypass the by-hand path under test — a successful
    # replay returns before `case.run` is ever reached, a false pass — and
    # (b) after a wire-format change, a stale cached proof fails to unpack
    # mid-callback and corrupts the connection. When disabled, both levels are
    # bypassed for lookup; a finished proof is still WRITTEN on success (see L1
    # SQLite store below and the ML-side L2 Phi_Cache_DB store).
    is_test_driver = driver.split(".", 1)[0] == "test"

    # Tell the user when a newer Semantic-Embedding DB is published: an out-of-date
    # one makes AoA re-interpret and re-embed theories another machine already did,
    # at API cost.  Warns only; `pull` merges, and only when you run it.
    #
    # Called inline, not on a thread.  Inside the weekly throttle it costs ~1ms;
    # the one call a week that really probes is a single anonymous HTTPS HEAD and
    # blocks this event loop for ~0.7s.  If the origin is unreachable it blocks for
    # the 15s timeout: nothing breaks (MCP's read timeout is 300s and the REPL
    # client has none), and asyncio.to_thread would only move that wait to
    # interpreter exit, where asyncio.run joins the default executor anyway.
    #
    # Skipped under the test driver: snapshot tests must not touch the network.
    if not is_test_driver:
        # Empty DB -> block and pull it (with progress warnings) before starting;
        # present DB -> just warn if a newer snapshot is published.  _ensure_...
        # returns False after handling an empty DB, so check_update is skipped then
        # (a fresh pull already has the latest; a bare run has nothing to compare).
        if await _ensure_semantic_db(logger):
            from Isabelle_Semantic_Embedding.r2_sync import check_update
            check_update(logger.warning)   # never raises; logs at most one line

    if not use_cache or is_test_driver:
        why = ("test driver: run by hand, never replay cache" if is_test_driver
               else "AoA_use_proof_cache=false")
        logger.info(
            "[AoA-cache] lookup BYPASSED (%s) goal_hash=%s; will still store on success",
            why, goal_hash)
    else:
        logger.info(
            "[AoA-cache] lookup goal_hash=%s | sqlite_db=%s | phi_cache_json=%s",
            goal_hash, pc.db_path,
            f"present({len(cached_xcmd_json)}B)" if cached_xcmd_json else "absent")

        # Level 1: Python SQLite
        cached_ops = pc.lookup(goal_hash)
        logger.info("[AoA-cache] L1 SQLite: %s",
                    "HIT" if cached_ops is not None else "MISS")

        # Level 2: Phi_Cache_DB (from ML)
        if cached_ops is None and cached_xcmd_json:
            try:
                cached_ops = json.loads(cached_xcmd_json)
                logger.info("[AoA-cache] L2 Phi_Cache_DB: HIT (%d ops)", len(cached_ops))
            except (json.JSONDecodeError, TypeError) as e:
                cached_ops = None
                logger.warning("[AoA-cache] L2 Phi_Cache_DB: JSON parse FAILED: %r", e)
        elif cached_ops is None:
            logger.info("[AoA-cache] L2 Phi_Cache_DB: MISS (no json from ML)")

        if cached_ops is not None:
            cache_source = "SQLite" if not cached_xcmd_json or pc.lookup(goal_hash) is not None else "Phi_Cache_DB"
            ok, final_state, _ = await _replay_cached_proof(connection, cached_ops, cache_source)
            logger.info("[AoA-cache] replay from %s: %s (%d ops)",
                        cache_source, "OK" if ok else "FAILED", len(cached_ops))
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
        quit_obj = None
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
        from .task import UsualTask, LearningTask
        task_obj = (LearningTask(task_payload) if task_kind == "learning"
                    else UsualTask())
        async with drv(connection.server.logger, actual_log_path,
                       argument=argument,
                       retrieval_forking_mode=retrieval_forking,
                       interactive_retrieval=interactive_retrieval,
                       timeout_seconds=timeout_seconds,
                       max_tool_calls=max_tool_calls,
                       max_retries=max_retries,
                       # Driver config (API keys, endpoints) resolved through
                       # the connected Isabelle: fresh after every Isabelle
                       # restart, no RPC-host restart needed.
                       env=await _resolve_driver_env(connection, drv)) as session:
            # Set the Task on the runtime (via the session shim) before init/run so
            # the system prompt and initial message pick it up. Forks inherit it
            # through the shared runtime singleton.
            session.task = task_obj
            session.enable_write_memory = enable_write_memory
            # Park the Connection on the shared Runtime so every tool entry point
            # can rebind Connection.current() (see model.bind_session_context):
            # uvicorn clears the context for each MCP request, so the binding made
            # in the RPC handle_client does not reach the tool handlers.
            session.runtime.connection = connection
            # Tolerate the lookup failing: Config.lookup errors on an option that
            # is not in the ML-side registry, and `AoA_Debug` only entered it when
            # preprocess.ML gained its register_rpc_option call -- so any REPL
            # started from older ML raises here. Debugging is opt-in; falling back
            # to False costs nothing, whereas propagating would break every run.
            try:
                session.runtime.debug = bool(
                    await connection.config_lookup("AoA_Debug"))
            except Exception:
                session.runtime.debug = False
            root = Root((global_context, ptree), connection)
            await session.initialize(root)
            await session.run()
            # Final missing-lemma survey before the MAIN agent winds down —
            # mirrors the worker_end survey in Session.run (workers fire one
            # when they wind down; the top-level major never did). Without it a
            # main-agent case that proved/failed having made fewer than the
            # query-interval count of successful queries — and dispatched no
            # worker — logs ZERO surveys, losing the loop's entire signal.
            # Only when it made ≥1 successful query since the last survey (else
            # there is nothing new to report); no-op unless the survey is
            # enabled (AOA_MISSING_LEMMA_SURVEY). Runs only on natural exit:
            # if session.run() raised (timeout / cancellation) we never reach
            # here, matching worker_end's "not on cancellation" semantics.
            if session._query_calls_since_survey >= 1:
                await session.run_missing_lemma_survey("session_end")
            # LearningTask reflection on success: distil reusable experience into
            # memories. No-op for a UsualTask (see maybe_run_memorize_interaction);
            # gated on a finished proof (decision 6: proof_done fires on success).
            if root.is_proof_finished():
                await session.maybe_run_memorize_interaction("proof_done")
            quit_obj = session.quit_info
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

        # ML concludes the theorem from the state named here (`Minilang.conclude`,
        # agent_server.ML), so it must be one the kernel derived from the agent's
        # proof. `root.final_ml_state` is not: its only writer runs once at
        # `Session.initialize`, while the goal is still open, and `_skip_proof` ->
        # SORRY_END_ALL closes it with a `Skip_Proof.cheat_tac` ORACLE, which nothing
        # recomputes. Return the replay of the assembled, sorry-free op list instead.
        ok, replayed_state, replay_err = await _replay_cached_proof(
            connection, assembled, "fresh proof")
        if not ok:
            # Never fall back to `final_ml_state` -- that is the hole this closes.
            raise InternalError(
                f"The proof tree reports the proof is finished, but replaying its "
                f"own {len(assembled)} assembled operations from $init failed. "
                f"Refusing to conclude the theorem from `final_ml_state`, which is "
                f"closed by a skip_proof oracle.\n"
                f"goal_hash={goal_hash}\nreplay failed with: {replay_err}")
        logger.info("[AoA] replayed the fresh proof from $init: OK (%d ops) -> %s",
                    len(assembled), replayed_state)

        # Store only AFTER the replay succeeded: a proof that does not replay must
        # never enter the cache.
        if store_cache:
            get_proof_cache().store(goal_hash, assembled)
            logger.info("[AoA-cache] L1 SQLite STORE goal_hash=%s (%d ops) db=%s",
                        goal_hash, len(assembled), get_proof_cache().db_path)
        else:
            logger.info("[AoA-cache] L1 SQLite STORE SKIPPED (AoA_store_proof_cache=false) goal_hash=%s",
                        goal_hash)
        # Write to log directory
        if actual_log_path:
            try:
                os.makedirs(actual_log_path, exist_ok=True)
                with open(os.path.join(actual_log_path, "proof.json"), "w") as f:
                    f.write(proof_json)
            except Exception as e:
                _logger.warning(f"Failed to write proof.json: {e}")
        return (assembled, replayed_state, cost, None, None, proof_json)
    else:
        reason = quit_obj.reason if quit_obj is not None else "resource_exhausted"
        detail = quit_obj.detail if quit_obj is not None else None
        logger.info("[AoA-cache] NOT stored: proof not finished (reason=%s) goal_hash=%s",
                    reason, goal_hash)
        return (assembled, None, cost, reason, detail, None)



