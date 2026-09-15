from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import *
from .model import interrupts_are_cancellations
from . import usage_count
from typing import Any
import json
import logging as _logging
_logger = _logging.getLogger(__name__)

# A per-op ML time on the wire is (thread CPU ms, wall ms), the pair nested in
# one slot as at every wire carrying a Phi_Proof_Store.times.  Summed
# element-wise: Python `+` on tuples concatenates.
_ZERO_TIMES_MS: tuple[int, int] = (0, 0)

def _add_times_ms(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] + b[0], a[1] + b[1])

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
# interface, but the driver has never been exercised against the live
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
@interrupts_are_cancellations
async def _query_by_name_rpc(arg: tuple[int, str], connection: Connection) -> tuple[str, bool]:
    """Query entity by kind and name — reuses the core of the MCP query tool."""
    from .retrieval import _query_entity_core
    from Isabelle_RPC_Host.universal_key import EntityKind
    kind_int, name = arg
    tag = EntityKind(kind_int)
    text, is_error, _uk = await _query_entity_core(connection, tag, name)
    return (text, is_error)

async def _replay_assembled_proof(connection: Connection, packed_ops: list[Any],
                                  source: str = "") -> tuple[bool, str | None, str | None, tuple[int, int]]:
    """Replay a freshly found proof by feeding its assembled operations through
    proof_opr callbacks.

    It is the only path whose resulting state the Isabelle kernel has actually
    derived from the proof, so it is what the returned theorem must be concluded
    from.  (Store-hit replay no longer comes through here: level-0 lookup and
    replay are entirely ML-side now.)

    Returns (success, final_state_name, error, replayed_ms): replayed_ms is the
    (thread CPU ms, wall ms) sum of the per-op ML execution times (D61)
    measured over exactly this — the final assembled stream, run once, in
    order — which is what a future replay of the recorded proof will spend on
    its op stream.
    """
    await connection.callback("IsaMini.set_replay_mode", True)
    replayed_ms = _ZERO_TIMES_MS
    peer_alive = True
    try:
        state_name = "$init"
        for i, packed_op in enumerate(packed_ops):
            dest_name = f"$replay_{i+1}"
            (_msgs, _flat_goal, times_ms) = await connection.callback(
                "IsaMini.proof_opr", (state_name, dest_name, packed_op))
            replayed_ms = _add_times_ms(replayed_ms, times_ms)
            state_name = dest_name
        return (True, state_name, None, replayed_ms)
    except asyncio.CancelledError:
        # Isabelle unwound with the interrupt and closed the connection:
        # nothing may call back, and the cancellation must not be replaced
        # by that failure
        peer_alive = False
        raise
    except (ConnectionError, EOFError) as e:
        peer_alive = False
        connection.server.logger.info(f"[AoA] Proof replay failed ({source}): {e}")
        return (False, None, f"{type(e).__name__}: {e}", replayed_ms)
    except Exception as e:
        connection.server.logger.info(f"[AoA] Proof replay failed ({source}): {e}")
        return (False, None, f"{type(e).__name__}: {e}", replayed_ms)
    finally:
        if peer_alive:
            try:
                await connection.callback("IsaMini.set_replay_mode", False)
            except Exception:
                pass    # a dead peer must not replace the replay's verdict

# The L19 empty-DB warning fires at most once per RPC-host process: the check
# itself runs (cheaply) at every `by aoa`, but a user who has seen the install
# hint does not need it again on every proof of the session.
_warned_empty_semantic_db = False


async def _ensure_semantic_db(connection) -> None:
    """Warn -- once per process -- when the layered semantic database is empty.

    A pure check (SEMANTIC_DB_LAYERED_PLAN L19): no download, no heartbeat, no
    blocking.  There is no automatic installation anywhere -- conda users get
    the `isabelle-semantic-data` payload as a package dependency, everyone else
    installs it explicitly with `isabelle-semantics pull` -- so an empty layered
    DB means the user has not installed it, and AoA runs bare after saying so.
    The warning branches on whether this environment is conda-managed
    (`sys.prefix/conda-meta` -- filesystem truth, activation-independent).

    Never raises, and the warning is best-effort (`Connection.warning` writes to
    the host logger before the RPC send): a missing or unreadable DB must never
    take down the proof RPC.
    """
    global _warned_empty_semantic_db
    if _warned_empty_semantic_db:
        return
    logger = connection.server.logger

    async def _warn(msg: str) -> None:
        try:
            await connection.warning(msg)
        except Exception as e:
            logger.debug(f"warning did not reach Isabelle: {e}")

    try:
        from Isabelle_Semantic_Embedding.snapshot_sync import semantic_db_is_empty
        empty = semantic_db_is_empty()
    except Exception as e:
        _warned_empty_semantic_db = True
        await _warn(
            f"Could not read the local semantic database ({e}) — it may be "
            "corrupt. Running this proof without it; check with "
            "'isabelle-semantics fsck'.")
        return
    if not empty:
        return
    _warned_empty_semantic_db = True
    if os.path.isdir(os.path.join(sys.prefix, "conda-meta")):
        await _warn(
            "No pre-built semantic database is installed on this machine — AoA "
            "will run without it. Install it into this environment with:\n"
            "    conda install -c https://conda.qiyuan.me isabelle-semantic-data")
    else:
        await _warn(
            "No pre-built semantic database is installed on this machine — AoA "
            "will run without it. Install it with:\n"
            "    isabelle-semantics pull")


@isabelle_remote_procedure("IsaMini.AoA")
@interrupts_are_cancellations
async def IsaMini_AoA(data: tuple, connection: Connection):
    (global_context, ptree, driver, log_dir, invocation_id,
     retrieval_forking_str, interactive_retrieval_str, budget_tuple,
     task_info, enable_write_memory) = data
    # Task = (kind, payload); "usual" (empty payload) or "learning" (Isar proof).
    task_kind, task_payload = task_info
    # AoA_enable_write_memory (Isabelle declaration): when False, the write_memory
    # tool is dropped from every advertised tool set and memorize is a no-op.
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

    # The nine agent_cost numbers.  The wire's stats tuple has a tenth element —
    # assembled_isabelle_time as (thread CPU ms, wall ms) (D61) — appended at
    # the return points below (the final stream's verification-replay sum;
    # zero when nothing assembled).
    zero_cost = (0, 0, 0, 0, 0.0, 0, 0.0, 0.0, 0.0)

    logger = connection.server.logger

    # All proof-store logic lives on the ML side now (level-0 lookup in
    # run_AoA/hammer_or_AoA, L1 served by IsaMini.proof_store).  The test-driver
    # test below only gates the semantic-DB startup checks.
    is_test_driver = driver.split(".", 1)[0] == "test"

    # An empty layered semantic DB warns once per process and AoA runs bare
    # (L19: no automatic installation anywhere).  A cheap O(1) check, no
    # network.  Skipped under the test driver: snapshot tests must stay silent.
    if not is_test_driver:
        await _ensure_semantic_db(connection)
        # The interpretation policy shell: at most ONE startup check per
        # `by aoa` (none once the user has declined it for the session) --
        # gate, dry run over this proof's context (an
        # as-is root, so locale-local facts are seen) and its ancestor cone,
        # then the threshold policy: small updates run silently, big ones ask
        # (the run itself never asks again -- AoA's query-time lookups pass
        # interpret_in_auto_embed=False in model.py; a per-call parameter, so
        # nothing sticks to the connection-cached store).
        # Best-effort like the check above: a broken semantic DB must never
        # take down the proof RPC.
        try:
            from Isabelle_Semantic_Embedding.semantics import update_interpretations
            await update_interpretations(connection, ask_user=True)
        except Exception as e:
            logger.warning(f"[AoA] semantic interpretation startup check failed: {e}")

    # --- Full agent run ---
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
        # Past the cache, about to enter the agent.  Sits inside this `else`, so
        # the test driver -- handled by the branch above -- reports nothing.
        # Note this says "entered the agent", NOT "spent model tokens": a user
        # who has not logged in to their model provider still gets here.
        usage_count.report(usage_count.EVENT_AGENT)
        async with drv(connection.server.logger, actual_log_path,
                       argument=argument,
                       retrieval_forking_mode=retrieval_forking,
                       interactive_retrieval=interactive_retrieval,
                       timeout_seconds=timeout_seconds,
                       max_tool_calls=max_tool_calls,
                       max_retries=max_retries) as session:
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
            # mirrors the worker_end survey in Session.run. Without it a
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
            # gated on a finished proof: proof_done fires only on success.
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
        # ML concludes the theorem from the state named here (`Minilang.conclude`,
        # agent_server.ML), so it must be one the kernel derived from the agent's
        # proof. `root.final_ml_state` is not: its only writer runs once at
        # `Session.initialize`, while the goal is still open, and `_skip_proof` ->
        # SORRY_END_ALL closes it with a `Skip_Proof.cheat_tac` ORACLE, which nothing
        # recomputes. Return the replay of the assembled, sorry-free op list instead.
        ok, replayed_state, replay_err, replayed_ms = await _replay_assembled_proof(
            connection, assembled, "fresh proof")
        if not ok:
            # Never fall back to `final_ml_state` -- that is the hole this closes.
            raise InternalError(
                f"The proof tree reports the proof is finished, but replaying its "
                f"own {len(assembled)} assembled operations from $init failed. "
                f"Refusing to conclude the theorem from `final_ml_state`, which is "
                f"closed by a skip_proof oracle.\n"
                f"invocation_id={invocation_id}\nreplay failed with: {replay_err}")
        logger.info("[AoA] replayed the fresh proof from $init: OK (%d ops, thread_cpu=%d ms wall=%d ms) -> %s",
                    len(assembled), replayed_ms[0], replayed_ms[1], replayed_state)

        # Write to log directory
        if actual_log_path:
            try:
                os.makedirs(actual_log_path, exist_ok=True)
                with open(os.path.join(actual_log_path, "proof.json"), "w") as f:
                    f.write(json.dumps(assembled))
            except Exception as e:
                _logger.warning(f"Failed to write proof.json: {e}")
        return (assembled, replayed_state, cost + (replayed_ms,), None, None)
    else:
        reason = quit_obj.reason if quit_obj is not None else "resource_exhausted"
        detail = quit_obj.detail if quit_obj is not None else None
        logger.info("[AoA] proof not finished (reason=%s)", reason)
        return (assembled, None, cost + (_ZERO_TIMES_MS,), reason, detail)



