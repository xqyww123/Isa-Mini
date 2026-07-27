#!/usr/bin/env python3
"""Standalone unit tests for the ``SessionQuit`` rail: what happens to an
interaction fork whose session acquires a terminal ``quit_info`` while the fork
is still waiting for an answer.

No Isabelle / no REPL / no LLM. Run directly from anywhere (it puts the package
root on ``sys.path``):  ``python test_session_quit.py``. Exits non-zero on any
failure. Same shape as ``test_loop_restart_detection.py``, and like it NOT
picked up by ``test_AoA.py`` -- run it explicitly.

Three groups:
  1. ``Session.quit_info``'s setter settles an unanswered fork slot with a
     ``SessionQuit`` carrying the reason -- and only for terminal values.
  2. The two work boundaries (``ToolExecutor.execute`` and
     ``_query_tool_logic``) stop a ``SessionQuit``, translate it back to
     ``quit_info`` on the caller, and return it as a tool error -- without
     reaching the ``except Exception`` arm below them (whose first act is
     ``sys.exit(1)`` under AoA_Debug).
  3. ``_shared_budget_exhausted_reason`` agrees with ``check_budget`` on the two
     run-wide dimensions and excludes the per-session retry count, and the two
     wind-down hooks use it to skip a fork that could never answer.
"""
import asyncio
import os
import sys
import types

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA import model, retrieval, mcp_http_server
from IsaMini.AoA.model import (
    Session, SessionQuit, Fork_Pending, Role_Interaction, Role_Major,
    ForkingMode, Interaction, ResourceExhausted, TechnicalFailure, Restart,
    Refresh, InteractiveRetrievalMode, TOOL_ANSWER_INDEX,
)
from IsaMini.AoA.mcp_http_server import ToolExecutor


def check(cond, msg):
    if not cond:
        print(f"FAIL: {msg}")
        sys.exit(1)


def make_runtime(*, tool_calls=0, start_time=None, debug=False):
    return types.SimpleNamespace(
        total_tool_calls=tool_calls, _budget_start_time=start_time,
        connection=None, debug=debug)


def make_session(*, role=None, runtime=None):
    """A bare Session with only the fields these tests read (bypasses __init__).

    ``log_interaction`` / the log_* family are stubbed out: they would need a
    whole log directory, and what they record is not under test here (the calls
    themselves are, so they are recorded in ``s.logged``).
    """
    s = Session.__new__(Session)
    s.parent = None
    s.role = role if role is not None else Role_Major()
    s.runtime = runtime if runtime is not None else make_runtime()
    s._quit_info = None
    s._nf_pending_interaction = None
    s._repeat_sig = None
    s._repeat_count = 0
    s._retry_count = 0
    s.max_retries = 3
    s.max_tool_calls = 500
    s.timeout_seconds = 7200.0
    s.tool_call_log = []
    s.last_proof_op_time = 0.0
    s.logged = []
    s.log_interaction = lambda tool_name, prompt: s.logged.append(
        ("interaction", tool_name, prompt))
    s.log_tool_call = lambda tool_name, tool_input: s.logged.append(
        ("call", tool_name, tool_input))
    s.log_tool_response = lambda tool_name, response: s.logged.append(
        ("response", tool_name, response))
    s.log_AoA_opr = lambda message: s.logged.append(("opr", message))
    s.warn_AoA_opr = lambda message, **kw: s.logged.append(("warn", message))
    s._log_meta = lambda *a, **kw: None
    return s


class _Probe(Interaction):
    """A minimal interaction; only its identity and allowed tools matter here."""
    forking = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools = [TOOL_ANSWER_INDEX]
    async def prompt(self, indent, file):
        pass


def make_fork(*, runtime=None):
    """A fork session with an unanswered slot, plus the slot itself.
    Must be called from inside a running loop (the slot is an asyncio.Future)."""
    answer: asyncio.Future = asyncio.get_running_loop().create_future()
    pending = Fork_Pending(interaction=_Probe(), answer=answer)
    s = make_session(role=Role_Interaction(pending=pending, prompt="", resume_id=None,
                                           mode=ForkingMode.FORKING_WITH_CTXT),
                     runtime=runtime)
    s.parent = Session.__new__(Session)     # a fork is never major
    return s, answer


# ---------------------------------------------------------------------------
# 1. the setter
# ---------------------------------------------------------------------------

async def test_setter_settles_unanswered_fork():
    fork, answer = make_fork()
    q = ResourceExhausted("timeout (7278s > 7200s)")
    fork.quit_info = q

    check(answer.done(), "a terminal quit_info must settle the unanswered slot")
    try:
        answer.result()
        check(False, "the settled slot must raise, not return a value")
    except SessionQuit as e:
        check(e.quit_info is q, "SessionQuit must carry the very quit_info that was set")
        check(str(e) == "timeout (7278s > 7200s)",
              f"SessionQuit's message must not be empty; got {str(e)!r}")
    check(fork.quit_info is q, "the value must still be readable back")
    check(any(kind == "interaction" and "settled without an answer" in prompt
              for kind, _tool, prompt in fork.logged),
          "settling must leave a trace in interaction.yaml")


async def test_setter_ignores_non_terminal_and_none():
    for q in (Restart(), Refresh(briefing="x"), None):
        fork, answer = make_fork()
        fork.quit_info = q
        check(not answer.done(),
              f"{type(q).__name__} is not terminal and must not settle the slot")
        check(fork.quit_info is q, "the value must still be stored")


async def test_setter_does_not_disturb_an_answered_fork():
    fork, answer = make_fork()
    answer.set_result("the real answer")
    fork.quit_info = TechnicalFailure(detail="something broke")
    check(answer.result() == "the real answer",
          "an already-answered slot must be left alone (set_exception would raise)")


def test_setter_is_a_no_op_off_the_fork_path():
    """Workers and the planner have no slot; the setter must just store."""
    s = make_session()
    q = ResourceExhausted("tool call limit (500 >= 500)")
    s.quit_info = q
    check(s.quit_info is q, "a non-fork session must still record quit_info")
    check(s.logged == [], "a non-fork session must not log a fork settlement")


async def test_setter_settles_a_nested_fork_in_turn():
    """A retrieval fork nested inside a memorize fork: settling the inner one
    lands on the outer via the boundary, whose write-back re-enters the setter."""
    outer, outer_answer = make_fork()
    outer.quit_info = TechnicalFailure(detail="inner blew up")
    check(outer_answer.done(), "the outer fork must be settled by the write-back too")
    check(isinstance(outer_answer.exception(), SessionQuit),   # also marks it retrieved
          "the outer slot must carry a SessionQuit")


async def _setter_group():
    await test_setter_settles_unanswered_fork()
    await test_setter_ignores_non_terminal_and_none()
    await test_setter_does_not_disturb_an_answered_fork()
    await test_setter_settles_a_nested_fork_in_turn()


# ---------------------------------------------------------------------------
# 2. the two work boundaries
# ---------------------------------------------------------------------------

def make_executor(session):
    ex = ToolExecutor.__new__(ToolExecutor)
    ex._session = session
    ex._suspended_task = None
    return ex


async def _run_execute_boundary(*, caller_quit_info, thrown):
    """Drive ToolExecutor.execute over a tool whose logic raises SessionQuit."""
    caller = make_session(runtime=make_runtime(debug=True))   # debug: sys.exit if it falls through
    caller._quit_info = caller_quit_info
    ex = make_executor(caller)

    async def _boom(session, args):
        raise SessionQuit(thrown)

    orig = mcp_http_server._report_tool_logic
    mcp_http_server._report_tool_logic = _boom
    try:
        return caller, await ex.execute("report", {})
    finally:
        mcp_http_server._report_tool_logic = orig


async def _run_query_boundary(*, caller_quit_info, thrown):
    """Drive _query_tool_logic over a search whose fork raises SessionQuit."""
    caller = make_session(runtime=make_runtime(debug=True))
    caller._quit_info = caller_quit_info
    caller.interactive_retrieval = InteractiveRetrievalMode.NO

    async def _boom(session, queries, override_state):
        raise SessionQuit(thrown)

    orig = retrieval._semantic_search_direct
    retrieval._semantic_search_direct = _boom
    try:
        return caller, await retrieval._query_tool_logic(
            caller, {"queries": [{"term_patterns": ["x"]}]})
    finally:
        retrieval._semantic_search_direct = orig


def test_boundaries_translate_back_to_state():
    for label, run in (("execute", _run_execute_boundary),
                       ("query", _run_query_boundary)):
        q = ResourceExhausted("timeout (7278s > 7200s)")
        caller, (result, is_error) = asyncio.run(
            run(caller_quit_info=None, thrown=q))
        check(is_error, f"{label}: a SessionQuit must be reported as a tool error")
        check(result == "timeout (7278s > 7200s)",
              f"{label}: the message must be the reason; got {result!r}")
        check(caller.quit_info is q,
              f"{label}: the reason must be written back onto the caller")
        check(any(kind == "response" and "resource_exhausted" in resp
                  for kind, _tool, resp in caller.logged),
              f"{label}: the boundary must log the tool response")


def test_boundaries_do_not_clobber_a_terminal_quit_info():
    """The shared sub-rule: terminal wins, non-terminal is overwritten."""
    for label, run in (("execute", _run_execute_boundary),
                       ("query", _run_query_boundary)):
        already = TechnicalFailure(detail="I stopped first")
        caller, _ = asyncio.run(run(caller_quit_info=already,
                                    thrown=ResourceExhausted("later")))
        check(caller.quit_info is already,
              f"{label}: an existing TERMINAL quit_info must not be overwritten")

        pending = Restart()
        newer = ResourceExhausted("later")
        caller, _ = asyncio.run(run(caller_quit_info=pending, thrown=newer))
        check(caller.quit_info is newer,
              f"{label}: a non-terminal Restart MUST be overwritten")


# ---------------------------------------------------------------------------
# 3. _shared_budget_exhausted_reason and the two wind-down guards
# ---------------------------------------------------------------------------

def test_shared_budget_matches_check_budget():
    from time import time as now

    # (label, runtime kwargs, retry_count, want_shared, want_check_budget)
    cases = [
        ("nothing exhausted",   dict(),                                 0, False, False),
        ("tool calls",          dict(tool_calls=500),                   0, True,  True),
        ("timeout",             dict(start_time=now() - 10_000),        0, True,  True),
        ("retries only",        dict(),                                 3, False, True),
    ]
    for label, rt, retries, want_shared, want_cb in cases:
        s = make_session(runtime=make_runtime(**rt))
        s._retry_count = retries
        s.log_budget_exhausted = lambda reason: None
        got_shared = s._shared_budget_exhausted_reason() is not None
        check(got_shared == want_shared,
              f"{label}: _shared_budget_exhausted_reason want {want_shared}, got {got_shared}")
        got_cb = s.check_budget()
        check(got_cb == want_cb,
              f"{label}: check_budget want {want_cb}, got {got_cb}")


def _make_hook_session(*, runtime, role=None):
    from IsaMini.AoA.task import LearningTask
    s = make_session(role=role, runtime=runtime)
    s.launched = []
    async def _launch(interaction):
        s.launched.append(type(interaction).__name__)
        return []
    s.launch_interaction = _launch
    s._missing_lemma_survey_interval = 5
    s._query_calls_since_survey = 3
    s.log_missing_lemmas = lambda trigger, lemmas: None
    s.enable_write_memory = True
    s.task = LearningTask.__new__(LearningTask)
    return s


def test_wind_down_hooks_skip_only_on_shared_budget():
    # (label, runtime kwargs, retry_count, should_ask)
    cases = [
        ("budget intact (e.g. Surrender/Refute)", dict(),                          0, True),
        ("retry limit only",                      dict(),                          9, True),
        ("tool-call budget gone",                 dict(tool_calls=500),            0, False),
        ("wall-clock gone",                       dict(start_time=1.0),            0, False),
    ]
    for label, rt, retries, should_ask in cases:
        for hook in ("run_missing_lemma_survey", "maybe_run_memorize_interaction"):
            s = _make_hook_session(runtime=make_runtime(**rt))
            s._retry_count = retries
            asyncio.run(getattr(s, hook)("worker_end"))
            asked = bool(s.launched)
            check(asked == should_ask,
                  f"{hook} / {label}: want asked={should_ask}, got {asked}")


def test_wind_down_hooks_absorb_session_quit():
    for hook, want_log in (("run_missing_lemma_survey", "warn"),
                           ("maybe_run_memorize_interaction", "opr")):
        s = _make_hook_session(runtime=make_runtime())
        async def _boom(interaction):
            raise SessionQuit(ResourceExhausted("timeout (7278s > 7200s)"))
        s.launch_interaction = _boom
        asyncio.run(getattr(s, hook)("worker_end"))     # must NOT propagate
        check(any(entry[0] == want_log and "skipped" in entry[1] for entry in s.logged),
              f"{hook}: a SessionQuit must be logged and dropped, not propagated")


def test_memorize_still_propagates_real_failures():
    """§4.4/D3: only SessionQuit is absorbed; a real bug must still surface."""
    s = _make_hook_session(runtime=make_runtime())
    async def _boom(interaction):
        raise RuntimeError("memory subsystem bug")
    s.launch_interaction = _boom
    try:
        asyncio.run(s.maybe_run_memorize_interaction("worker_end"))
        check(False, "a non-SessionQuit failure must still propagate out of memorize")
    except RuntimeError:
        pass


def main():
    asyncio.run(_setter_group())
    test_setter_is_a_no_op_off_the_fork_path()
    test_boundaries_translate_back_to_state()
    test_boundaries_do_not_clobber_a_terminal_quit_info()
    test_shared_budget_matches_check_budget()
    test_wind_down_hooks_skip_only_on_shared_budget()
    test_wind_down_hooks_absorb_session_quit()
    test_memorize_still_propagates_real_failures()
    print("OK — all SessionQuit tests passed")


if __name__ == "__main__":
    main()
