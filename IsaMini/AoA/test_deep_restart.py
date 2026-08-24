#!/usr/bin/env python3
"""Standalone unit tests for the deep-restart machinery (corrupted CLI chat
history stop-loss): ``settle_quit``, ``request_deep_restart``,
``Session._deep_restart`` (state boundary + operability), the shared message
pump ``ClaudeCode._pump_response``, and the ``_sdk_loop`` bottom dispatcher
driven end-to-end over the incident scenario.

No Isabelle / no REPL / no LLM. Run directly from anywhere (it puts the
package root on ``sys.path``): ``python test_deep_restart.py``. Exits non-zero
on any failure. Same shape as ``test_session_quit.py``.
"""
import asyncio
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA import model, driver_claude_code
from IsaMini.AoA.model import (
    Session, SessionQuit, Fork_Pending, Role_Interaction, Role_Major,
    Role_Worker, ForkingMode, Interaction, InteractionChannel, Runtime,
    DeepRestart, Restart, Refresh, Surrender, TechnicalFailure,
    ResourceExhausted, TOOL_ANSWER_INDEX,
)
from IsaMini.AoA.driver_claude_code import (
    ClaudeCode, _CorruptedHistoryError, Chat_Restart)
from IsaMini.AoA.language_model_driver import _QuotaError
from IsaMini.AoA.mcp_http_server import ToolExecutor, EditResult, InteractionPrompt
from claude_agent_sdk import ResultMessage
from claude_agent_sdk.types import AssistantMessage, TextBlock

CORRUPT_400 = ("API Error: 400 The request body is not valid JSON: "
               "no low surrogate in string: line 1 column 16547 (char 16546)")

CHILD_DETAIL = "corrupted CLI chat history; the proof context is restarting"


def check(cond, msg):
    if not cond:
        print(f"FAIL: {msg}")
        sys.exit(1)


def make_session(*, parent=None, role=None, runtime=None, cls=Session):
    """A bare session with the fields the deep-restart machinery touches."""
    s = cls.__new__(cls)
    s.parent = parent
    s.role = role if role is not None else Role_Major()
    if runtime is not None:
        s.runtime = runtime
    elif parent is not None:
        s.runtime = parent.runtime
    else:
        s.runtime = Runtime()
    s._quit_info = None
    s._retry_count = 0
    s.max_retries = 5
    s.max_tool_calls = 10000
    s.timeout_seconds = 14400.0
    s._nf_pending_interaction = None
    s._channel = None
    s._executor = None
    s._owned_tasks = set()
    s.tool_call_log = []
    s.last_proof_op_time = 0.0
    s.logged = []
    s.meta = []
    s.interrupts = 0
    s.view_resets = 0
    s.log_interaction = lambda tool_name, prompt: s.logged.append(
        ("interaction", tool_name, prompt))
    s.log_tool_call = lambda tool_name, tool_input: None
    s.log_tool_response = lambda tool_name, response: s.logged.append(
        ("response", tool_name, response))
    s.log_AoA_opr = lambda message: s.logged.append(("opr", message))
    s.warn_AoA_opr = lambda message, **kw: s.logged.append(("warn", message))
    s._log_meta = lambda event, **kw: s.meta.append((event, kw))
    s._reset_view_state = lambda: setattr(s, "view_resets", s.view_resets + 1)

    async def _interrupt():
        s.interrupts += 1
    s.interrupt = _interrupt
    return s


class _Probe(Interaction):
    forking = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools = [TOOL_ANSWER_INDEX]
    async def prompt(self, indent, file):
        pass


def make_fork(parent):
    answer: asyncio.Future = asyncio.get_running_loop().create_future()
    pending = Fork_Pending(interaction=_Probe(), answer=answer)
    s = make_session(parent=parent,
                     role=Role_Interaction(pending=pending, prompt="",
                                           resume_id=None,
                                           mode=ForkingMode.FORKING_WITH_CTXT))
    return s, answer


# ---------------------------------------------------------------------------
# 1. settle_quit truth table (§11.3)
# ---------------------------------------------------------------------------

def test_settle_quit_truth_table():
    terminal = Surrender("done first")
    for newcomer in (TechnicalFailure(detail="later"), DeepRestart(detail="x"),
                     Restart(), Refresh(briefing="b")):
        s = make_session()
        s._quit_info = terminal
        s.settle_quit(newcomer)
        check(s.quit_info is terminal,
              f"terminal must survive {type(newcomer).__name__}")

    deep = DeepRestart(detail="poisoned")
    for newcomer in (TechnicalFailure(detail="child verdict"), Restart(),
                     Refresh(briefing="b"), DeepRestart(detail="again")):
        s = make_session()
        s._quit_info = deep
        s.settle_quit(newcomer)
        check(s.quit_info is deep,
              f"pending DeepRestart must survive {type(newcomer).__name__}")

    for standing in (None, Restart(), Refresh(briefing="b")):
        s = make_session()
        s._quit_info = standing
        q = DeepRestart(detail="new")
        s.settle_quit(q)
        check(s.quit_info is q,
              f"{type(standing).__name__} must be overwritten (R20/R21/R22)")

    s = make_session()
    q = Surrender("verdict")
    s.settle_quit(q)
    check(s.quit_info is q, "a clean session must accept a terminal verdict")


# ---------------------------------------------------------------------------
# 2. request_deep_restart (§11.4)
# ---------------------------------------------------------------------------

async def test_request_from_major():
    s = make_session()
    await s.request_deep_restart(detail=CORRUPT_400, cli_record="/rec")
    check(isinstance(s.quit_info, DeepRestart),
          "self-detection on the major must post DeepRestart to itself")
    check(s.quit_info.detail == CORRUPT_400, "the 400 text must ride in detail")
    check(s.interrupts == 1, "the major must be interrupted")
    check(("CORRUPTED_HISTORY_RESTART",
           {"detail": CORRUPT_400, "cli_record": "/rec"}) in s.meta,
          "the forensic meta event must be recorded with detail + cli_record")


async def test_request_from_nested_fork_finds_major_and_abandons():
    major = make_session()
    worker = make_session(parent=major, role=Role_Worker(target=None))
    fork, answer = make_fork(worker)
    await fork.request_deep_restart(detail=CORRUPT_400)
    check(isinstance(major.quit_info, DeepRestart),
          "the signal must land on the MAJOR (walking the whole parent chain)")
    check(worker.quit_info is None,
          "intermediate sessions must not be judged")
    check(isinstance(fork.quit_info, TechnicalFailure)
          and fork.quit_info.detail == CHILD_DETAIL,
          "the child must self-judge with the approved detail")
    check(answer.done() and isinstance(answer.exception(), SessionQuit),
          "the fork's answer future must be settled via the SessionQuit rail")
    check(major.interrupts == 1 and fork.interrupts == 0,
          "only the major is interrupted")
    check(any(e == "CORRUPTED_HISTORY_RESTART" for e, _ in fork.meta),
          "child detection must record the meta event too")


async def test_request_from_worker_self_judges():
    major = make_session()
    worker = make_session(parent=major, role=Role_Worker(target=None))
    await worker.request_deep_restart(detail=CORRUPT_400)
    check(isinstance(major.quit_info, DeepRestart), "signal on the major")
    check(isinstance(worker.quit_info, TechnicalFailure),
          "the worker must self-judge (弃子) — _wait_next_event carries .detail")


async def test_request_refuses_to_clobber_terminal_verdict():
    major = make_session()
    verdict = Surrender("already decided")
    major._quit_info = verdict
    fork, answer = make_fork(major)
    await fork.request_deep_restart(detail=CORRUPT_400)
    check(major.quit_info is verdict,
          "a standing terminal verdict on the major must be kept")
    check(answer.done() and isinstance(answer.exception(), SessionQuit),
          "the child must still self-judge and settle its slot")


# ---------------------------------------------------------------------------
# 3. _deep_restart: ledger preserved, teardown performed (§11.5)
# ---------------------------------------------------------------------------

class _StubRoot:
    def __init__(self):
        self.closed_subagents = 0
    async def aclose_all_subagents(self):
        self.closed_subagents += 1


async def _park(queue):
    await queue.get()


async def test_deep_restart_preserves_ledger_and_tears_down():
    s = make_session()
    s.root = _StubRoot()
    s.log_dir = "/sentinel/log_dir"
    s.total_cost_usd = 1.25
    s._cost_by_session = {"cli-1": 1.25}
    s._retry_count = 3
    s.runtime._budget_start_time = 1000.0
    s.runtime.total_tool_calls = 42
    s._quit_info = DeepRestart(detail="x")

    # A parked non-forking interaction + an owned task + a live fork task.
    ex = ToolExecutor(s)            # installs channel + back-reference
    q1, q2, q3 = asyncio.Queue(), asyncio.Queue(), asyncio.Queue()
    parked = asyncio.get_running_loop().create_task(_park(q1))
    ex._suspended_task = parked
    s._owned_tasks = {parked}
    s._nf_pending_interaction = _Probe()
    old_channel = ex._channel
    owned = asyncio.get_running_loop().create_task(_park(q2))
    s._owned_tasks.add(owned)
    live_fork = asyncio.get_running_loop().create_task(_park(q3))
    s.runtime._live_forks.add(live_fork)
    await asyncio.sleep(0)          # let the tasks start
    root_before = s.root

    await s._deep_restart()

    check(s.log_dir == "/sentinel/log_dir" and s.total_cost_usd == 1.25
          and s._cost_by_session == {"cli-1": 1.25} and s._retry_count == 3
          and s.runtime._budget_start_time == 1000.0
          and s.runtime.total_tool_calls == 42,
          "ledger/budget/retry/log-dir must ALL survive a deep restart")
    check(s.root is root_before, "the proof tree object must survive")
    check(parked.cancelled() and owned.cancelled() and live_fork.cancelled(),
          "parked task, owned task and live fork must all be cancelled")
    check(ex._suspended_task is None and s._nf_pending_interaction is None,
          "the parked interaction must be fully discarded")
    check(s._channel is not None and s._channel is not old_channel
          and ex._channel is s._channel,
          "a FRESH channel must replace the old one, on BOTH references")
    check(s.root.closed_subagents == 1, "all workers must be released")
    check(s.view_resets == 1, "the view state must be reset")
    check(s.quit_info is None,
          "a DeepRestart that arrived during teardown is served -> drained")
    check(any(kind == "opr" and m.startswith("Deep restart:")
              for kind, m in s.logged), "the approved operator line must log")


async def test_deep_restart_drain_never_eats_a_terminal_verdict():
    s = make_session()
    s.root = _StubRoot()
    verdict = Surrender("mid-teardown verdict")
    s._quit_info = verdict
    await s._deep_restart()
    check(s.quit_info is verdict,
          "the typed drain must only clear DeepRestart, never a terminal verdict")


async def test_claude_code_override_clears_conversation_id():
    s = make_session(cls=ClaudeCode)
    s.root = _StubRoot()
    s._conversation_id = "poisoned-cli-session"
    await s._deep_restart()
    check(s._conversation_id is None,
          "ClaudeCode must clear _conversation_id (the re-poisoning window)")


# ---------------------------------------------------------------------------
# 4. post-restart operability: the wedge is impossible (§11.6)
# ---------------------------------------------------------------------------

async def test_mutations_work_after_discarding_a_parked_interaction():
    s = make_session()
    ex = ToolExecutor(s)      # installs a channel on the session

    async def _asks():
        await s._channel.outbox.put(InteractionPrompt(_Probe(), "answer me"))
        await s._channel.inbox.get()

    text, is_error = await ex._run_tool_via_channel(_asks(), s, is_edit=True)
    check(ex._suspended_task is not None and text == "answer me",
          "precondition: a tool task is parked on a non-forking interaction")

    async def _noop():
        pass
    noop_coro = _noop()
    refused, refused_err = await ex._run_tool_via_channel(noop_coro, s, is_edit=True)
    check(refused_err and "operation is in progress" in refused,
          "precondition: mutations are refused while parked")
    noop_coro.close()      # the refusal path never starts the coroutine

    await s.discard_parked_interaction()

    async def _edits():
        await s._channel.outbox.put(EditResult("edited fine", False))
    text2, err2 = await ex._run_tool_via_channel(_edits(), s, is_edit=True)
    check(not err2 and text2 == "edited fine",
          "after the discard, the next mutation must run normally (no wedge)")
    check(ex._channel is s._channel,
          "executor and session must see the SAME (fresh) channel")


# ---------------------------------------------------------------------------
# 5. the shared pump (§11.2)
# ---------------------------------------------------------------------------

class FakeClient:
    def __init__(self, messages):
        self._messages = list(messages)
    async def receive_response(self):
        for m in self._messages:
            yield m
    async def query(self, prompt):
        pass
    async def interrupt(self):
        pass


def _result(**kw):
    base = dict(subtype="success", duration_ms=100, duration_api_ms=0,
                is_error=False, num_turns=1, session_id="cli-1",
                total_cost_usd=0.2748,
                usage={"input_tokens": 3136, "output_tokens": 1166,
                       "cache_read_input_tokens": 85760,
                       "cache_creation_input_tokens": 18653})
    base.update(kw)
    return ResultMessage(**base)


def _assistant(error=None, text=None, model="m"):
    content = [TextBlock(text=text)] if text else []
    return AssistantMessage(content=content, model=model, error=error)


def make_pump_driver():
    d = make_session(cls=ClaudeCode)
    d._model_time_start = None
    d.total_model_time = 0.0
    d.total_cost_usd = 0.0
    d.total_input_tokens = 0
    d.total_output_tokens = 0
    d.total_cache_read_input_tokens = 0
    d.total_cache_creation_input_tokens = 0
    d._cost_by_session = {}
    d.model_outputs = []
    d.log_model_output = lambda t: d.model_outputs.append(t)
    d.log_model_thinking = lambda t: None
    d.log_cost = lambda m: None
    return d


async def test_pump_defers_corruption_and_keeps_the_accounting():
    d = make_pump_driver()
    client = FakeClient([
        _assistant(error="unknown", text=CORRUPT_400),
        _result(is_error=True, subtype="error_during_execution", result=None,
                total_cost_usd=0.2748),
    ])
    try:
        await d._pump_response(client, d)
        check(False, "the pump must raise the deferred Chat_Restart after the stream")
    except _CorruptedHistoryError:
        pass
    check(abs(d.total_cost_usd - 0.2748) < 1e-9,
          "the trailing ResultMessage's accounting must land (the incident's "
          "$0.2748 / 108,715 tokens used to vanish)")
    check(d.total_input_tokens == 3136 and d.total_output_tokens == 1166,
          "token usage must land too")
    check(all(CORRUPT_400 not in t for t in d.model_outputs),
          "the synthetic notice must NOT be logged as model output")


async def test_pump_healthy_stream_and_fork_split():
    parent = make_pump_driver()
    fork = make_pump_driver()
    results = []
    client = FakeClient([
        _assistant(text="thinking about the goal"),
        _result(),
    ])
    await parent._pump_response(
        client, fork, tag="[f]", on_result=lambda m: results.append(m.subtype))
    check(fork.model_outputs == ["[f] thinking about the goal"],
          "logs (with tag) must land on the SINK (the fork)")
    check(parent.model_outputs == [] and abs(parent.total_cost_usd - 0.2748) < 1e-9
          and fork.total_cost_usd == 0.0,
          "dollars must land on SELF (the parent), never the sink")
    check(results == ["success"], "on_result must fire after accounting")


async def test_pump_quota_still_raises_immediately():
    d = make_pump_driver()
    client = FakeClient([
        _assistant(error="unknown", text="You've hit your limit until 3pm")])
    try:
        await d._pump_response(client, d)
        check(False, "a quota classification must raise immediately")
    except _QuotaError:
        pass


async def test_pump_corruption_outranks_a_later_quota_text():
    """A quota/transient notice AFTER the corruption notice in the same stream
    must not displace it: the 20-min wait-and-rebuild it asks for is doomed on
    a poisoned session."""
    d = make_pump_driver()
    client = FakeClient([
        _assistant(error="unknown", text=CORRUPT_400),
        _assistant(error="unknown", text="You've hit your limit until 3pm"),
    ])
    try:
        await d._pump_response(client, d)
        check(False, "the cached corruption must be raised, and immediately")
    except _CorruptedHistoryError:
        pass
    except _QuotaError:
        check(False, "the later quota text displaced the cached corruption")


async def test_run_fork_abandon_arm():
    """§11.2 both loops: drive the REAL _run_fork over a corrupted stream and
    watch the abandon (弃子) end to end — self-judgment settles the answer via
    the SessionQuit rail, the DeepRestart lands on the major."""
    saved_client = driver_claude_code.ClaudeSDKClient
    saved_make_fork = ClaudeCode._make_fork
    driver_claude_code.ClaudeSDKClient = FakeSDKClient
    forks = []

    def _stub_fork(parent, role):
        f = make_session(parent=parent, role=role, cls=ClaudeCode)
        f._mcp_url = "http://stub"
        f._fork_name = "main.fork_1"
        f._model_time_start = None
        f.total_model_time = 0.0
        f.total_isabelle_time = 0.0
        f.total_quota_wait_time = 0.0
        f._interrupt_tasks = set()
        f._http_server = None
        f._session_id = None
        f._client = None
        f.log_model_output = lambda t: None
        f.log_model_thinking = lambda t: None

        async def _init(root):
            pass
        f.initialize = _init
        forks.append(f)
        return f
    ClaudeCode._make_fork = classmethod(
        lambda cls, parent, role=None: _stub_fork(parent, role))
    try:
        d = make_pump_driver()
        d.root = _StubRoot()
        d._model = "claude-test"
        d._conversation_id = None
        d.working_dir = "/tmp/agent_AoA_test"
        d._http_server = None
        d._client = None
        d.total_isabelle_time = 0.0
        d.total_quota_wait_time = 0.0
        d.system_prompt = lambda: None
        d._role_allowed_tools = lambda: []
        FakeSDKClient.script = [_corrupt_turn()]

        class _AbandonProbe(_Probe):
            answer_tool_name = TOOL_ANSWER_INDEX

        try:
            await d._run_fork(_AbandonProbe(), "prompt text")
            check(False, "_run_fork must end via the SessionQuit rail")
        except SessionQuit as e:
            check(isinstance(e.quit_info, TechnicalFailure)
                  and e.quit_info.detail == CHILD_DETAIL,
                  "the fork must self-judge with the approved detail")
        check(isinstance(d.quit_info, DeepRestart),
              "the abandon must post DeepRestart on the major")
        check(forks and forks[0]._client is None,
              "the finally must clear the fork's client")
        check(any(e == "CORRUPTED_HISTORY_RESTART" for e, _ in forks[0].meta),
              "the fork's detection must leave the forensic meta event")
    finally:
        driver_claude_code.ClaudeSDKClient = saved_client
        ClaudeCode._make_fork = saved_make_fork


# ---------------------------------------------------------------------------
# 6. the bottom dispatcher, end to end over the incident scenario (§11.7)
# ---------------------------------------------------------------------------

class FakeSDKClient:
    """Stands in for ClaudeSDKClient inside _sdk_loop. Each connection pops
    the next scripted message list."""
    script: list = []
    connections = 0

    def __init__(self, options=None):
        pass
    async def __aenter__(self):
        FakeSDKClient.connections += 1
        self._messages = FakeSDKClient.script.pop(0)
        return self
    async def __aexit__(self, *a):
        return False
    async def query(self, prompt):
        pass
    async def interrupt(self):
        pass
    async def receive_response(self):
        for m in self._messages:
            yield m


def make_loop_driver(*, max_retries):
    d = make_pump_driver()
    d.max_retries = max_retries
    d.root = _StubRoot()
    d.options = None
    d._client = None
    d._refresh_summary = None
    d._interrupt_tasks = set()
    d._conversation_id = "cli-old"
    d.working_dir = "/tmp/agent_AoA_test"
    d.refresh_YAML = lambda: None
    d.log_proof = lambda: None
    d.log_budget_exhausted = lambda reason: None
    d.deep_restarts = 0
    _orig = ClaudeCode._deep_restart

    async def _counted_deep_restart():
        d.deep_restarts += 1
        await _orig(d)
    d._deep_restart = _counted_deep_restart

    async def _initial_prompt():
        return "prove it"
    d.initial_prompt = _initial_prompt
    d.proof_scope_unfinished_nodes = lambda: {"1"}
    # interrupt: use the REAL ClaudeCode.interrupt (fire-and-forget path).
    del d.interrupt
    return d


def _corrupt_turn():
    return [_assistant(error="unknown", text=CORRUPT_400),
            _result(is_error=True, subtype="error_during_execution",
                    result=None)]


async def test_incident_scenario_bounded_by_retries():
    """8/8 burns cannot recur: each deep restart charges one retry and the
    retry limit ends the run as ResourceExhausted."""
    saved = driver_claude_code.ClaudeSDKClient
    driver_claude_code.ClaudeSDKClient = FakeSDKClient
    try:
        d = make_loop_driver(max_retries=2)
        FakeSDKClient.script = [_corrupt_turn(), _corrupt_turn(), _corrupt_turn()]
        FakeSDKClient.connections = 0
        await d._sdk_loop()
        check(d._retry_count == 2, "every deep restart must charge one retry")
        check(d.deep_restarts == 1,
              "restart happens only while check_budget still allows it")
        check(FakeSDKClient.connections == 2,
              "a fresh CLI conversation per restart, stop at the limit")
        check(isinstance(d.quit_info, ResourceExhausted),
              "the run must end as ResourceExhausted(retry limit), not hang")
        check(d._conversation_id is None,
              "the ClaudeCode override must have cleared _conversation_id")
        check(any(kind == "warn" and "restarting context" in m
                  for kind, m in d.logged),
              "the user warning fires only when a restart really happens")
        # meta trail: one CORRUPTED_HISTORY_RESTART per detection, one
        # DEEP_RESTART per PERFORMED restart (detections ≠ performances)
        check(sum(1 for e, _ in d.meta if e == "CORRUPTED_HISTORY_RESTART") == 2,
              "every detection must leave a forensic meta event")
        check(sum(1 for e, _ in d.meta if e == "DEEP_RESTART") == 1,
              "every performed deep restart must leave a DEEP_RESTART event")
    finally:
        driver_claude_code.ClaudeSDKClient = saved


async def test_standing_terminal_verdict_survives_corruption():
    saved = driver_claude_code.ClaudeSDKClient
    driver_claude_code.ClaudeSDKClient = FakeSDKClient
    try:
        d = make_loop_driver(max_retries=5)
        verdict = Surrender("decided before the notice")
        d._quit_info = verdict
        FakeSDKClient.script = [_corrupt_turn()]
        FakeSDKClient.connections = 0
        await d._sdk_loop()
        check(d.quit_info is verdict,
              "a standing terminal verdict must survive a corruption notice")
        check(d.deep_restarts == 0, "no restart on a terminal-verdict run")
    finally:
        driver_claude_code.ClaudeSDKClient = saved


def main():
    test_settle_quit_truth_table()
    asyncio.run(test_request_from_major())
    asyncio.run(test_request_from_nested_fork_finds_major_and_abandons())
    asyncio.run(test_request_from_worker_self_judges())
    asyncio.run(test_request_refuses_to_clobber_terminal_verdict())
    asyncio.run(test_deep_restart_preserves_ledger_and_tears_down())
    asyncio.run(test_deep_restart_drain_never_eats_a_terminal_verdict())
    asyncio.run(test_claude_code_override_clears_conversation_id())
    asyncio.run(test_mutations_work_after_discarding_a_parked_interaction())
    asyncio.run(test_pump_defers_corruption_and_keeps_the_accounting())
    asyncio.run(test_pump_healthy_stream_and_fork_split())
    asyncio.run(test_pump_quota_still_raises_immediately())
    asyncio.run(test_pump_corruption_outranks_a_later_quota_text())
    asyncio.run(test_run_fork_abandon_arm())
    asyncio.run(test_incident_scenario_bounded_by_retries())
    asyncio.run(test_standing_terminal_verdict_survives_corruption())
    print("OK — all deep-restart tests passed")


if __name__ == "__main__":
    main()
