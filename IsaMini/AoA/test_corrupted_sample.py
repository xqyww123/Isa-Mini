#!/usr/bin/env python3
"""Standalone unit tests for the API drivers' entry validation of corrupted
samples (lone UTF-16 surrogates in a model response): ``_validate_sample`` /
``_checked_chat``, the ``(_CorruptedSampleError, UnicodeEncodeError)`` arm in
``_api_loop`` (charged, capped, context-restarting — and never reaching
``_with_retry``), the fork loop's existing transient arm, and the compaction
seam (a failed summary request = the same charged, capped light restart, on
both the automatic and the Refresh call site).

No Isabelle / no REPL / no LLM. Run directly from anywhere (it puts the
package root on ``sys.path``): ``python test_corrupted_sample.py``. Exits
non-zero on any failure. Same shape as ``test_deep_restart.py``.
"""
import asyncio
import contextlib
import os
import sys
from time import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA.driver_api import (
    APIDriver, Provider, ProviderResponse, ToolCall, COMPACTION_PROMPT,
    _CompactionFailed, SystemMsg, UserMsg, AssistantMsg, ToolResultMsg)
from IsaMini.AoA.language_model_driver import (
    _CorruptedSampleError, _TransientError, _QuotaError, Usage)
from IsaMini.AoA.model import (
    Runtime, Role_Major, ResourceExhausted, SessionQuit, Interaction,
    ForkingMode, Refresh, TOOL_ANSWER_INDEX, TOOL_REFRESH)

LONE = "\ud83d"            # lone high surrogate (孤悬半)
SPLIT = "\ud83d" + "\ude00"  # surrogate pair split into two code points (劈开对)
PAIRED = "\U0001F600"      # the same emoji as ONE real non-BMP character

ZERO_USAGE = Usage(0, 0, 0, 0)
BRIEFING = "BRIEF"        # what the fake refresh tool hands to the Refresh branch

# The wording of _with_retry's transient arm (the fork loop's own transient
# arm shares it, but no fork runs in the main-loop scenarios): its presence
# there would mean a corrupted sample escaped to the outer layer (silent
# context rebuild). The primary escape detector is run_loop's entry count.
WITH_RETRY_MARK = "retrying in 2s"


def check(cond, msg):
    if not cond:
        print(f"FAIL: {msg}")
        sys.exit(1)


@contextlib.contextmanager
def fast_sleep():
    """Collapse asyncio.sleep so _retry_transient's backoff runs instantly."""
    real = asyncio.sleep
    async def _instant(_t, *a, **kw):
        await real(0)
    asyncio.sleep = _instant
    try:
        yield
    finally:
        asyncio.sleep = real


async def _no_retries(fn):
    """The "OpenAI"/"Codex-API" family's _retry_transient override: no re-rolls."""
    return await fn()


def resp(content=None, thinking=None, tool_calls=()):
    return ProviderResponse(content=content, thinking=thinking,
                            tool_calls=list(tool_calls), usage=ZERO_USAGE)


class FakeProvider(Provider):
    """Pops one scripted item per chat() call: a ProviderResponse is returned,
    an exception instance is raised. Script exhaustion raises IndexError —
    a scenario must consume its script exactly."""

    def __init__(self, script):
        self.script = list(script)
        self.calls = 0
        self.requests = []   # a snapshot of every request's message list

    async def chat(self, messages, tools, *, previous_response_id=None,
                   allowed_tools=None):
        self.calls += 1
        self.requests.append(list(messages))
        item = self.script.pop(0)
        if isinstance(item, BaseException):
            raise item
        return item

    def format_tools(self, tool_info):
        return []

    def format_assistant_msg(self, response):
        return AssistantMsg(response=response)

    @property
    def context_window(self):
        return 10_000_000

    @property
    def model_name(self):
        return "fake-model"

    def pricing(self):
        return {"input": 0.0, "cached": 0.0, "output": 0.0}


class FakeExecutor:
    """Executes nothing; settles the fork's answer future on the answer tool."""

    def __init__(self, session):
        self.session = session
        self.calls = []

    def tool_schemas(self):
        return {}

    async def execute(self, name, args):
        self.calls.append((name, args))
        p = self.session.fork_pending
        if name == TOOL_ANSWER_INDEX and p is not None and not p.answer.done():
            p.answer.set_result("ANSWERED")
        if name == TOOL_REFRESH:   # the real tool's raw write, then interrupt
            self.session.quit_info = Refresh(briefing=BRIEFING)
            await self.session.interrupt()
        return ("ok", False)


def make_driver(provider, *, max_retries=5):
    """A bare APIDriver with real loop/validation/budget machinery and stubbed
    logging/rendering — the ``cls.__new__(cls)`` host style of
    test_deep_restart.py."""
    d = APIDriver.__new__(APIDriver)
    d.parent = None
    d.root = None
    d.role = Role_Major()
    d.runtime = Runtime()
    d._quit_info = None
    d._retry_count = 0
    d.max_retries = max_retries
    d.max_tool_calls = 100000
    d.timeout_seconds = 14400.0
    d._provider = provider
    d._messages = []
    d._interrupted = False
    d._model_time_start = None
    d._last_response_id = None
    d._msgs_sent_through = 0
    d._prev_prompt_total = 0
    d._prev_output_tokens = 0
    d.total_input_tokens = 0
    d.total_output_tokens = 0
    d.total_cache_read_input_tokens = 0
    d.total_cache_creation_input_tokens = 0
    d.total_cost_usd = 0.0
    d.total_model_time = 0.0
    d.total_isabelle_time = 0.0
    d.total_quota_wait_time = 0.0
    d._fork_counter = 0
    d._fork_name = "main"
    d._total_calls_at_last_refresh = 0
    d.logged = []
    d.meta = []
    d._executor = FakeExecutor(d)
    d.system_prompt = lambda: "SYS"
    async def _initial():
        return "INITIAL PROMPT"
    d.initial_prompt = _initial
    d.retry_prompt = lambda unfinished: "RETRY"
    d.proof_scope_unfinished_nodes = lambda: set()
    d.log_model_output = lambda t: None
    d.log_model_thinking = lambda t: None
    d.log_retry = lambda u, r: None
    d.log_AoA_opr = lambda m, **kw: d.logged.append(("opr", m))
    d.warn_AoA_opr = lambda m, **kw: d.logged.append(("warn", m))
    d.log_cost = lambda m: None
    d.log_interaction = lambda t, p: None
    d.log_budget_exhausted = lambda reason: d.logged.append(("budget", reason))
    d._log_meta = lambda event, **kw: d.meta.append((event, kw))
    d._reset_view_state = lambda: None
    d.refresh_YAML = lambda: None
    d.log_proof = lambda: None
    async def _memo(trigger):
        pass
    d.maybe_run_memorize_interaction = _memo
    return d


def warns(d):
    return [m for kind, m in d.logged if kind == "warn"]


def meta_events(d):
    return [e for e, _ in d.meta]


def assert_messages_encodable(d, where):
    """The invariant: every string in the message list UTF-8-encodes."""
    for m in d._messages:
        strings = []
        match m:
            case SystemMsg(content=c) | UserMsg(content=c) \
                    | ToolResultMsg(content=c):
                strings.append(c)
            case AssistantMsg(response=r):
                strings += [r.content, r.thinking]
                strings += [tc.arguments for tc in r.tool_calls]
        for s in strings:
            if s is None:
                continue
            try:
                s.encode("utf-8")
            except UnicodeEncodeError:
                check(False, f"{where}: message list holds a lone surrogate")


async def run_loop(d, timeout=30):
    """Drive the REAL outer entry (_run_agent_loop = _with_retry(_api_loop))
    counting _api_loop entries: >1 would mean an escape to _with_retry."""
    entries = 0
    orig = APIDriver._api_loop
    async def counting():
        nonlocal entries
        entries += 1
        await orig(d)
    d._api_loop = counting
    with fast_sleep():
        await asyncio.wait_for(d._run_agent_loop(), timeout=timeout)
    return entries


# ---------------------------------------------------------------------------
# 1. the validator (§5.1)
# ---------------------------------------------------------------------------

def test_validator():
    d = make_driver(FakeProvider([]))

    d._validate_sample(resp(content=f"ok {PAIRED}", thinking="fine",
                            tool_calls=[ToolCall("1", "edit", '{"a": "x✓"}')]))
    check(d.meta == [], "legit pairs and normal Unicode must pass silently")

    for field, pos, r in [
            ("content", 2, resp(content="ab" + LONE)),
            ("thinking", 2, resp(content="ok", thinking="ab" + LONE)),
            ("tool_calls[1].arguments", 9,
             resp(tool_calls=[ToolCall("1", "edit", "{}"),
                              ToolCall("2", "edit", '{"x": "ab' + LONE + '"}')])),
    ]:
        d.meta.clear()
        try:
            d._validate_sample(r)
            check(False, f"corruption in {field} must be rejected")
        except _CorruptedSampleError:
            pass
        check(d.meta[0][0] == "CORRUPTED_SAMPLE"
              and d.meta[0][1]["field"] == field
              and d.meta[0][1]["shape"] == "lone_half"
              and d.meta[0][1]["position"] == pos,
              f"CORRUPTED_SAMPLE for {field} must carry field/shape/position")
        check(d.meta[0][1]["excerpt"].isascii(),
              "the excerpt must be ascii()-archived")

    d.meta.clear()
    try:
        d._validate_sample(resp(content="ab" + SPLIT + "cd"))
        check(False, "a split pair must be rejected")
    except _CorruptedSampleError:
        pass
    check(d.meta[0][1]["shape"] == "split_pair",
          "adjacent high+low surrogates must classify as split_pair")


# ---------------------------------------------------------------------------
# 2. end to end: re-roll, then the bounded arm (§5.2)
# ---------------------------------------------------------------------------

async def test_reroll_on_real_retry_path():
    p = FakeProvider([resp(content="ab" + SPLIT), resp(content="done")])
    d = make_driver(p)
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 2,
          "one _retry_transient re-roll must fix a single corrupted sample")
    check(d._retry_count == 0, "a re-roll absorbed inside _retry_transient is free")
    check(d.quit_info is None, "the run must end clean")
    check(not any(WITH_RETRY_MARK in w for w in warns(d)),
          "the corrupted sample must never reach _with_retry")
    assert_messages_encodable(d, "re-roll scenario")


async def test_bounded_arm_after_retries_exhausted():
    p = FakeProvider([resp(content="ab" + SPLIT)] * 10 + [resp(content="done")])
    d = make_driver(p)
    entries = await run_loop(d)
    check(entries == 1, "the arm must handle exhaustion inside _api_loop "
          "(an escape to _with_retry would re-enter it)")
    check(p.calls == 11, "10 re-rolls, then one turn after the restart")
    check(d._retry_count == 1, "the arm must charge exactly one retry")
    check("CONTEXT_RESTART" in meta_events(d),
          "the arm must go through the existing restart dispatcher")
    check(any("restarting context" in w for w in warns(d)),
          "the arm must log the restart")
    check(not any(WITH_RETRY_MARK in w for w in warns(d)),
          "the corrupted sample must never reach _with_retry")
    check(d.quit_info is None, "the run must end clean after the restart")
    assert_messages_encodable(d, "bounded-arm scenario")


async def test_retry_cap_in_noop_family():
    # The no-op _retry_transient override family ("OpenAI"/"Codex-API"): every
    # corrupted sample costs one charged light restart, max_retries caps it.
    p = FakeProvider([resp(content="ab" + LONE)] * 5)
    d = make_driver(p)
    d._retry_transient = _no_retries
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 5,
          "each corrupted sample must cost exactly one charged restart")
    check(d._retry_count == 5, "the restart branch must not reset the counter")
    check(meta_events(d).count("CONTEXT_RESTART") == 4,
          "hits 1-4 restart; hit 5 trips the cap instead")
    check(isinstance(d.quit_info, ResourceExhausted)
          and "retry limit" in d.quit_info.detail,
          "max_retries must end the run as ResourceExhausted")


# ---------------------------------------------------------------------------
# 3. fork: the existing transient arm, zero new code (§5.3)
# ---------------------------------------------------------------------------

class _Probe(Interaction):
    forking = ForkingMode.FORKING_WITH_CTXT
    answer_tool_name = TOOL_ANSWER_INDEX
    fork_allowed_tools = [TOOL_ANSWER_INDEX]
    async def prompt(self, indent, file):
        pass


async def _drive_fork(parent):
    saved = APIDriver._make_fork
    forks = []
    def _stub_fork(p, role):
        f = make_driver(p._provider)
        f.parent = p
        f.role = role
        f.runtime = p.runtime
        f._fork_name = "main.fork_1"
        async def _init(root):
            pass
        f.initialize = _init
        async def _close():
            pass
        f.close = _close
        forks.append(f)
        return f
    APIDriver._make_fork = classmethod(
        lambda cls, p, role=None: _stub_fork(p, role))
    try:
        with fast_sleep():
            answer = await asyncio.wait_for(
                parent._run_fork(_Probe(), "question?"), timeout=30)
    finally:
        APIDriver._make_fork = saved
    return answer, forks[0]


ANSWER_CALL = resp(tool_calls=[ToolCall("1", TOOL_ANSWER_INDEX, "{}")])


async def test_fork_rerolls_on_real_retry_path():
    p = FakeProvider([resp(content="ab" + SPLIT), ANSWER_CALL])
    parent = make_driver(p)
    answer, fork = await _drive_fork(parent)
    check(answer == "ANSWERED" and p.calls == 2,
          "the fork must re-roll the corrupted sample and then answer")
    check(fork.quit_info is None and parent.quit_info is None,
          "no verdict may spill out of the fork's re-roll")
    check(any(e == "CORRUPTED_SAMPLE" for e in meta_events(fork)),
          "the fork's rejection must log on the fork")


async def test_fork_transient_arm_in_noop_family():
    p = FakeProvider([resp(content="ab" + LONE), ANSWER_CALL])
    parent = make_driver(p)
    parent._retry_transient = _no_retries
    answer, fork = await _drive_fork(parent)
    check(answer == "ANSWERED" and p.calls == 2,
          "the existing fork transient arm must re-roll in place")
    check(any(WITH_RETRY_MARK in w for w in warns(parent)),
          "the fork's own transient arm (same wording) must have fired")
    check(fork.quit_info is None and parent.quit_info is None,
          "no verdict may spill onto the calling session")


class AlwaysRaise(Provider):
    """chat() raises the same exception on every call (counts calls)."""

    def __init__(self, exc):
        self.exc = exc
        self.calls = 0

    async def chat(self, messages, tools, *, previous_response_id=None,
                   allowed_tools=None):
        self.calls += 1
        raise self.exc

    format_tools = FakeProvider.format_tools
    format_assistant_msg = FakeProvider.format_assistant_msg
    context_window = FakeProvider.context_window
    model_name = FakeProvider.model_name
    pricing = FakeProvider.pricing


async def test_fork_transient_spin_is_bounded():
    # The fork's transient arm re-rolls forever unless the RUN-WIDE budget
    # stops it; a fork's own _retry_count must never become the reason.
    p = AlwaysRaise(_TransientError("5xx"))
    parent = make_driver(p)
    parent.runtime._budget_start_time = time() - parent.timeout_seconds - 1
    try:
        await _drive_fork(parent)
        check(False, "an exhausted budget must end the fork via SessionQuit")
    except SessionQuit as e:
        check(isinstance(e.quit_info, ResourceExhausted)
              and "timeout" in e.quit_info.detail,
              "the fork must stop on the shared wall clock")
    check(p.calls == 10, "one _retry_transient burst, then the guard trips")
    check(parent._retry_count == 0, "no retry may be charged to the parent")


async def test_fork_unicode_error_escapes_by_design():
    # Retry is futile on this seam (the poisoned list cannot be rebuilt), so
    # the fork lets UnicodeEncodeError out unchanged — fail fast, true cause.
    p = AlwaysRaise(UnicodeEncodeError("utf-8", LONE, 0, 1, "surrogates"))
    parent = make_driver(p)
    try:
        await _drive_fork(parent)
        check(False, "UnicodeEncodeError must propagate out of _run_fork")
    except UnicodeEncodeError:
        pass
    check(p.calls == 1, "no retry may be attempted")


# ---------------------------------------------------------------------------
# 4. compaction: a failed summary request is a charged, capped light restart
#    (COMPACTION_FAILURE_RESTART_PLAN.md §3)
# ---------------------------------------------------------------------------

# A turn WITH a tool call: the no-tool-call branch charges _retry_count on
# every turn while the proof is unfinished, which would silently turn the
# "capped on the 5th failure / charged 1" assertions into something else.
TOOL_CALL = resp(tool_calls=[ToolCall("1", "edit", "{}")])
REFRESH_CALL = resp(tool_calls=[ToolCall("1", TOOL_REFRESH, "{}")])
CORRUPTED = resp(content="ab" + SPLIT)
DONE = resp(content="done")


def make_compaction_driver(script, *, automatic, noop_family=False):
    """A driver whose proof stays unfinished until the script's last item is
    served (so tool-call turns reach the compaction point and the final turn
    ends the run clean). ``automatic`` forces _should_compact (the host's
    context window is 10M and usage all zero: it would never trigger);
    ``noop_family`` installs the "OpenAI"/"Codex-API" no-op _retry_transient."""
    p = FakeProvider(script)
    d = make_driver(p)
    d.proof_scope_unfinished_nodes = lambda: {"x"} if p.script else set()
    if automatic:
        d._should_compact = lambda usage: True
    if noop_family:
        d._retry_transient = _no_retries
    return d, p


def assert_no_prompt_residue(d, p, where):
    """Non-mutating construction: the compaction prompt appears only as the
    LAST message of a summary request, never in the driver's own list and
    never mid-request."""
    check(not any(isinstance(m, UserMsg) and m.content == COMPACTION_PROMPT
                  for m in d._messages),
          f"{where}: COMPACTION_PROMPT must not remain in d._messages")
    for req in p.requests:
        check(not any(isinstance(m, UserMsg) and m.content == COMPACTION_PROMPT
                      for m in req[:-1]),
              f"{where}: COMPACTION_PROMPT may only be the last message sent")
    assert_messages_encodable(d, where)


def compaction_failed_events(d):
    return [kw for e, kw in d.meta if e == "COMPACTION_FAILED"]


# (1) automatic compaction ---------------------------------------------------

async def test_auto_compaction_failure_restarts_after_rerolls():
    d, p = make_compaction_driver([TOOL_CALL] + [CORRUPTED] * 10 + [DONE],
                                  automatic=True)
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 12,
          "10 re-rolls of the summary, restart, then one turn after it")
    check(d._retry_count == 1, "one failed compaction charges exactly one retry")
    check("CONTEXT_RESTART" in meta_events(d), "the failure must light-restart")
    check("COMPACTION" not in meta_events(d), "no COMPACTION for a failed one")
    [ev] = compaction_failed_events(d)
    check(ev["error"] == "_CorruptedSampleError" and ev["briefing_dropped"] is False,
          "COMPACTION_FAILED must name the cause; no briefing on this path")
    check(any("_CorruptedSampleError on the model turn; restarting context" in w
              for w in warns(d)),
          "the warn must name the cause, not the _CompactionFailed wrapper")
    check(d.quit_info is None, "the run must end clean after the restart")
    assert_no_prompt_residue(d, p, "auto compaction, real retry family")


async def test_auto_compaction_failure_in_noop_family():
    d, p = make_compaction_driver([TOOL_CALL, CORRUPTED, DONE],
                                  automatic=True, noop_family=True)
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 3,
          "zero re-rolls in the no-op family: one corrupted summary = one restart")
    check(d._retry_count == 1 and "CONTEXT_RESTART" in meta_events(d),
          "charged once, restarted once")
    assert_no_prompt_residue(d, p, "auto compaction, no-op family")


async def test_auto_compaction_failure_is_capped():
    d, p = make_compaction_driver([TOOL_CALL, CORRUPTED] * 5,
                                  automatic=True, noop_family=True)
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 10,
          "after the cap no further model turn may be issued")
    check(d._retry_count == 5, "the restart branch must not reset the counter")
    check(meta_events(d).count("CONTEXT_RESTART") == 4,
          "failures 1-4 restart; failure 5 trips max_retries")
    check(len(compaction_failed_events(d)) == 5,
          "COMPACTION_FAILED is logged on the capped failure too")
    check(isinstance(d.quit_info, ResourceExhausted)
          and "retry limit" in d.quit_info.detail,
          "max_retries must end the run as ResourceExhausted")
    assert_no_prompt_residue(d, p, "auto compaction, capped")


# (2) the Refresh call site ---------------------------------------------------

async def test_refresh_failure_restarts_and_leaves_no_trace():
    d, p = make_compaction_driver([REFRESH_CALL, CORRUPTED, DONE],
                                  automatic=False, noop_family=True)
    age0 = d.runtime.age
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 3, "refresh, failed summary, restart, done")
    check(d._retry_count == 1 and "CONTEXT_RESTART" in meta_events(d),
          "a failed refresh is the same charged light restart")
    check("REFRESH" not in meta_events(d)
          and not any("Context refreshed" in m for _, m in d.logged),
          "a refresh that did not happen must not be reported as done")
    check(d.runtime.age == age0, "no age bump for a failed refresh")
    check(d._total_calls_at_last_refresh == 0,
          "a failed refresh must not consume the refresh cooldown")
    [ev] = compaction_failed_events(d)
    check(ev["briefing_dropped"] is True,
          "the dropped briefing must be visible in COMPACTION_FAILED")
    check(not any(isinstance(m, UserMsg) and BRIEFING in m.content
                  for m in d._messages), "the briefing is dropped with the restart")
    check(d.quit_info is None, "the run must end clean after the restart")
    assert_no_prompt_residue(d, p, "refresh failure")


async def test_refresh_failure_is_capped():
    # The load-bearing case: the Refresh caller sits in the OUTER loop; on the
    # capped path only _restart_after's trailing interrupt stops it from
    # `continue`-ing into one more model turn.
    d, p = make_compaction_driver([REFRESH_CALL, CORRUPTED] * 5,
                                  automatic=False, noop_family=True)
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 10,
          "after the cap no further model turn may be issued")
    check(isinstance(d.quit_info, ResourceExhausted)
          and "retry limit" in d.quit_info.detail,
          "max_retries must end the run as ResourceExhausted")
    check(meta_events(d).count("CONTEXT_RESTART") == 4
          and "REFRESH" not in meta_events(d), "four restarts, no refresh")
    assert_no_prompt_residue(d, p, "refresh failure, capped")


# (3) quota passes through ---------------------------------------------------

async def test_compaction_quota_error_escapes_uncharged():
    d, p = make_compaction_driver([TOOL_CALL, _QuotaError("billing")],
                                  automatic=True, noop_family=True)
    try:
        with fast_sleep():
            await asyncio.wait_for(d._api_loop(), timeout=30)
        check(False, "_QuotaError from the summary request must leave _api_loop")
    except _QuotaError:
        pass
    check(d._retry_count == 0, "quota is _with_retry's business, not a retry")
    check(compaction_failed_events(d) == [], "quota is not a compaction failure")
    assert_no_prompt_residue(d, p, "compaction quota error")


# (4) the wall clock --------------------------------------------------------

class YieldingProvider(FakeProvider):
    """Yields to the event loop once per chat() — asyncio.timeout can only
    fire at a suspension point, and the plain FakeProvider never suspends."""

    async def chat(self, messages, tools, **kw):
        await asyncio.sleep(0)
        return await super().chat(messages, tools, **kw)


async def test_compaction_wall_clock_cap_fires():
    p = YieldingProvider([DONE])
    d = make_driver(p)
    d.runtime._budget_start_time = time() - d.timeout_seconds - 1
    msgs = [SystemMsg("SYS"), UserMsg("INITIAL PROMPT")]
    try:
        await asyncio.wait_for(d._compact(msgs), timeout=30)
        check(False, "an expired budget must abort the summary request")
    except _CompactionFailed as e:
        check(isinstance(e.cause, TimeoutError), "the cause is the wall clock")
        await d._restart_after(e.cause)
    check(isinstance(d.quit_info, ResourceExhausted)
          and "timeout" in d.quit_info.detail,
          "the wall clock leg must end as ResourceExhausted, not restart")
    check(not any("restarting context" in w for w in warns(d)),
          "no restart on the wall-clock leg")
    check(len(msgs) == 2, "the caller's list is untouched")


# (5) the UnicodeEncodeError leg ---------------------------------------------

async def test_compaction_unicode_error_restarts():
    poison = UnicodeEncodeError("utf-8", LONE, 0, 1, "surrogates not allowed")
    d, p = make_compaction_driver([TOOL_CALL, poison, DONE], automatic=True)
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 3, "not retried, restarted once, done")
    check(d._retry_count == 1 and "CONTEXT_RESTART" in meta_events(d),
          "the UnicodeEncodeError leg charges one retry and restarts")
    check(any("UnicodeEncodeError on the model turn; restarting context" in w
              for w in warns(d)),
          "the warn must name the cause, not the _CompactionFailed wrapper")
    check(compaction_failed_events(d)[0]["error"] == "UnicodeEncodeError",
          "COMPACTION_FAILED names the leg")
    assert_no_prompt_residue(d, p, "compaction UnicodeEncodeError")


# (6) success paths -----------------------------------------------------------

async def test_compaction_success_paths():
    d, p = make_compaction_driver([TOOL_CALL, resp(content="SUMMARY"), DONE],
                                  automatic=True)
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 3 and d._retry_count == 0,
          "a successful compaction is free")
    check("COMPACTION" in meta_events(d) and compaction_failed_events(d) == [],
          "COMPACTION logged, no failure")
    check(any(isinstance(m, UserMsg) and "SUMMARY" in m.content
              for m in d._messages), "the new list carries the summary")
    assert_no_prompt_residue(d, p, "auto compaction success")

    d, p = make_compaction_driver([REFRESH_CALL, resp(content="SUMMARY"), DONE],
                                  automatic=False)
    age0 = d.runtime.age
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 3 and d._retry_count == 0,
          "a successful refresh is free")
    check("REFRESH" in meta_events(d)
          and any("Context refreshed" in m for _, m in d.logged),
          "a real refresh is reported")
    check(d.runtime.age == age0 + 1 and d._total_calls_at_last_refresh == 1,
          "age and cooldown move only on a real refresh")
    check(any(isinstance(m, UserMsg) and "SUMMARY" in m.content
              and BRIEFING in m.content for m in d._messages),
          "the new list carries summary and briefing")
    assert_no_prompt_residue(d, p, "refresh success")


# ---------------------------------------------------------------------------
# 6. the UnicodeEncodeError safety-net leg (§5.6)
# ---------------------------------------------------------------------------

async def test_safety_net_leg():
    # Poison hidden in a parsed native payload is invisible to the probe; the
    # HTTP client's strict UTF-8 encode raises client-side. Same arm, same bound.
    client_side = UnicodeEncodeError("utf-8", LONE, 0, 1, "surrogates not allowed")
    p = FakeProvider([client_side, resp(content="done")])
    d = make_driver(p)
    entries = await run_loop(d)
    check(entries == 1 and p.calls == 2,
          "the UnicodeEncodeError leg must restart once and finish")
    check(d._retry_count == 1, "the leg must charge one retry")
    check("CONTEXT_RESTART" in meta_events(d),
          "the leg must go through the restart dispatcher")
    check(d.quit_info is None, "the run must end clean")
    assert_messages_encodable(d, "safety-net scenario")


# ---------------------------------------------------------------------------

def main():
    test_validator()
    print("PASS: validator")
    asyncio.run(test_reroll_on_real_retry_path())
    print("PASS: re-roll on the real retry path")
    asyncio.run(test_bounded_arm_after_retries_exhausted())
    print("PASS: bounded arm after retries exhausted")
    asyncio.run(test_retry_cap_in_noop_family())
    print("PASS: retry cap in the no-op family")
    asyncio.run(test_fork_rerolls_on_real_retry_path())
    print("PASS: fork re-rolls on the real retry path")
    asyncio.run(test_fork_transient_arm_in_noop_family())
    print("PASS: fork existing transient arm (no-op family)")
    asyncio.run(test_fork_transient_spin_is_bounded())
    print("PASS: fork transient spin is bounded by the run-wide budget")
    asyncio.run(test_fork_unicode_error_escapes_by_design())
    print("PASS: fork UnicodeEncodeError escapes by design")
    asyncio.run(test_auto_compaction_failure_restarts_after_rerolls())
    print("PASS: auto compaction failure restarts after re-rolls")
    asyncio.run(test_auto_compaction_failure_in_noop_family())
    print("PASS: auto compaction failure in the no-op family")
    asyncio.run(test_auto_compaction_failure_is_capped())
    print("PASS: auto compaction failure is capped")
    asyncio.run(test_refresh_failure_restarts_and_leaves_no_trace())
    print("PASS: refresh failure restarts and leaves no trace")
    asyncio.run(test_refresh_failure_is_capped())
    print("PASS: refresh failure is capped")
    asyncio.run(test_compaction_quota_error_escapes_uncharged())
    print("PASS: compaction quota error escapes uncharged")
    asyncio.run(test_compaction_wall_clock_cap_fires())
    print("PASS: compaction wall-clock cap fires")
    asyncio.run(test_compaction_unicode_error_restarts())
    print("PASS: compaction UnicodeEncodeError restarts")
    asyncio.run(test_compaction_success_paths())
    print("PASS: compaction success paths")
    asyncio.run(test_safety_net_leg())
    print("PASS: UnicodeEncodeError safety-net leg")
    print("ALL PASS")


if __name__ == "__main__":
    main()
