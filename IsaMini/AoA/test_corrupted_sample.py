#!/usr/bin/env python3
"""Standalone unit tests for the API drivers' entry validation of corrupted
samples (lone UTF-16 surrogates in a model response): ``_validate_sample`` /
``_checked_chat``, the ``(_CorruptedSampleError, UnicodeEncodeError)`` arm in
``_api_loop`` (charged, capped, context-restarting — and never reaching
``_with_retry``), the fork loop's existing transient arm, and the compaction
degrade path.

No Isabelle / no REPL / no LLM. Run directly from anywhere (it puts the
package root on ``sys.path``): ``python test_corrupted_sample.py``. Exits
non-zero on any failure. Same shape as ``test_deep_restart.py``.
"""
import asyncio
import contextlib
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA.driver_api import (
    APIDriver, Provider, ProviderResponse, ToolCall,
    SystemMsg, UserMsg, AssistantMsg, ToolResultMsg)
from IsaMini.AoA.language_model_driver import (
    _CorruptedSampleError, _TransientError, Usage)
from IsaMini.AoA.model import (
    Runtime, Role_Major, Restart, ResourceExhausted, Interaction, ForkingMode,
    TOOL_ANSWER_INDEX)

LONE = "\ud83d"            # lone high surrogate (孤悬半)
SPLIT = "\ud83d" + "\ude00"  # surrogate pair split into two code points (劈开对)
PAIRED = "\U0001F600"      # the same emoji as ONE real non-BMP character

ZERO_USAGE = Usage(0, 0, 0, 0)

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

    async def chat(self, messages, tools, *, previous_response_id=None,
                   allowed_tools=None):
        self.calls += 1
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
    check(any("Corrupted sample" in w for w in warns(d)),
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
    async def _direct(fn):
        return await fn()
    d._retry_transient = _direct
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
    async def _direct(fn):
        return await fn()
    parent._retry_transient = _direct
    answer, fork = await _drive_fork(parent)
    check(answer == "ANSWERED" and p.calls == 2,
          "the existing fork transient arm must re-roll in place")
    check(any(WITH_RETRY_MARK in w for w in warns(parent)),
          "the fork's own transient arm (same wording) must have fired")
    check(fork.quit_info is None and parent.quit_info is None,
          "no verdict may spill onto the calling session")


# ---------------------------------------------------------------------------
# 4. compaction degrades to a skip (§5.4)
# ---------------------------------------------------------------------------

async def test_compaction_degrades_to_skip():
    p = FakeProvider([resp(content="ab" + SPLIT)] * 10)
    d = make_driver(p)
    msgs = [SystemMsg("SYS"), UserMsg("INITIAL PROMPT")]
    with fast_sleep():
        result = await asyncio.wait_for(d._compact(msgs, []), timeout=30)
    check(result is msgs, "the degrade must return the SAME list object "
          "(downstream identity test keeps the cache state)")
    check(len(result) == 2, "the appended compaction prompt must be popped")
    check(any("continuing without compaction" in w for w in warns(d)),
          "the skip must be logged")
    check("COMPACTION" not in meta_events(d),
          "no COMPACTION event may be logged for a skipped compaction")


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
    asyncio.run(test_compaction_degrades_to_skip())
    print("PASS: compaction degrades to a skip")
    asyncio.run(test_safety_net_leg())
    print("PASS: UnicodeEncodeError safety-net leg")
    print("ALL PASS")


if __name__ == "__main__":
    main()
