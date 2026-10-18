#!/usr/bin/env python3
"""Standalone unit tests for the Codex driver: its command lines, its
interaction forks, its default model and its usage per exec.

Every option precedes the subcommand (codex-cli 0.163.0 refuses ``-s`` after
``resume`` or ``fork``). An interaction fork runs as an ephemeral
``codex exec fork`` of the thread its parent forks from, and builds its own
commands: a fork launched from a fork forks that same thread without any shared
lock, and sibling forks run at once. A session records its thread id at
``thread.started``, before any tool call can launch a fork; ``_codex_loop``
clears the id and its usage total on entry, on Refresh and on Restart; an
interaction fork keeps the id and the usage total it inherited. A fork's later
attempts resend the question the fork was last shown, then the reminder; a
transient error forks the thread afresh. A fork is advertised the MCP tools of
the session that launched it. With no model in the driver string, the model and
reasoning effort are the Codex configuration's (``config.toml``), each falling
back to the class constant; a model in the driver string wins.
``turn.completed`` reports the thread's total, so an exec records the growth
since the thread's last ``turn.completed``, and nothing without one.

No Isabelle / no REPL / no codex process: the subprocess tests run a fake codex
script through the real ``_run_codex_exec``. Run directly from anywhere (it puts
the package root on ``sys.path``): ``python test_codex_fork.py``. Exits
non-zero on the first failure. Same shape as ``test_session_quit.py``.
"""
import asyncio
import contextlib
import json
import os
import shutil
import sys
import tempfile
from time import time
from types import SimpleNamespace

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))))

from IsaMini.AoA import mcp_http_server as mcp
from IsaMini.AoA.driver_codex import Codex_Driver
from IsaMini.AoA.language_model_driver import _TransientError
from IsaMini.AoA.model import (
    ContinuingInteraction, Fork_Pending, ForkingMode, InternalError, Refresh, Restart,
    Role_Interaction, Role_Worker, TOOL_ANSWER_INDEX, TOOL_SEARCH, TOOL_SUBAGENT)
from IsaMini.AoA.test_corrupted_sample import fast_sleep
from IsaMini.AoA.test_session_quit import _Probe


def check(cond, msg):
    if not cond:
        print(f"  FAIL {msg}")
        sys.exit(1)
    print(f"  ok   {msg}")


# ---------------------------------------------------------------------------
# Harness
# ---------------------------------------------------------------------------

@contextlib.contextmanager
def codex_root(config_toml: str | None = None, argument: str | None = None):
    """A major ``Codex_Driver`` (no parent) without file logging, built under a temporary
    CODEX_HOME holding an empty ``auth.json`` (the constructor copies the
    credential file and never reads it) and, when given, a ``config.toml``;
    ``argument`` is the driver string's model part. The directories are removed
    afterwards."""
    old = os.environ.get("CODEX_HOME")
    with tempfile.TemporaryDirectory() as home:
        open(os.path.join(home, "auth.json"), "w").close()
        if config_toml is not None:
            with open(os.path.join(home, "config.toml"), "w") as f:
                f.write(config_toml)
        os.environ["CODEX_HOME"] = home
        try:
            d = Codex_Driver(None, "", argument=argument)
        finally:
            if old is None:
                os.environ.pop("CODEX_HOME", None)
            else:
                os.environ["CODEX_HOME"] = old
    try:
        yield d
    finally:
        shutil.rmtree(d.working_dir, ignore_errors=True)
        shutil.rmtree(d._codex_home_dir, ignore_errors=True)


@contextlib.contextmanager
def codex_major():
    """The major, set up as far as a fork reads it: a stand-in proof tree (the
    sub-session constructor copies ``parent.root``), its MCP endpoint and its
    instructions file."""
    with codex_root() as d:
        d.root = object()  # type: ignore[assignment]
        d._mcp_url = "http://127.0.0.1:1/mcp/main"
        d._model_instructions_path = "/x/main.md"
        yield d


class _StagedProbe(_Probe):
    """An interaction whose question depends on its stage, like Interaction_Memorize."""
    stage = 1

    async def prompt(self, indent, file):
        file.write(f"stage {self.stage}")


class _ContinuingProbe(_Probe):
    """An interaction whose answer keeps the fork alive: ``continuing`` is the
    ``ContinuingInteraction`` its ``answer`` raises (a re-prompt or a replacement)."""

    def __init__(self, continuing):
        self.continuing = continuing

    async def answer(self, answer):
        raise self.continuing


def direct_fork(parent, interaction=None, prompt=""):
    """An interaction fork of ``parent`` built through the constructor, holding
    an unanswered slot; ``prompt`` is the question it was launched with. Called
    inside a running loop (the slot is a Future)."""
    fork = Codex_Driver(parent=parent, role=Role_Interaction(
        pending=Fork_Pending(interaction or _Probe(), asyncio.get_running_loop().create_future()),
        prompt=prompt, resume_id=None, mode=ForkingMode.FORKING_WITH_CTXT))
    fork._mcp_url = f"http://127.0.0.1:1/mcp/{fork._fork_name}"
    return fork


def endpoint_arg(url: str) -> str:
    return f"mcp_servers.proof.url={json.dumps(url)}"


def fork_prompt_for(text: str) -> str:
    """What ``_fork_prompt`` builds for an interaction whose prompt does not name
    the answer tool."""
    return ("Let's consider a sub-task forked from the context:\n" + text
            + "\nAnswer the question above by calling the "
            "`mcp__proof__answer_index` tool.")


@contextlib.contextmanager
def fork_plumbing_stubs():
    """``_do_fork`` without an MCP server or a proof tree: ``initialize`` only
    gives the fork its endpoint."""
    real = Codex_Driver.initialize

    async def _initialize(self, root):
        self._session_id = self._fork_name
        self._mcp_url = f"http://127.0.0.1:1/mcp/{self._fork_name}"
    Codex_Driver.initialize = _initialize
    try:
        yield
    finally:
        Codex_Driver.initialize = real


@contextlib.contextmanager
def fake_exec(fn):
    """Replace ``_run_codex_exec`` for every session with ``fn(self, cmd)``."""
    real = Codex_Driver._run_codex_exec
    Codex_Driver._run_codex_exec = fn
    try:
        yield
    finally:
        Codex_Driver._run_codex_exec = real


# A fake codex: prints `thread.started` with the id it is given; `--tool` prints
# one MCP tool call; `--sentinel PATH` waits for that file; then prints
# `turn.completed` with the thread total `--usage input,cached,output[,cache_write]`
# (default 7,2,1,0), or nothing more under `--abort` (an exec ended by an
# interrupt).
_FAKE_CODEX = '''\
import json, os, sys, time
args = sys.argv[2:]
def opt(name, default=None):
    return args[args.index(name) + 1] if name in args else default
print(json.dumps({"type": "thread.started", "thread_id": sys.argv[1]}), flush=True)
if "--tool" in args:
    print(json.dumps({"type": "item.started", "item": {
        "type": "mcp_tool_call", "server": "proof", "tool": "query", "arguments": {}}}),
          flush=True)
if opt("--sentinel"):
    while not os.path.exists(opt("--sentinel")):
        time.sleep(0.01)
if "--abort" not in args:
    i, c, o, w = (int(x) for x in (opt("--usage", "7,2,1") + ",0").split(",")[:4])
    print(json.dumps({"type": "turn.completed", "usage": {
        "input_tokens": i, "cached_input_tokens": c, "output_tokens": o,
        "cache_write_input_tokens": w}}), flush=True)
'''


def write_fake_codex(directory: str) -> str:
    path = os.path.join(directory, "fake_codex.py")
    with open(path, "w") as f:
        f.write(_FAKE_CODEX)
    return path


async def wait_until(pred, timeout: float = 5.0) -> bool:
    deadline = time() + timeout
    while not pred():
        if time() > deadline:
            return False
        await asyncio.sleep(0.01)
    return True


def loop_stubs(d, *, unfinished_once: bool):
    """``_codex_loop`` without a proof tree: the prompts, the budget, the YAML
    and the proof log are stubbed; ``proof_scope_unfinished_nodes`` reports one
    unfinished node on its first call iff ``unfinished_once``."""
    async def initial_prompt():
        return "init"
    calls = [0]

    def unfinished():
        calls[0] += 1
        return {object()} if unfinished_once and calls[0] == 1 else set()
    d.initial_prompt = initial_prompt
    d.retry_prompt = lambda nodes: "retry"
    d.proof_scope_unfinished_nodes = unfinished
    d.check_budget = lambda: False
    d.refresh_YAML = lambda: None
    d._reset_view_state = lambda: None
    d.log_proof = lambda: None
    d.log_retry = lambda nodes, prompt: None


def exec_recorder(d, script: str, thread_ids: list[str], record: list, after_first=None):
    """Wrap ``d._run_codex_exec``: record ``(cmd, d._codex_session_id)`` at entry,
    then run the fake codex through the real method with the next thread id;
    ``after_first()`` runs once the first exec has returned."""
    real = Codex_Driver._run_codex_exec
    ids = iter(thread_ids)

    async def wrapped(cmd):
        record.append((cmd, d._codex_session_id))
        await real(d, [sys.executable, script, next(ids)])
        if after_first is not None and len(record) == 1:
            after_first()
    d._run_codex_exec = wrapped


def usage_totals(d):
    """The session's recorded usage: (uncached input, cached, output)."""
    return (d.total_input_tokens, d.total_cache_read_input_tokens, d.total_output_tokens)


# ---------------------------------------------------------------------------
# T1 / T2: command shapes and the constructor
# ---------------------------------------------------------------------------

def test_T1_command_shapes():
    async def body():
        with codex_major() as major:
            major._codex_session_id = "T0"
            fork = direct_fork(major)
            for d, who in ((major, "the major"), (fork, "the fork")):
                common = d._codex_common_args()
                exec_cmd = d._build_exec_cmd("p")
                resume_cmd = d._build_resume_cmd("T", "p")
                fork_cmd = d._build_fork_cmd("T", "p")
                check(exec_cmd == ["codex", "exec", *common, "-C", d.working_dir, "p"],
                      f"{who}: a fresh exec is the options, then the working directory and the prompt")
                check(resume_cmd == ["codex", "exec", *common, "resume", "T", "p"],
                      f"{who}: a resume is the options, then `resume`, the thread id and the prompt")
                check(fork_cmd == ["codex", "exec", *common, "fork", "T", "p"],
                      f"{who}: a fork is the options, then `fork`, the thread id and the prompt")
                check(resume_cmd.index("-s") < resume_cmd.index("resume")
                      and fork_cmd.index("-s") < fork_cmd.index("fork"),
                      f"{who}: the sandbox option precedes the subcommand")
                check('model_instructions_file="/x/main.md"' in common,
                      f"{who}: the commands carry the major's instructions file")
            check("--ephemeral" not in major._codex_common_args(),
                  "the major's commands carry no --ephemeral")
            fork_cmd = fork._build_fork_cmd("T", "p")
            check("--ephemeral" in fork_cmd and fork_cmd.index("--ephemeral") < fork_cmd.index("fork"),
                  "the fork's commands carry --ephemeral, before the subcommand")
            check(endpoint_arg("http://127.0.0.1:1/mcp/main.fork_1") in fork_cmd
                  and endpoint_arg("http://127.0.0.1:1/mcp/main") not in fork_cmd,
                  "the fork's commands name the fork's own MCP endpoint")
    asyncio.run(body())


def test_T2_constructor():
    async def body():
        with codex_major() as major:
            major._codex_session_id = "T0"
            fork = direct_fork(major)
            check(fork._codex_session_id == "T0",
                  "a fork is constructed with the thread id of the session that launched it")
            check(fork._model_instructions_path == "/x/main.md",
                  "a fork is constructed with that session's instructions file")
            check(not any(hasattr(d, a) for d in (major, fork)
                          for a in ("_fork_lock", "_codex_session_jsonl")),
                  "no session has a fork lock or a rollout path")
    asyncio.run(body())


# ---------------------------------------------------------------------------
# T3 / T4: the thread id (D5)
# ---------------------------------------------------------------------------

def test_T3_thread_id_known_during_the_exec():
    async def body():
        with codex_major() as major, tempfile.TemporaryDirectory() as tmp:
            script = write_fake_codex(tmp)
            sentinel = os.path.join(tmp, "go")
            task = asyncio.ensure_future(
                major._run_codex_exec([sys.executable, script, "T1", "--sentinel", sentinel]))
            seen = await wait_until(lambda: major._codex_session_id == "T1")
            check(seen and not task.done(),
                  "the major records its thread id while its exec is still running")
            open(sentinel, "w").close()
            await task
            check(usage_totals(major) == (5, 2, 1),
                  "the exec records the turn's usage on the session")
            major._codex_session_id = "P"
            fork = direct_fork(major)
            sentinel = os.path.join(tmp, "go2")
            calls = fork.total_tool_calls
            task = asyncio.ensure_future(
                fork._run_codex_exec([sys.executable, script, "E1", "--sentinel", sentinel, "--tool"]))
            seen = await wait_until(lambda: fork.total_tool_calls > calls)
            check(seen and fork._codex_session_id == "P",
                  "an interaction fork keeps the inherited thread id while its exec runs "
                  "(its own thread.started has been read)")
            open(sentinel, "w").close()
            await task
            check(fork._codex_session_id == "P",
                  "an interaction fork keeps the inherited thread id after its exec")
    asyncio.run(body())


def test_T4_thread_selection_in_the_loop():
    async def body():
        with codex_major() as major, tempfile.TemporaryDirectory() as tmp:
            script = write_fake_codex(tmp)
            # a retry turn resumes the thread the first exec started
            record: list = []
            loop_stubs(major, unfinished_once=True)
            exec_recorder(major, script, ["T1", "T1"], record)
            await major._codex_loop()
            check([field for _, field in record] == [None, "T1"],
                  "the first exec starts with no thread; the retry turn sees the recorded id")
            check(record[0][0][-3:] == ["-C", major.working_dir, "init"]
                  and record[1][0][-3:] == ["resume", "T1", "retry"],
                  "a fresh exec, then `resume T1` with the retry prompt")
            # the fake reports the same thread total (7,2,1) at every turn.completed:
            # a fresh exec records it in full, a resume turn records its growth, 0
            check(usage_totals(major) == (5, 2, 1),
                  "the retry turn records the growth of the thread total, here nothing")
            # Refresh and Restart: the next exec is fresh (after a Refresh, with the
            # briefing) and starts a new thread, whose first total is recorded in full
            for quit, prompt, totals in (
                    (Refresh(briefing="b"), "init\n\nAgent's briefing:\nb", (15, 6, 3)),
                    (Restart(), "init", (25, 10, 5))):
                record = []
                loop_stubs(major, unfinished_once=False)
                exec_recorder(major, script, ["T2", "T3"], record,
                              after_first=lambda q=quit: setattr(major, "quit_info", q))
                await major._codex_loop()
                check([field for _, field in record] == [None, None]
                      and record[1][0][-3:] == ["-C", major.working_dir, prompt],
                      f"after a {quit.reason} the next exec is fresh and sees no thread id")
                check(major._codex_session_id == "T3",
                      f"after a {quit.reason} the new thread is recorded")
                check(usage_totals(major) == totals,
                      f"the two threads of the {quit.reason} pass each record their first total in full")
            # a worker clears the inherited id and usage total before its first exec;
            # its retry turn is measured over its own thread's total
            major._codex_session_id = "P"
            worker = Codex_Driver(parent=major, role=Role_Worker(
                target=SimpleNamespace(id="1")))  # type: ignore[arg-type]
            worker._mcp_url = "http://127.0.0.1:1/mcp/w"
            check(worker._codex_session_id == "P"
                  and worker._codex_total_usage == major._codex_total_usage != {},
                  "a worker is constructed with the major's id and usage total")
            before = dict(major._codex_total_usage)
            record = []
            loop_stubs(worker, unfinished_once=True)
            exec_recorder(worker, script, ["W1", "W1"], record)
            await worker._codex_loop()
            check([field for _, field in record] == [None, "W1"] and record[0][0][-3] == "-C"
                  and worker._codex_session_id == "W1",
                  "the worker's first exec is fresh, sees None, and records its own thread, "
                  "which its retry turn resumes")
            check(usage_totals(worker) == (5, 2, 1),
                  "the worker's first total is recorded in full and its retry turn's growth over it")
            check("--ephemeral" not in record[0][0], "the worker's commands carry no --ephemeral")
            check(major._codex_session_id == "P" and major._codex_total_usage == before,
                  "the major's id and usage total are untouched by the worker")
    asyncio.run(body())


# ---------------------------------------------------------------------------
# T5: the fork's attempts
# ---------------------------------------------------------------------------

def test_T5_fork_attempts():
    reminder = ("\n\nYou haven't submitted your answer. Call the "
                "`mcp__proof__answer_index` tool to submit it.")

    def recorder(fork, answer_on: int | None, during_first=None):
        """Replace the fork's exec: record the command, run ``during_first`` inside
        the first attempt (as the model's tool calls would run), and answer on
        attempt ``answer_on``."""
        record: list = []

        async def fake(cmd):
            record.append(cmd)
            if during_first is not None and len(record) == 1:
                await during_first()
            if len(record) == answer_on:
                fork.fork_pending.answer.set_result(42)
        fork._run_codex_exec = fake
        return record

    def answer_call(fork):
        return lambda: mcp._answer_tool_dispatch(fork, TOOL_ANSWER_INDEX, {"index": 0})

    async def body():
        with codex_major() as major:
            major._codex_session_id = "P"
            fork = direct_fork(major, _StagedProbe(), "Q")
            record = recorder(fork, 1)
            await fork._run_fork_attempts("Q", "[t]")
            check(record == [fork._build_fork_cmd("P", fork_prompt_for("Q"))],
                  "attempt 1 forks the inherited thread with the question as launched")
            # the fork searches during attempt 1 (`yes_recursive`): the results of its `query`
            # calls, taken down by the executor, are resent on attempt 2 between the question
            # and the reminder, under the header
            fork = direct_fork(major, _StagedProbe(), "Q")
            fork.fork_pending.interaction.fork_allowed_tools = [TOOL_ANSWER_INDEX, TOOL_SEARCH]  # type: ignore[union-attr]
            executor = mcp.ToolExecutor(fork)
            fork.check_budget = lambda: False
            executor._should_loop_restart = lambda session, name, arguments: False
            found = iter(["found: lemma_a", "found: lemma_b"])

            async def fake_query(session, arguments):
                return (next(found), False)
            searched: list = []

            async def two_searches():
                for _ in range(2):
                    searched.append(await executor.execute("query", {"queries": []}))
            real_query = mcp._query_tool_logic
            mcp._query_tool_logic = fake_query
            try:
                record = recorder(fork, 2, during_first=two_searches)
                await fork._run_fork_attempts("Q", "[t]")
            finally:
                mcp._query_tool_logic = real_query
            check(searched == [("found: lemma_a", False), ("found: lemma_b", False)],
                  "the fork's searches answer what the query tool answers")
            check(len(record) == 2
                  and record[1] == fork._build_fork_cmd("P", fork_prompt_for("Q")
                                                        + "\n\nResults of the searches you ran before this retry:\n"
                                                        "found: lemma_a\n\nfound: lemma_b" + reminder),
                  "attempt 2 resends the question, the results of the fork's searches, then the reminder")
            # the interaction re-prompts itself during attempt 1 (as Interaction_Memorize
            # does when it advances its stage): attempt 2 resends that question
            fork = direct_fork(major, _ContinuingProbe(ContinuingInteraction(new_prompt="stage 2")), "Q")
            record = recorder(fork, 2, during_first=answer_call(fork))
            await fork._run_fork_attempts("Q", "[t]")
            check(len(record) == 2
                  and record[1] == fork._build_fork_cmd("P", fork_prompt_for("stage 2") + reminder),
                  "attempt 2 forks the thread again and resends the question the fork was "
                  "last shown, then the reminder")
            # the interaction is replaced during attempt 1: attempt 2 resends the
            # replacement's question
            later = _StagedProbe()
            later.stage = 3
            fork = direct_fork(major, _ContinuingProbe(ContinuingInteraction(new_interaction=later)), "Q")
            record = recorder(fork, 2, during_first=answer_call(fork))
            await fork._run_fork_attempts("Q", "[t]")
            check(len(record) == 2 and fork.fork_pending.interaction is later  # type: ignore[union-attr]
                  and record[1] == fork._build_fork_cmd("P", fork_prompt_for("stage 3") + reminder),
                  "after a replacement, attempt 2 resends the replacement's question, then the reminder")
            # never answers, nothing shown anew: the question as launched, never rendered again
            fork = direct_fork(major, _StagedProbe(), "Q")
            record = recorder(fork, None)
            try:
                await fork._run_fork_attempts("Q", "[t]")
                check(False, "a fork that never answers raises")
            except InternalError as e:
                check("[t] fork did not submit an answer after 4 attempts" in str(e),
                      "a fork that never answers raises after the fourth attempt")
            check(len(record) == 4
                  and all(c == fork._build_fork_cmd("P", fork_prompt_for("Q") + reminder)
                          for c in record[1:]),
                  "every later attempt resends the question as launched, then the reminder")
            fork = direct_fork(major, prompt="Q")
            fork._codex_session_id = None
            record = recorder(fork, 1)
            await fork._run_fork_attempts("Q", "[t]")
            check(record == [fork._build_exec_cmd(fork_prompt_for("Q"))] and "--ephemeral" in record[0]
                  and "fork" not in record[0],
                  "with no thread to fork, the attempt is a fresh ephemeral exec")
    asyncio.run(body())


# ---------------------------------------------------------------------------
# T6 - T9: forks through `_do_fork`
# ---------------------------------------------------------------------------

def test_T6_nested_fork_and_T9_totals():
    async def body():
        with codex_major() as major, fork_plumbing_stubs():
            major._codex_session_id = "T0"
            record: list = []
            outer_after_inner: list = []

            async def fake(self, cmd):
                record.append((self._fork_name, cmd))
                if self._fork_name == "main.fork_1":
                    # a `query` inside the outer fork's exec launches a fork
                    inner = await self._do_fork(_Probe(), "inner question")
                    outer_after_inner.append(self.total_input_tokens)
                    self.fork_pending.answer.set_result(("outer", inner))
                else:
                    self.fork_pending.answer.set_result("inner answer")
                self._record_codex_usage({"input_tokens": 100, "cached_input_tokens": 40,
                                          "output_tokens": 5})
            with fake_exec(fake):
                try:
                    result = await asyncio.wait_for(major._do_fork(_Probe(), "outer question"), 10)
                except Exception as e:
                    check(False, f"a fork launched from a fork completes ({e!r})")
                    return
            check(result == ("outer", "inner answer"),
                  "a fork launched from a fork answers, and the outer fork returns")
            check([name for name, _ in record] == ["main.fork_1", "main.fork_1.fork_1"],
                  "the outer fork's exec started first, and the inner fork's exec ran inside it")
            inner_cmd = record[1][1]
            check(inner_cmd[-3:] == ["fork", "T0", fork_prompt_for("inner question")],
                  "the inner fork forks the major's thread")
            check(endpoint_arg("http://127.0.0.1:1/mcp/main.fork_1.fork_1") in inner_cmd
                  and "--ephemeral" in inner_cmd,
                  "the inner fork is ephemeral and uses its own MCP endpoint")
            check(record[0][1][-3:] == ["fork", "T0", fork_prompt_for("outer question")],
                  "the outer fork forks the major's thread")
            # T9: the inner fork's usage reaches the major through the outer fork
            check(usage_totals(major) == (120, 80, 10),
                  "both forks' usage reaches the major (input excludes the cached part)")
            check(outer_after_inner == [60],
                  "the inner fork's usage is folded into the outer fork when the inner fork ends")
    asyncio.run(body())


def test_T7_sibling_forks_run_concurrently():
    async def body():
        with codex_major() as major, fork_plumbing_stubs():
            major._codex_session_id = "T0"
            barrier = asyncio.Barrier(2)

            async def fake(self, cmd):
                # both forks must be inside their exec at the same time
                await asyncio.wait_for(barrier.wait(), 5)
                self.fork_pending.answer.set_result(self._fork_name)
            with fake_exec(fake):
                try:
                    results = await asyncio.wait_for(asyncio.gather(
                        major._do_fork(_Probe(), "a"), major._do_fork(_Probe(), "b")), 10)
                except Exception as e:
                    check(False, f"two sibling forks run at the same time ({e!r})")
                    return
            check(sorted(results) == ["main.fork_1", "main.fork_2"],
                  "two sibling forks run at the same time")
    asyncio.run(body())


def test_T8_transient_error_forks_afresh():
    async def body():
        with codex_major() as major, fork_plumbing_stubs(), fast_sleep():
            major._codex_session_id = "T0"
            calls: list = []

            async def fake(self, cmd):
                calls.append(cmd)
                if len(calls) == 1:
                    raise _TransientError("boom")
                self.fork_pending.answer.set_result(1)
            with fake_exec(fake):
                result = await asyncio.wait_for(major._do_fork(_Probe(), "q"), 10)
            check(result == 1 and len(calls) == 2
                  and calls[1][-3:] == ["fork", "T0", fork_prompt_for("q")],
                  "after a transient error the thread is forked afresh with the full prompt")
    asyncio.run(body())


# ---------------------------------------------------------------------------
# T10: a fork's MCP tools
# ---------------------------------------------------------------------------

def test_T10_fork_tools_are_those_of_the_session_that_launched_it():
    async def body():
        with codex_major() as major:
            fork = direct_fork(major)
            inner = direct_fork(fork)
            tools = mcp._tool_schemas_for(major)
            check(TOOL_SUBAGENT in tools
                  and mcp._tool_schemas_for(fork) == tools == mcp._tool_schemas_for(inner),
                  "a fork, and a fork launched from it, are advertised the major's tools")
            check("is not allowed" in (mcp._check_tool_permission(fork, TOOL_SUBAGENT) or ""),
                  "a fork's subagent call is refused")
            for logic in (mcp._subagent_tool_logic, mcp._close_subagent_tool_logic):
                try:
                    await logic(fork, {"step_id": "1"})
                    raised = None
                except Exception as e:
                    raised = e
                check(isinstance(raised, InternalError) and "called by an interaction fork" in str(raised),
                      f"{logic.__name__} run by a fork, past the permission check, raises InternalError"
                      f" (got {type(raised).__name__})")
            major._can_offer_dispatch_tools = lambda: False
            check(TOOL_SUBAGENT not in mcp._tool_schemas_for(inner)
                  and mcp._tool_schemas_for(inner) == mcp._tool_schemas_for(major),
                  "when the major cannot dispatch, a fork launched from its fork is advertised "
                  "the major's tools, without a dispatch tool")
    asyncio.run(body())


# ---------------------------------------------------------------------------
# T11 / T12: the model default and the usage of an exec
# ---------------------------------------------------------------------------

def test_T11_default_model_is_the_codex_configurations():
    with codex_root('model = "m-x"\nmodel_reasoning_effort = "low"\n') as d:
        d._mcp_url = "http://127.0.0.1:1/mcp/main"
        common = d._codex_common_args()
        check((d._model, d._reasoning_effort) == ("m-x", "low")
              and common[common.index("-m") + 1] == "m-x"
              and 'model_reasoning_effort="low"' in common,
              "with no model in the driver string, the Codex configuration's model and effort")
        check(str(d) == "Codex(m-x-low)", "the driver's name carries the model and effort")
        lines: list = []
        d.log_AoA_opr = lambda message: lines.append(message)
        d._on_start_run()
        check(len(lines) == 1 and lines[0].startswith("Driver Codex(m-x-low), "),
              "the start line names the model and effort")
    with codex_root('model = "m-max"\n') as d:
        check((d._model, d._reasoning_effort) == ("m-max", Codex_Driver.DEFAULT_EFFORT),
              "a configured model is taken whole, never split at an effort suffix; "
              "without an effort it takes the default effort")
    with codex_root('model_reasoning_effort = "medium"\n') as d:
        check((d._model, d._reasoning_effort) == (Codex_Driver.DEFAULT_MODEL, "medium"),
              "a configured effort without a model takes the default model")
    with codex_root() as d:
        check((d._model, d._reasoning_effort)
              == (Codex_Driver.DEFAULT_MODEL, Codex_Driver.DEFAULT_EFFORT) == ("gpt-5.5", "high"),
              "without a configured model or effort, the class constants")
        check(str(d) == "Codex(gpt-5.5-high)",
              "the driver's name carries the default model and effort too")
    with codex_root('model = "m-x"\nmodel_reasoning_effort = "medium"\n', argument="gpt-5.4-low") as d:
        check((d._model, d._reasoning_effort) == ("gpt-5.4", "low"),
              "a model and effort in the driver string win over the configuration")
    with codex_root('model_reasoning_effort = "medium"\n', argument="gpt-5.4") as d:
        check((d._model, d._reasoning_effort) == ("gpt-5.4", Codex_Driver.DEFAULT_EFFORT),
              "a driver string without an effort suffix takes the default effort, not the configured one")


def test_T12_usage_is_the_growth_of_the_thread_total():
    async def body():
        with codex_major() as major, tempfile.TemporaryDirectory() as tmp:
            script = write_fake_codex(tmp)
            costs: list = []
            events: list = []
            major.log_cost = lambda msg: costs.append(msg)
            major._log_meta = lambda event_type, **data: events.append(event_type)
            py = sys.executable
            await major._run_codex_exec([py, script, "T1", "--usage", "7,2,1"])
            await major._run_codex_exec([py, script, "T1", "--abort"])
            await major._run_codex_exec([py, script, "T1", "--usage", "17,6,3"])
            check(usage_totals(major) == (11, 6, 3),
                  "a later exec of the thread records the growth of the thread total "
                  "(input without the cached part)")
            check(costs == ["input=7 cached=2 output=1", "input=10 cached=4 output=2"]
                  and events.count("USAGE") == 2,
                  "an exec without turn.completed writes neither a cost line nor a usage row")
            await major._run_codex_exec([py, script, "T1", "--usage", "27,8,4,4"])
            check(usage_totals(major) == (15, 8, 4) and major.total_cache_creation_input_tokens == 4,
                  "cache-written input is recorded apart from the uncached input")
            # an interaction fork keeps the inherited total: each attempt is a fresh
            # ephemeral thread whose total is the source's plus the attempt's own
            major._codex_session_id = "P"
            fork = direct_fork(major)
            fork.log_cost = lambda msg: costs.append(msg)
            await fork._run_codex_exec([py, script, "E1", "--usage", "34,10,7,4"])
            await fork._run_codex_exec([py, script, "E2", "--usage", "31,8,5,4"])
            check(usage_totals(fork) == (9, 2, 4)
                  and costs[-2:] == ["input=7 cached=2 output=3", "input=4 cached=0 output=1"],
                  "each fork attempt records its growth over the inherited total")
            check(fork._codex_session_id == "P" and fork._codex_total_usage is major._codex_total_usage,
                  "the fork's thread id and usage total stay the inherited ones")
    asyncio.run(body())


def main():
    for t in (test_T1_command_shapes, test_T2_constructor,
              test_T3_thread_id_known_during_the_exec,
              test_T4_thread_selection_in_the_loop, test_T5_fork_attempts,
              test_T6_nested_fork_and_T9_totals, test_T7_sibling_forks_run_concurrently,
              test_T8_transient_error_forks_afresh,
              test_T10_fork_tools_are_those_of_the_session_that_launched_it,
              test_T11_default_model_is_the_codex_configurations,
              test_T12_usage_is_the_growth_of_the_thread_total):
        print(t.__name__)
        t()
    print("\nall checks passed")


if __name__ == "__main__":
    main()
