"""Focused unit test for replacing a fork's pending interaction mid-answer.

Covers the mechanism added so that an Interaction's answer() can raise
ContinuingInteraction(new_interaction=...) to swap the whole pending interaction
within the same fork (reusing its answer future).

Run:  python -m IsaMini.AoA.test_replace_interaction
"""

import asyncio

from .model import (
    Interaction, ContinuingInteraction, ImmediateAnswer, InternalError,
    Role_Interaction, Fork_Pending, ForkingMode, Session,
    TOOL_ANSWER_INDEXES, TOOL_ANSWER_TARGET_GOAL, TOOL_SEARCH,
)
from .mcp_http_server import _answer_tool_dispatch


# --- stub interactions -------------------------------------------------------

class StubA(Interaction):
    forking = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools = [TOOL_ANSWER_INDEXES, TOOL_SEARCH]

    def __init__(self, to_raise=None, result=None):
        self.to_raise = to_raise
        self.result = result

    async def prompt(self, indent, file):
        file.write("PROMPT_A")

    async def answer(self, payload):
        if self.to_raise is not None:
            raise self.to_raise
        return self.result


class StubB(Interaction):
    forking = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools = [TOOL_ANSWER_INDEXES, TOOL_SEARCH]

    def __init__(self, prompt_raises=None):
        self.prompt_raises = prompt_raises

    async def prompt(self, indent, file):
        if self.prompt_raises is not None:
            raise self.prompt_raises
        file.write("PROMPT_B")

    async def answer(self, payload):
        return "B_ANSWER"


class StubC(Interaction):
    # incompatible forking mode for the mode-mismatch test
    forking = ForkingMode.FORKING_WITHOUT_CTXT
    fork_allowed_tools = [TOOL_ANSWER_INDEXES, TOOL_SEARCH]

    async def prompt(self, indent, file):
        file.write("PROMPT_C")

    async def answer(self, payload):
        return "C_ANSWER"


class StubB_TargetGoal(Interaction):
    # same forking mode as StubA, but a DIFFERENT answer tool, to verify the
    # appended hint names the swapped-in interaction's own tool.
    forking = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools = [TOOL_ANSWER_TARGET_GOAL, TOOL_SEARCH]

    async def prompt(self, indent, file):
        file.write("PROMPT_B_TG")  # deliberately does NOT name any answer tool

    async def answer(self, payload):
        return "B_TG_ANSWER"


# --- minimal Session double --------------------------------------------------

class FakeSession:
    """Just enough of Session for _answer_tool_dispatch; reuses the real
    fork_pending / replace_pending_interaction so the code under test runs.

    `is_major` is configurable: real forks are NON-major (they have a parent),
    so the `if not session.is_major: await session.interrupt()` resolve path
    only fires when is_major is False. Tests cover both."""

    def __init__(self, role, is_major=True):
        self.role = role
        self.is_major = is_major
        self.logs = []

    def interrupted(self):
        return any(kind == "interrupt" for kind, _a, _b in self.logs)

    def tool_name(self, t):
        return t  # identity for the test

    def log_tool_call(self, tn, args):
        self.logs.append(("call", tn, args))

    def log_tool_response(self, tn, msg):
        self.logs.append(("response", tn, msg))

    def log_interaction(self, tn, msg):
        self.logs.append(("interaction", tn, msg))

    async def interrupt(self):
        self.logs.append(("interrupt", None, None))

    # reuse the real implementations under test
    fork_pending = Session.fork_pending
    replace_pending_interaction = Session.replace_pending_interaction


def _new_role(interaction):
    fut = asyncio.get_event_loop().create_future()
    return Role_Interaction(
        pending=Fork_Pending(interaction, fut),
        prompt="", resume_id=None, mode=ForkingMode.FORKING_WITH_CTXT)


# --- tests -------------------------------------------------------------------

async def test_swap():
    stub_b = StubB()
    stub_a = StubA(ContinuingInteraction(new_interaction=stub_b))
    role = _new_role(stub_a)
    fut = role.pending.answer
    session = FakeSession(role)

    text, is_error = await _answer_tool_dispatch(session, "answer_indexes", {"indexes": []})

    assert is_error is False, "swap should not be an error"
    assert session.fork_pending.interaction is stub_b, "pending must now be stub_b"
    assert session.fork_pending.answer is fut, "answer future must be reused"
    assert not fut.done(), "fork must stay alive (future not resolved)"
    assert "PROMPT_B" in text, f"text must be stub_b's prompt, got: {text!r}"
    assert "answer_indexes" in text, f"text must carry answer-tool hint, got: {text!r}"
    assert any(kind == "interaction" and "interaction replaced" in msg
               for kind, _tn, msg in session.logs), "replacement must be logged"
    assert not session.interrupted(), "swap keeps the fork alive; must NOT interrupt"
    print("test_swap: PASS")


async def test_immediate_answer_on_replacement():
    # run under both is_major settings; real forks are NON-major.
    for is_major in (True, False):
        stub_b = StubB(prompt_raises=ImmediateAnswer("IMMEDIATE_PAYLOAD"))
        stub_a = StubA(ContinuingInteraction(new_interaction=stub_b))
        role = _new_role(stub_a)
        fut = role.pending.answer
        session = FakeSession(role, is_major=is_major)

        text, is_error = await _answer_tool_dispatch(session, "answer_indexes", {"indexes": []})

        assert is_error is False
        assert fut.done(), "original future must be resolved by ImmediateAnswer path"
        assert fut.result() == "IMMEDIATE_PAYLOAD", f"got {fut.result()!r}"
        # no swap happened: pending interaction is left as stub_a
        assert session.fork_pending.interaction is stub_a, "must NOT swap on ImmediateAnswer"
        assert "IMMEDIATE_PAYLOAD" in text
        # distinct log line for the replaced+resolved branch (not plain "answered")
        assert any(kind == "interaction" and "interaction replaced+resolved" in msg
                   for kind, _tn, msg in session.logs), "replaced+resolved must be logged"
        # interrupt() fires iff the fork is non-major
        assert session.interrupted() == (not is_major), \
            f"interrupt expected={not is_major} for is_major={is_major}"
    print("test_immediate_answer_on_replacement: PASS")


async def test_plain_resolve_interrupt_path():
    # answer() returns a value normally -> the future is resolved and interrupt()
    # fires iff non-major. (Covers the non-ContinuingInteraction resolve tail.)
    for is_major in (True, False):
        stub_a = StubA(result="A_RESULT")
        role = _new_role(stub_a)
        fut = role.pending.answer
        session = FakeSession(role, is_major=is_major)

        text, is_error = await _answer_tool_dispatch(session, "answer_indexes", {"indexes": []})

        assert is_error is False
        assert fut.done() and fut.result() == "A_RESULT", f"got {text!r}"
        assert session.interrupted() == (not is_major), \
            f"interrupt expected={not is_major} for is_major={is_major}"
    print("test_plain_resolve_interrupt_path: PASS")


async def test_swap_changes_answer_tool():
    # swap to an interaction whose answer tool DIFFERS from the original's;
    # the appended hint must name the new interaction's tool (answer_target_goal),
    # not the original (answer_indexes).
    stub_b = StubB_TargetGoal()
    stub_a = StubA(ContinuingInteraction(new_interaction=stub_b))
    role = _new_role(stub_a)
    session = FakeSession(role)

    text, is_error = await _answer_tool_dispatch(session, "answer_indexes", {"indexes": []})

    assert is_error is False
    assert session.fork_pending.interaction is stub_b, "pending must now be stub_b"
    assert "PROMPT_B_TG" in text
    assert "answer_target_goal" in text, \
        f"hint must name the swapped-in interaction's tool, got: {text!r}"
    assert "answer_indexes" not in text, \
        f"hint must NOT name the original interaction's tool, got: {text!r}"
    print("test_swap_changes_answer_tool: PASS")


async def test_mode_mismatch():
    role = _new_role(StubA(RuntimeError("unused")))
    session = FakeSession(role)
    raised = False
    try:
        session.replace_pending_interaction(StubC())
    except InternalError as e:
        raised = True
        assert "incompatible" in str(e), f"unexpected message: {e}"
    assert raised, "mode mismatch must raise InternalError"
    # pending unchanged after the failed swap
    assert isinstance(session.fork_pending.interaction, StubA)
    print("test_mode_mismatch: PASS")


async def test_reprompt_same_interaction_still_works():
    # regression: ContinuingInteraction(new_prompt=...) re-prompt path unchanged
    stub_a = StubA(ContinuingInteraction("RE_PROMPT_TEXT"))
    role = _new_role(stub_a)
    fut = role.pending.answer
    session = FakeSession(role)

    text, is_error = await _answer_tool_dispatch(session, "answer_indexes", {"indexes": []})

    assert is_error is False
    assert text == "RE_PROMPT_TEXT", f"got {text!r}"
    assert session.fork_pending.interaction is stub_a, "must stay same interaction"
    assert not fut.done()
    print("test_reprompt_same_interaction_still_works: PASS")


async def main():
    await test_swap()
    await test_immediate_answer_on_replacement()
    await test_plain_resolve_interrupt_path()
    await test_swap_changes_answer_tool()
    await test_mode_mismatch()
    await test_reprompt_same_interaction_still_works()
    print("\nALL TESTS PASS")


if __name__ == "__main__":
    asyncio.run(main())
