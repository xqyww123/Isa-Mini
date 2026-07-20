"""Tests for ClaudeCode._check_message_error.

The regression these guard: an unauthenticated Claude Code CLI raises nothing.
`connect()` succeeds and the failure arrives as ordinary messages -- an
AssistantMessage carrying error='authentication_failed' (whose text block reads
like model output), then a ResultMessage whose `subtype` still says 'success'.

Before this classifier existed, `_check_error_text` matched neither ("You've hit
your limit" / "Rate limit"), so nothing raised: the agent made no progress, the
retry loop span to max_retries, and the run ended as
ResourceExhausted("retry limit") -- an infrastructure failure reported as a proof
failure, with cost $0 and zero tool calls as the only clue.
"""
import pytest
from claude_agent_sdk import ResultMessage
from claude_agent_sdk.types import AssistantMessage, TextBlock

from IsaMini.AoA.driver_claude_code import ClaudeCode
from IsaMini.AoA.language_model_driver import _QuotaError, _TransientError, _TechnicalError
from IsaMini.AoA.model import LMUnreachable


@pytest.fixture
def drv():
    # __init__ needs a live Session/Connection; _check_message_error only touches
    # _model_error_detail (a staticmethod), so a bare instance is enough.
    return object.__new__(ClaudeCode)


def _result(**kw):
    base = dict(subtype="success", duration_ms=100, duration_api_ms=0,
                is_error=False, num_turns=1, session_id="s")
    base.update(kw)
    return ResultMessage(**base)


def _assistant(error=None, text=None):
    content = [TextBlock(text=text)] if text else []
    return AssistantMessage(content=content, model="m", error=error)


# --- the headline case ------------------------------------------------------

def test_unauthenticated_assistant_message_gives_up_via_lm_unreachable(drv):
    with pytest.raises(LMUnreachable) as e:
        drv._check_message_error(
            _assistant(error="authentication_failed",
                       text="Failed to authenticate. API Error: 403"))
    # The remedy, and the model's own words -- the latter matter because a relay
    # that signals an exhausted quota with HTTP 403 also lands here.
    assert "/login" in str(e.value)
    assert "403" in str(e.value)


def test_unauthenticated_result_message_is_caught_by_the_fail_safe(drv):
    """is_error is True while subtype still reads 'success'; branching on subtype
    would miss it entirely."""
    with pytest.raises(_TechnicalError):
        drv._check_message_error(
            _result(is_error=True, subtype="success",
                    result="Not logged in · Please run /login"))


def test_healthy_messages_do_not_raise(drv):
    drv._check_message_error(_assistant(text="Let me look at the goal."))
    drv._check_message_error(_result(is_error=False, result="done"))


# --- routing to the existing rails ------------------------------------------

@pytest.mark.parametrize("err,exc", [
    ("rate_limit", _QuotaError),        # existing rail: wait 20 min, retry
    ("server_error", _TransientError),  # existing rail: wait 2 s, retry
    ("authentication_failed", LMUnreachable),
    ("billing_error", LMUnreachable),
    ("invalid_request", _TechnicalError),
    ("unknown", _TechnicalError),
])
def test_each_error_class_takes_its_own_rail(drv, err, exc):
    with pytest.raises(exc):
        drv._check_message_error(_assistant(error=err, text="whatever"))


def test_model_text_is_carried_into_the_message(drv):
    with pytest.raises(_TechnicalError) as e:
        drv._check_message_error(
            _assistant(error="invalid_request", text="tool schema rejected"))
    assert "tool schema rejected" in str(e.value)


def test_result_message_detail_falls_back_to_its_result_text(drv):
    with pytest.raises(_TechnicalError) as e:
        drv._check_message_error(_result(is_error=True, result="something novel"))
    assert "something novel" in str(e.value)
