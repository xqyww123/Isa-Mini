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
from IsaMini.AoA.language_model_driver import _QuotaError, _TransientError
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


def test_interrupt_result_message_is_not_a_failure(drv):
    """THE regression guard. Every terminal AoA path ends its turn by calling
    interrupt() from an MCP tool handler, and the CLI answers with exactly this
    message. Classifying it as an error reported successful proofs as
    TechnicalFailure and destroyed Refresh."""
    drv._check_message_error(
        _result(is_error=True, subtype="error_during_execution", result=None))


def test_quota_result_message_stays_on_the_retry_rail(drv):
    """_check_result_error, not _check_message_error, owns ResultMessages: a usage
    cap must keep reaching _QuotaError (wait 20 min) rather than becoming fatal."""
    drv._check_message_error(
        _result(is_error=True, result="You've hit your limit for today"))
    with pytest.raises(_QuotaError):
        drv._check_result_error(
            _result(is_error=True, result="You've hit your limit for today"))


def test_healthy_messages_do_not_raise(drv):
    drv._check_message_error(_assistant(text="Let me look at the goal."))
    drv._check_message_error(_result(is_error=False, result="done"))


# --- routing to the existing rails ------------------------------------------

@pytest.mark.parametrize("err", ["billing_error", "invalid_request", "unknown",
                                 "rate_limit", "server_error"])
def test_every_other_enum_value_is_left_alone(drv, err):
    """ONE value is classified here, not a catch-all. rate_limit / server_error keep
    their existing owners (_check_error_text -> _QuotaError / _TransientError); the rest
    have never been observed, and an unrecognised signal must not become a terminal
    verdict -- that is what broke successful proofs, Surrender/Refute and Refresh."""
    drv._check_message_error(_assistant(error=err, text="whatever"))


def test_model_text_is_carried_into_the_message(drv):
    """The CLI's own words matter: a relay signalling an exhausted quota with HTTP 403
    also arrives as authentication_failed, where "/login" alone is wrong advice."""
    with pytest.raises(LMUnreachable) as e:
        drv._check_message_error(
            _assistant(error="authentication_failed", text="403 quota exhausted"))
    assert "403 quota exhausted" in str(e.value)


def test_unrecognised_result_message_is_left_alone(drv):
    """No is_error fail-safe on ResultMessage in AoA — see the docstring on
    _check_message_error for why an is_error result is normal here."""
    drv._check_message_error(_result(is_error=True, result="something novel"))
