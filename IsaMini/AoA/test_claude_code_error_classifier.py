"""Tests for ClaudeCode._classify_message (né _check_message_error).

Two regressions these guard:

1. An unauthenticated Claude Code CLI raises nothing. `connect()` succeeds and
   the failure arrives as ordinary messages -- an AssistantMessage carrying
   error='authentication_failed' (whose text block reads like model output),
   then a ResultMessage whose `subtype` still says 'success'. Before this
   classifier existed, nothing raised: the agent made no progress, the retry
   loop span to max_retries, and the run ended as ResourceExhausted("retry
   limit") -- an infrastructure failure reported as a proof failure.

2. A corrupted conversation history (a lone UTF-16 surrogate the CLI stored in
   an assistant message) makes every subsequent request 400 at the same
   position. The CLI's synthetic 400 notice used to be treated as model
   output, so 8/8 retries burned on a doomed session. _classify_message now
   raises _CorruptedHistoryError, and only for SYNTHETIC messages -- real
   model prose is never pattern-matched (so a model *writing* "Rate limit"
   no longer trips the quota rail either).
"""
import pytest
from claude_agent_sdk import ResultMessage
from claude_agent_sdk.types import AssistantMessage, TextBlock

from IsaMini.AoA.driver_claude_code import ClaudeCode, _CorruptedHistoryError
from IsaMini.AoA.language_model_driver import _QuotaError, _TransientError
from IsaMini.AoA.model import LMUnreachable

# The incident's verbatim notice (log 0233B0025_ECFBF4, 8 identical turns).
CORRUPT_400 = ("API Error: 400 The request body is not valid JSON: "
               "no low surrogate in string: line 1 column 16547 (char 16546)")


@pytest.fixture
def drv():
    # __init__ needs a live Session/Connection; _classify_message only touches
    # _model_error_detail (a staticmethod), so a bare instance is enough.
    return object.__new__(ClaudeCode)


def _result(**kw):
    base = dict(subtype="success", duration_ms=100, duration_api_ms=0,
                is_error=False, num_turns=1, session_id="s")
    base.update(kw)
    return ResultMessage(**base)


def _assistant(error=None, text=None, model="m"):
    content = [TextBlock(text=text)] if text else []
    return AssistantMessage(content=content, model=model, error=error)


# --- the headline cases -----------------------------------------------------

def test_unauthenticated_assistant_message_gives_up_via_lm_unreachable(drv):
    with pytest.raises(LMUnreachable) as e:
        drv._classify_message(
            _assistant(error="authentication_failed",
                       text="Failed to authenticate. API Error: 403"))
    # The remedy, and the model's own words -- the latter matter because a relay
    # that signals an exhausted quota with HTTP 403 also lands here.
    assert "/login" in str(e.value)
    assert "403" in str(e.value)


def test_corrupted_history_notice_with_error_field(drv):
    """The incident's exact shape: error='unknown' on all 8 rejected turns."""
    with pytest.raises(_CorruptedHistoryError) as e:
        drv._classify_message(_assistant(error="unknown", text=CORRUPT_400))
    assert "column 16547" in str(e.value)


def test_corrupted_history_notice_via_synthetic_model(drv):
    """The other gate path: no error field, but model == '<synthetic>'."""
    with pytest.raises(_CorruptedHistoryError):
        drv._classify_message(
            _assistant(text=CORRUPT_400, model="<synthetic>"))


def test_no_high_surrogate_variant(drv):
    """A lone LOW surrogate manifests as 'no high surrogate'."""
    with pytest.raises(_CorruptedHistoryError):
        drv._classify_message(_assistant(
            error="unknown",
            text=("API Error: 400 The request body is not valid JSON: "
                  "no high surrogate in string: line 1 column 3 (char 2)")))


def test_model_prose_is_never_classified(drv):
    """Regression lock on the old per-text-block _check_error_text calls: real
    model output containing the magic words must NOT trip any rail."""
    drv._classify_message(_assistant(
        text="Rate limit analysis: You've hit your limit is what a 429 means. "
             + CORRUPT_400))


def test_synthetic_quota_and_rate_limit_texts_keep_their_rails(drv):
    with pytest.raises(_QuotaError):
        drv._classify_message(
            _assistant(error="unknown", text="You've hit your limit until 3pm"))
    with pytest.raises(_TransientError):
        drv._classify_message(
            _assistant(error="unknown", text="API Error: Rate limit exceeded"))


def test_interrupt_result_message_is_not_a_failure(drv):
    """THE regression guard. Every terminal AoA path ends its turn by calling
    interrupt() from an MCP tool handler, and the CLI answers with exactly this
    message. Classifying it as an error reported successful proofs as
    TechnicalFailure and destroyed Refresh."""
    drv._classify_message(
        _result(is_error=True, subtype="error_during_execution", result=None))


def test_quota_result_message_stays_on_the_retry_rail(drv):
    """_check_result_error, not _classify_message, owns ResultMessages: a usage
    cap must keep reaching _QuotaError (wait 20 min) rather than becoming fatal."""
    drv._classify_message(
        _result(is_error=True, result="You've hit your limit for today"))
    with pytest.raises(_QuotaError):
        drv._check_result_error(
            _result(is_error=True, result="You've hit your limit for today"))


def test_healthy_messages_do_not_raise(drv):
    drv._classify_message(_assistant(text="Let me look at the goal."))
    drv._classify_message(_result(is_error=False, result="done"))


# --- routing to the existing rails ------------------------------------------

@pytest.mark.parametrize("err", ["billing_error", "invalid_request", "unknown",
                                 "rate_limit", "server_error"])
def test_unmatched_synthetic_errors_are_left_alone(drv, err):
    """ONE structural value (authentication_failed) is terminal; everything else
    is classified by its text, and an unrecognised signal must not become a
    terminal verdict -- that is what broke successful proofs, Surrender/Refute
    and Refresh."""
    drv._classify_message(_assistant(error=err, text="whatever"))


def test_model_text_is_carried_into_the_message(drv):
    """The CLI's own words matter: a relay signalling an exhausted quota with HTTP 403
    also arrives as authentication_failed, where "/login" alone is wrong advice."""
    with pytest.raises(LMUnreachable) as e:
        drv._classify_message(
            _assistant(error="authentication_failed", text="403 quota exhausted"))
    assert "403 quota exhausted" in str(e.value)


def test_unrecognised_result_message_is_left_alone(drv):
    """No is_error fail-safe on ResultMessage in AoA — see the docstring on
    _classify_message for why an is_error result is normal here."""
    drv._classify_message(_result(is_error=True, result="something novel"))
