"""AoA configuration switches, and the agent-facing wording they gate.

Module-level globals that toggle AoA agent behavior, together with the small
pieces of agent-facing text whose presence those switches control. Kept
dependency-free (no imports from the rest of the package) so any module can
import it cheaply, and so a gated string has a SINGLE source of truth: the
`request`-tool description is assembled here once and imported by both
``model.py`` (the system-prompt tool list) and ``mcp_http_server.py`` (the MCP
tool advertisement), so the two copies cannot drift.
"""

# When True, two agent-facing reminders are shown: (1) the `request`-tool
# description carries a reminder that requesting a general lemma dispatches a
# sub-agent to prove it (which burns tokens) and so should be done only when
# necessary; (2) both `subagent`-tool descriptions carry a cost caution that
# dispatching a sub-agent is expensive. Set False to drop both reminders; the
# factual base descriptions are kept either way.
REMIND_REQUEST_ONLY_WHEN_NECESSARY = False

# Base (ALWAYS shown): the two things `request` does. States — factually, in
# place of the misleading word "auto-proved" — that a dispatched sub-agent is
# what proves a requested general lemma and brings it into scope.
_REQUEST_TOOL_BASE = (
    "Report constraints your sub-goal is missing, and/or request general lemmas "
    "to be proved by an auto-dispatched sub-agent and then made available in "
    "your scope."
)

# Caution (shown only when REMIND_REQUEST_ONLY_WHEN_NECESSARY): the cost nudge.
_REQUEST_TOOL_CAUTION = (
    " Proving the lemmas burns tokens. Request general lemmas only when "
    "necessary. Do not request a fully general lemma that is harder to prove "
    "than your specific case. Consider whether a trick tailored to your case is "
    "more efficient."
)

# When True (the current default), a worker may no longer request GENERAL lemmas
# via `request` (the path that auto-dispatches a headless prover sub-agent — the
# token burn). Such a request is rejected with a nudge to prove the needed
# special case directly; any `constraints` in the same call are still processed;
# the `request` tool description and JSON schema drop the general-lemma part; and
# the worker system-prompt guidance drops the "raise a request" option. The
# requested lemmas are STILL mirrored into missing_lemmas.yaml (the external
# import-expansion loop's signal is kept). Set back to False to restore the old
# behavior byte-identical. Deployment-static: the MCP tool advertisement and
# schema resolve once at import, so set this before the process starts.
DISABLE_REQUEST_GENERAL_LEMMAS = True

# Shown (in place of the base) when DISABLE_REQUEST_GENERAL_LEMMAS is on: only the
# constraint half of `request` remains, so the description advertises just that.
_REQUEST_TOOL_BASE_NO_GENERAL = "Report constraints your sub-goal is missing."

# Rejection shown to a worker that requested general lemmas while the gate is on
# (the general lemmas are dropped; constraints, if any, are still processed).
DISABLED_GENERAL_LEMMA_REQUEST_MSG = (
    "Requesting general lemmas is disabled for this case. Instead of a general "
    "lemma, prove the specific instance your sub-goal needs directly (e.g. "
    "inline as a `Have`).")


def request_tool_description() -> str:
    """The `request`-tool description shown to the agent. When general-lemma
    requests are disabled, only the constraint half remains; otherwise the
    factual base, plus the cost caution when ``REMIND_REQUEST_ONLY_WHEN_NECESSARY``
    is on."""
    if DISABLE_REQUEST_GENERAL_LEMMAS:
        return _REQUEST_TOOL_BASE_NO_GENERAL
    if REMIND_REQUEST_ONLY_WHEN_NECESSARY:
        return _REQUEST_TOOL_BASE + _REQUEST_TOOL_CAUTION
    return _REQUEST_TOOL_BASE


# Caution (shown only when REMIND_REQUEST_ONLY_WHEN_NECESSARY): the cost nudge
# for dispatching a sub-agent. Appended to BOTH `subagent`-tool descriptions —
# the system-prompt tool list (``model.py``) and the MCP advertisement
# (``mcp_http_server.py``) — from this single source so the two cannot drift.
_SUBAGENT_TOOL_CAUTION = (
    " Dispatching a sub-agent spawns a whole separate proving agent and burns "
    "a large amount of tokens. Dispatch a sub-agent only when necessary."
)


def subagent_cost_caution() -> str:
    """The cost caution appended to the `subagent`-tool descriptions when
    ``REMIND_REQUEST_ONLY_WHEN_NECESSARY`` is on; empty string otherwise."""
    return _SUBAGENT_TOOL_CAUTION if REMIND_REQUEST_ONLY_WHEN_NECESSARY else ""
