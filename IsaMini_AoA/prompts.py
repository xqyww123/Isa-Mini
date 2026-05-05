"""
Centralized prompt strings and templates for ClaudeCode driver.
All user-facing messages, error messages, and prompt texts are defined here.
"""

from typing import Any
from . import model
from .model import Node, NonLeaf_Node, Root, Parsed_Opr, FailureReason
from .model import tn, TOOL_EDIT, TOOL_DELETE, TOOL_SEARCH, TOOL_ANSWER, TOOL_READ
from io import StringIO
from .helper import MyIO

# ============================================================================
# MCP Tool Descriptions
# ============================================================================

EDIT_TOOL_DESCRIPTION = "Edit the proof.yaml file"


# ============================================================================
# Edit Action Response Messages
# ============================================================================

_VERB = {
    model.EditOperation.FILL: "Filled",
    model.EditOperation.INSERT: "Inserted",
    model.EditOperation.AMEND: "Amended",
}


def _headline(outcome: 'model.EditOutcome') -> str:
    verb = _VERB[outcome.operation]
    c = outcome.committed
    if not c:
        return f"{verb} nothing.\n"
    if len(c) == 1:
        return f"{verb} step {c[0].id}.\n"
    return f"{verb} step {c[0].id}-{c[-1].id}.\n"


def _render_auto_intro_warning(session: 'model.Session', file: MyIO) -> None:
    if not session.auto_intro_nodes:
        return
    live = [n for n in session.auto_intro_nodes if n.parent is not None and n in n.parent.sub_nodes]
    session.auto_intro_nodes.clear()
    if not live:
        return
    ids = ', '.join(n.id for n in live)
    noun = "steps" if len(live) > 1 else "step"
    file.write(
        f"Note: {noun} {ids} {'were' if len(live) > 1 else 'was'} "
        f"auto-introduced. You may delete {'them' if len(live) > 1 else 'it'} "
        f"using {tn(TOOL_DELETE)} if unhelpful.\n"
    )


async def edit_message(
    root: Root,
    outcome: 'model.EditOutcome',
    session: 'model.Session',
) -> str:
    """Response for `fill` / `insert_before` / `amend`, dispatched on
    `outcome.operation`.

    If `outcome.failure.is_error`, `str(failure)` is prepended to the
    response.  If `failure` is set but `is_error=False`, it is appended."""
    failure = outcome.failure
    file = MyIO(StringIO())
    file.write(_headline(outcome))
    if failure is not None and failure.is_error:
        file.write(str(failure))
        file.write("\n")
    _p = outcome.committed[-1].parent if outcome.committed else None
    parent_hint = _p if isinstance(_p, NonLeaf_Node) else None
    # Completion hint only for fill/amend; insert intentionally skips it.
    if parent_hint is not None and outcome.operation is not model.EditOperation.INSERT:
        goal_id = parent_hint.id_of_goal()
        if (goal_id is not None
                and parent_hint.should_I_show_pending_goal() is None
                and not parent_hint.does_quickview_need_detail()):
            file.write(f"All proof goals of {parent_hint.titled_id} are completed.\n")
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    if outcome.committed:
        file.write("Outline:\n")
        root.quickview(1, file)
        root.reset_changed()
        _render_auto_intro_warning(session, file)
        unfinished = set()
        root.unfinished_nodes(unfinished)
        if not unfinished:
            file.write("Congratulations! All goals are proven.\n")
            await session.interrupt()
        root.reset()
    if failure is not None and not failure.is_error:
        file.write(str(failure))
        file.write("\n")
    return file.getvalue()


async def deleted_steps_message(steps: list[str], root: Root, session: 'model.Session') -> str:
    """Message returned when steps are successfully deleted."""
    file = MyIO(StringIO())
    noun = "steps" if len(steps) > 1 else "step"
    file.write(f"Deleted {noun} {', '.join(steps)}.\n")
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Outline:\n")
    root.quickview(1, file)
    root.reset_changed()
    _render_auto_intro_warning(session, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    if not unfinished:
        file.write("Congratulations! All goals are proven.\n")
        await session.interrupt()
    return file.getvalue()


# ============================================================================
# Edit Action Error Messages
# ============================================================================

def invalid_action_error(action: str) -> str:
    """Error message for invalid edit actions."""
    return (
        f"Invalid action: {action}. "
        f"Must be one of: 'fill', 'insert_before', or 'amend'. "
        f"Use the '{tn(TOOL_DELETE)}' tool to delete steps."
    )


# ============================================================================
# Permission Control - Tool Rejection Messages
# ============================================================================

def tool_not_allowed_base(tool: str) -> str:
    """Base rejection message for tools not in whitelist."""
    return f"Tool `{tool}` is not allowed."


def edit_tool_use_mcp_for_proof_yaml() -> str:
    return f" You should use the `{tn(TOOL_EDIT)}` tool to edit proof.yaml."

def edit_tool_only_proof_yaml() -> str:
    return (
        f" You cannot modify any files except proof.yaml, "
        f"and you must use the `{tn(TOOL_EDIT)}` tool to edit it."
    )

ASK_USER_QUESTION_REJECTION = (
    " You cannot ask the user any questions. "
    "You must complete the theorem proof independently."
)

BASH_REJECTION = (
    " You cannot run any Bash command; "
    "proof.yaml contains all the information you need."
)


# ============================================================================
# Permission Control - Path Access Messages
# ============================================================================

def path_access_denied(tool: str, yaml_path: str, target_path: str) -> str:
    """Message when tool tries to access a file other than the YAML file."""
    return (
        f"{tool} operation can only access ./proof.yaml, "
        f"access denied for: {target_path}"
    )


# ============================================================================
# System Prompt & Initial User Prompt
# ============================================================================

def system_prompt() -> str:
    return (
        "You are a formal theorem proving agent.\n"
        "A proof goal and an incomplete proof are provided in `./proof.yaml` under the current directory.\n"
        "Analyze the proof goal, plan a proof, and complete it using the MCP proof tools.\n"
        "Continue until no errors remain.\n"
        "Be concise in text output.\n"
        "\n"
        "## Tools\n"
        f"- {tn(TOOL_EDIT)}: Fill, insert, or amend proof steps (your primary tool)\n"
        f"- {tn(TOOL_DELETE)}: Delete proof steps\n"
        f"- {tn(TOOL_SEARCH)}: Search for theorems, constants, types, and rules; help you understand unfamiliar terms\n"
        f"- {tn(TOOL_READ)}: Read `proof.yaml`. Use only when necessary.\n"
    )

def INITIAL_PROMPT(root: Root) -> str:
    from .model import the_session
    session = the_session()
    if session.has_system_prompt:
        buf = StringIO()
        root.print(0, MyIO(buf), update_line=True, show_warnings=True)
        return (
            "Complete the following proof using the MCP proof tools.\n"
            + buf.getvalue()
            + "\n`proof.yaml` contains the full proof state, but read it only when you lose track of it."
        )
    else:
        buf = StringIO()
        root.print(0, MyIO(buf), update_line=True, show_warnings=True)
        return (
            "An incomplete proof is provided as follows\n"
            + buf.getvalue() +
            f"Analyze the proof goal, plan a proof, and complete it using tools `{tn(TOOL_EDIT)}` and `{tn(TOOL_DELETE)}`.\n"
            "Continue building the proof until no error remains.\n"
            "`proof.yaml` contains the full proof state, but read it only when you lose track of it."
        )

def RETRY_PROMPT(unfinished_nodes: set[Node]) -> str:
    return (
    f"Steps {', '.join([node.id for node in unfinished_nodes])} are incomplete. "
    f"You must call the `{tn(TOOL_EDIT)}` tool to complete the steps. "
    "Continue building the proof until `proof.yaml` contains no remaining errors."
)
