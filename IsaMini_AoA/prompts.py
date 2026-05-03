"""
Centralized prompt strings and templates for ClaudeCode driver.
All user-facing messages, error messages, and prompt texts are defined here.
"""

from typing import Any
from . import model
from .model import Node, NonLeaf_Node, Root, Parsed_Opr, FailureReason
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
        f"Use the 'mcp__proof__delete' tool to delete steps."
    )


# ============================================================================
# Permission Control - Tool Rejection Messages
# ============================================================================

def tool_not_allowed_base(tool: str) -> str:
    """Base rejection message for tools not in whitelist."""
    return f"Tool `{tool}` is not allowed."


EDIT_TOOL_USE_MCP_FOR_PROOF_YAML = " You should use the `mcp__proof__edit` tool to edit proof.yaml."

EDIT_TOOL_ONLY_PROOF_YAML = (
    " You cannot modify any files except proof.yaml, "
    "and you must use the `mcp__proof__edit` tool to edit it."
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

SYSTEM_PROMPT = """\
You are a formal theorem proving agent.
A proof goal and an incomplete proof are provided in `./proof.yaml` under the current directory.
Analyze the proof goal, plan a proof, and complete it using the MCP proof tools.
Continue until no errors remain.
Be concise in text output.

## Tools
- mcp__proof__edit: Fill, insert, or amend proof steps (your primary tool)
- mcp__proof__delete: Delete proof steps
- mcp__proof__query: Search for theorems, constants, types, and rules; help you understand unfamiliar terms
- Read: Inspect ./proof.yaml to check the current proof state
"""

INITIAL_PROMPT = "Complete the proof in `./proof.yaml` using the MCP proof tools."

def RETRY_PROMPT(unfinished_nodes: set[Node]) -> str:
    return (
    f"Steps {', '.join([node.id for node in unfinished_nodes])} are incomplete. "
    "You must call the `mcp__proof__edit` tool to complete the steps. "
    "Continue building the proof until `proof.yaml` contains no remaining errors."
)
