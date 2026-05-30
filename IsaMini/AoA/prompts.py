"""
Tool response messages, error messages, and rejection texts.
System/initial/retry prompts are methods on Session (model.py).
"""

from . import model
from .model import Node, NonLeaf_Node, Root
from .model import tn, TOOL_EDIT, TOOL_DELETE
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


def _collect_completed_ancestors(committed: list[Node]) -> list[str]:
    """Walk up from each committed node, collecting titled IDs of ancestors
    whose proof goals are all completed.  Stops climbing at the first
    ancestor that still has pending goals."""
    completed_ids: list[str] = []
    visited: set[int] = set()
    for node in committed:
        ancestor = node.parent
        while (ancestor is not None
               and isinstance(ancestor, NonLeaf_Node)
               and id(ancestor) not in visited):
            visited.add(id(ancestor))
            if ancestor.should_I_show_pending_goal() is not None:
                break
            if ancestor.does_quickview_need_detail():
                break
            goal_id = ancestor.id_of_goal()
            if goal_id is not None:
                completed_ids.append(ancestor.titled_id)
            ancestor = ancestor.parent
    return completed_ids


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
        f"using `{tn(TOOL_DELETE)}` if unhelpful.\n"
    )


async def edit_message(
    root: Root,
    outcome: 'model.EditOutcome',
    session: 'model.Session',
) -> tuple[str, bool]:
    """Response for `fill` / `insert_before` / `amend`, dispatched on
    `outcome.operation`.

    Returns `(message, finished)` where `finished` is `not unfinished`, i.e.
    whether the edit discharged every remaining goal in the proof scope. The
    caller is responsible for acting on `finished` (e.g. `session.interrupt()`).

    If `outcome.failure.is_error`, `str(failure)` is prepended to the
    response.  If `failure` is set but `is_error=False`, it is appended."""
    failure = outcome.failure
    finished = False
    file = MyIO(StringIO())
    file.write(_headline(outcome))
    if failure is not None and failure.is_error:
        file.write(str(failure))
        file.write("\n")
    # Completion hint only for fill/amend; insert intentionally skips it.
    if outcome.committed and outcome.operation is not model.EditOperation.INSERT:
        completed_ids = _collect_completed_ancestors(outcome.committed)
        if len(completed_ids) == 1:
            file.write(f"All proof goals of {completed_ids[0]} are completed.\n")
        elif completed_ids:
            file.write(f"All proof goals of {', '.join(completed_ids)} are completed.\n")
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    if outcome.committed:
        file.write("Outline:\n")
        session.quickview_proof_scope(1, file)
        root.reset_changed()
        _render_auto_intro_warning(session, file)
        unfinished = session.proof_scope_unfinished_nodes()
        if not unfinished:
            file.write("Congratulations! All goals are proven.\n")
            finished = True
        root.reset()
    if failure is not None and not failure.is_error:
        file.write(str(failure))
        file.write("\n")
    return file.getvalue(), finished


async def deleted_steps_message(steps: list[str], root: Root, session: 'model.Session') -> tuple[str, bool]:
    """Message returned when steps are successfully deleted.

    Returns `(message, finished)` where `finished` is `not unfinished`, i.e.
    whether deletion left every remaining goal in the proof scope discharged.
    The caller is responsible for acting on `finished` (e.g.
    `session.interrupt()`)."""
    finished = False
    file = MyIO(StringIO())
    noun = "steps" if len(steps) > 1 else "step"
    file.write(f"Deleted {noun} {', '.join(steps)}.\n")
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Outline:\n")
    session.quickview_proof_scope(1, file)
    root.reset_changed()
    _render_auto_intro_warning(session, file)
    unfinished = session.proof_scope_unfinished_nodes()
    if not unfinished:
        file.write("Congratulations! All goals are proven.\n")
        finished = True
    return file.getvalue(), finished


# ============================================================================
# Edit Action Error Messages
# ============================================================================

def invalid_action_error(action: str) -> str:
    """Error message for invalid edit actions."""
    return (
        f"Invalid action: {action}. "
        f"Must be one of: `fill`, `insert_before`, or `amend`. "
        f"Use the `{tn(TOOL_DELETE)}` tool to delete steps."
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


