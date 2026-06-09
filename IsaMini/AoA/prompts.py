"""
Tool response messages, error messages, and rejection texts.
System/initial/retry prompts are methods on Session (model.py).
"""

from . import model
from .model import Node, NonLeaf_Node, Root
from .model import tn, TOOL_EDIT, TOOL_DELETE, TOOL_COMMENT, CommentOutcome
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


def _headline(outcome: 'model.EditOutcome', session: 'model.Session') -> str:
    verb = _VERB[outcome.operation]
    c = outcome.committed
    if not c:
        return f"{verb} nothing.\n"
    if len(c) == 1:
        return f"{verb} step {session._display_id(c[0].id)}.\n"
    return f"{verb} step {session._display_id(c[0].id)}-{session._display_id(c[-1].id)}.\n"


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


def _write_newly_completed(session: 'model.Session', file: MyIO) -> None:
    """Append one line naming the steps whose whole subtree became proved this
    call and were not announced before (delta, top-most/no-overlap — see
    `Session.newly_completed_topmost`). Writes nothing when there are none,
    which includes the case where the entire scope is now proved (reported via
    the caller's "all goals proven" path instead)."""
    newly = session.newly_completed_topmost()
    if not newly:
        return
    ids = ', '.join(n.titled_id for n in newly)
    file.write(f"All proof goals of {ids} are now completed.\n")


def _render_auto_intro_warning(session: 'model.Session', file: MyIO) -> None:
    if not session.auto_intro_nodes:
        return
    live = [n for n in session.auto_intro_nodes if n.parent is not None and n in n.parent.sub_nodes]
    session.auto_intro_nodes.clear()
    if not live:
        return
    ids = ', '.join(session._display_id(n.id) for n in live)
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
    file.write(_headline(outcome, session))
    if failure is not None and failure.is_error:
        file.write(str(failure))
        file.write("\n")
    # Report steps newly proved this call — unconditionally (even when the edit
    # failed or committed nothing): a reverted/no-op edit can still flip a step
    # to proved as a side effect, and the agent must learn about it. Delta + top-
    # most/no-overlap is handled by `newly_completed_topmost`.
    _write_newly_completed(session, file)
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    if outcome.committed:
        file.write("Outline:\n")
        session.quickview_proof_scope(1, file)
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
    file.write(f"Deleted {noun} {', '.join(session._display_id(s) for s in steps)}.\n")
    _write_newly_completed(session, file)
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Outline:\n")
    session.quickview_proof_scope(1, file)
    _render_auto_intro_warning(session, file)
    unfinished = session.proof_scope_unfinished_nodes()
    if not unfinished:
        file.write("Congratulations! All goals are proven.\n")
        finished = True
    root.reset()
    return file.getvalue(), finished


async def comment_message(
    outcome: CommentOutcome,
    action: str,
    root: Root,
    session: 'model.Session',
) -> tuple[str, bool]:
    finished = False
    file = MyIO(StringIO())
    if outcome.affected:
        noun = "steps" if len(outcome.affected) > 1 else "step"
        ids = ', '.join(session._display_id(s) for s in outcome.affected)
        if action == "comment":
            file.write(f"Commented out {noun} {ids}.\n")
        else:
            file.write(f"Uncommented {noun} {ids}.\n")
    if outcome.not_found:
        noun = "steps" if len(outcome.not_found) > 1 else "step"
        ids = ', '.join(session._display_id(s) for s in outcome.not_found)
        file.write(f"Warning: {noun} {ids} not found.\n")
    for w in outcome.warnings:
        file.write(f"Warning: {w}\n")
    _write_newly_completed(session, file)
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Outline:\n")
    session.quickview_proof_scope(1, file)
    _render_auto_intro_warning(session, file)
    unfinished = session.proof_scope_unfinished_nodes()
    if not unfinished:
        file.write("Congratulations! All goals are proven.\n")
        finished = True
    root.reset()
    return file.getvalue(), finished


async def subagent_overall(root: Root, session: 'model.Session') -> tuple[str, bool]:
    """Whole-proof outline tail appended to every `subagent` outcome, mirroring
    `edit_message`'s `Outline:` section (same quickview + reset bookkeeping)
    under an `Overall:` header. Returns `(text, finished)` where `finished` is
    `not unfinished` — whether the sub-agent's work discharged the last open
    goal (the caller acts on it, e.g. `session.interrupt()`).

    Unlike `edit_message` it does NOT bump `session.age`: the worker already
    advanced the render generation during its run, and its edits set each
    touched node's `changed` flag directly, so the quickview still highlights
    them; the trailing `root.reset()` then clears those flags (and the node
    warnings) as `edit_message` does."""
    finished = False
    file = MyIO(StringIO())
    file.write("Overall:\n")
    # Scope the outline to the dispatcher's own proof scope: the whole `root` for
    # the main agent (proof_scope_root IS root), or just the target subtree for a
    # worker dispatcher — consistent with `print_proof_scope`.
    session.proof_scope_root.quickview(1, file)
    if not session.proof_scope_unfinished_nodes():
        file.write("Congratulations! All goals are proven.\n")
        finished = True
    root.reset()
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


