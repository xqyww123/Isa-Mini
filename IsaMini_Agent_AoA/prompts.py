"""
Centralized prompt strings and templates for ClaudeCode driver.
All user-facing messages, error messages, and prompt texts are defined here.
"""

from typing import Any
from . import model
from .model import Node, Root
from io import StringIO
from .helper import MyIO

# ============================================================================
# MCP Tool Descriptions
# ============================================================================

EDIT_TOOL_DESCRIPTION = "Edit the proof.yaml file"


# ============================================================================
# Edit Action Response Messages
# ============================================================================

async def filled_step_message(step: str, root: Root, node: Node, session: 'model.Session') -> str:
    """Message returned when a step is successfully filled."""
    file = MyIO(StringIO())
    file.write(f"Filled {node.titled_id}.\n")
    parent = node.parent
    if parent is not None:
        goal_and_to_file = parent.should_I_show_pending_goal()
        goal_id = parent.id_of_goal()
        if goal_and_to_file is not None:
            goal, step_to_fill = goal_and_to_file
            file.write(f"Call command `edit` with action `fill` and target step `{step_to_fill}`"
                " to provide the proof.\n")
        elif goal_id is not None and not parent.does_quickview_need_detail():
            file.write(f"All proof goals of {parent.titled_id} are completed.\n")
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Overall outline:\n")
    root.quickview(1, file)
    root.reset_changed()
    unfinished = set()
    root.unfinished_nodes(unfinished)
    if not unfinished:
        file.write("Congratulations! All goals are proven.\n")
        await session.interrupt()
    root.reset()
    return file.getvalue()

# ============================================================================
# Not Implemented Error Messages
# ============================================================================

NOT_IMPLEMENTED_INSERT_BEFORE = "insert_before is not implemented"


async def inserted_before_step_message(step: str, root: Root, node: Node, session: 'model.Session') -> str:
    """Message returned when a step is successfully inserted before another."""
    file = MyIO(StringIO())
    file.write(f"Inserted step {node.id} before step {step}.\n")
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Overall outline:\n")
    root.quickview(1, file)
    root.reset_changed()
    unfinished = set()
    root.unfinished_nodes(unfinished)
    if not unfinished:
        file.write("Congratulations! All goals are proven.\n")
        await session.interrupt()
    root.reset()
    return file.getvalue()
NOT_IMPLEMENTED_AMEND = "amend is not implemented"


async def amended_step_message(step: str, root: Root, node: Node, session: 'model.Session') -> str:
    """Message returned when a step is successfully amended."""
    file = MyIO(StringIO())
    file.write(f"Amended step {step}.\n")
    parent = node.parent
    if parent is not None:
        goal_and_to_file = parent.should_I_show_pending_goal()
        goal_id = parent.id_of_goal()
        if goal_and_to_file is not None:
            goal, step_to_fill = goal_and_to_file
            file.write(f"Call command `edit` with action `fill` and target step `{step_to_fill}`"
                " to provide the proof.\n")
        elif goal_id is not None and not parent.does_quickview_need_detail():
            file.write(f"All proof goals of {parent.titled_id} are completed.\n")
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Overall outline:\n")
    root.quickview(1, file)
    root.reset_changed()
    unfinished = set()
    root.unfinished_nodes(unfinished)
    if not unfinished:
        file.write("Congratulations! All goals are proven.\n")
        await session.interrupt()
    root.reset()
    return file.getvalue()
def unapplied_batch_warning(unapplied: list[dict], failure: Exception, failed_idx: int) -> str:
    """Render a single aggregated warning string for the unapplied tail of a
    multi-item edit batch.  Includes the underlying failure reason and the
    verbatim content of every operation starting from the failing index, so
    the agent can re-submit any of them at the right location."""
    import yaml as _yaml
    reason = str(failure) if failure is not None else "unknown"
    dump = _yaml.safe_dump(unapplied, default_flow_style=False,
                           allow_unicode=True, sort_keys=False, width=120).rstrip()
    return (
        f"{len(unapplied)} operation(s) from this edit batch were not applied "
        f"(starting at index {failed_idx}). Reason: {reason}. "
        f"Previously-committed items in this batch remain in the tree. "
        f"You may re-submit any unapplied operation at the appropriate "
        f"location on a later tool call. Unapplied operations:\n{dump}")


async def batch_edit_message(
    action: str, target_step: str, root: Root,
    committed: list[Node], session: 'model.Session',
    failure: Exception | None,
) -> str:
    """Response message for a multi-item edit batch.

    Shows which ops landed (if any), emits the ``session.warnings`` block
    (including the aggregated unapplied-batch warning), then renders the
    overall quickview.  Mirrors the single-op templates' structure so the
    agent's expectations are preserved."""
    file = MyIO(StringIO())
    if committed:
        ids = ", ".join(n.titled_id for n in committed)
        if action == "fill":
            verb = "Filled"
        elif action == "insert_before":
            verb = "Inserted"
        elif action == "amend":
            verb = "Amended at"
        else:
            verb = "Applied"
        file.write(
            f"{verb} {len(committed)} step(s) at target {target_step}: {ids}.\n")
        # Show pending-proof hint if the last committed node's parent still has
        # a pending goal (mirrors the single-op messages).
        last = committed[-1]
        parent = last.parent
        if parent is not None:
            goal_and_to_file = parent.should_I_show_pending_goal()
            goal_id = parent.id_of_goal()
            if goal_and_to_file is not None:
                _, step_to_fill = goal_and_to_file
                file.write(
                    f"Call command `edit` with action `fill` and target step "
                    f"`{step_to_fill}` to provide the proof.\n")
            elif goal_id is not None and not parent.does_quickview_need_detail():
                file.write(
                    f"All proof goals of {parent.titled_id} are completed.\n")
    else:
        # Nothing applied — report the failure cause.
        if failure is not None:
            file.write(f"No operations from this batch were applied: {failure}\n")
        else:
            file.write("No operations from this batch were applied.\n")
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Overall outline:\n")
    root.quickview(1, file)
    root.reset_changed()
    unfinished = set()
    root.unfinished_nodes(unfinished)
    if not unfinished:
        file.write("Congratulations! All goals are proven.\n")
        await session.interrupt()
    root.reset()
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
    file.write("Overall outline:\n")
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
# Test/Debug Messages
# ============================================================================

INITIAL_PROMPT =\
"""A proof goal and an incomplete proof are provided in `./proof.yaml` under the current directory.
`mcp__proof__edit` and `mcp__proof__delete` are the tools to edit the proof.yaml.
Analyze the proof goal, plan a proof, and complete it using the tools.
Continue building the proof until `proof.yaml` contains no errors.
"""

def RETRY_PROMPT(unfinished_nodes: set[Node]) -> str:
    return (
    f"Steps {', '.join([node.id for node in unfinished_nodes])} are incomplete. "
    "You must call the `mcp__proof__edit` tool to complete the steps. "
    "Continue building the proof until `proof.yaml` contains no remaining errors."
)
