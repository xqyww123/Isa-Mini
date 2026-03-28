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

def filled_step_message(step: str, root: Root, node: Node, session: 'model.Session') -> str:
    """Message returned when a step is successfully filled."""
    file = MyIO(StringIO())
    file.write(f"Successfully filled step {step}:\n")
    node.print(1, file, update_line=False)
    # Print any auto-generated nodes after the filled node (e.g., Intro)
    parent = node.parent
    if parent is not None:
        siblings = parent.sub_nodes
        idx = next((i for i, n in enumerate(siblings) if n is node), -1)
        for sibling in siblings[idx + 1:]:
            sibling.print(1, file, update_line=False)
    if parent is not None:
        goal_and_to_file = parent.should_I_show_pending_goal()
        goal_id = parent.id_of_goal()
        if goal_and_to_file is not None:
            goal, step_to_fill = goal_and_to_file
            if goal_id is None:
                file.write(f"Pending goal:\n")
            else:
                file.write(f"Pending goal of {goal_id}:\n")
            model.print_goal(goal, 1, False, file, parent._ctxt_of_filling())
            file.write(f"Call command `edit` with action `fill` and target step `{step_to_fill}`"
                " to provide the proof.\n")
        elif goal_id is not None:
            file.write(f"All proof goals of {goal_id} are completed.\n")
    # Print and reset session warnings
    if session.warnings:
        file.write("Warnings:\n")
        for w in session.warnings:
            file.write(f"  - {w}\n")
        session.warnings.clear()
    file.write("Overall outline:\n")
    root.quickview(1, file)
    root._print_all_warnings(file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    if not unfinished:
        file.write("Congratulations! All goals are proven. Terminate immediately without output!\n")
    return file.getvalue()

# ============================================================================
# Not Implemented Error Messages
# ============================================================================

NOT_IMPLEMENTED_INSERT_BEFORE = "insert_before is not implemented"
NOT_IMPLEMENTED_AMEND = "amend is not implemented"
NOT_IMPLEMENTED_DELETE = "delete is not implemented"
NOT_IMPLEMENTED_DELETE_ALL_AFTER = "delete_all_after is not implemented"


# ============================================================================
# Edit Action Error Messages
# ============================================================================

def invalid_action_error(action: str) -> str:
    """Error message for invalid edit actions."""
    return (
        f"Invalid action: {action}. "
        f"Must be either 'fill', 'insert_before', 'amend', 'delete', 'delete_all_after'."
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
`mcp__proof__edit` is the tool to edit the proof.yaml.
Analyze the proof goal, plan a proof, and complete it using the `mcp__proof__edit` tool.
Continue building the proof until `proof.yaml` contains no errors.
"""

def RETRY_PROMPT(unfinished_nodes: set[Node]) -> str:
    return (
    f"Steps {', '.join([node.id for node in unfinished_nodes])} are incomplete. "
    "You must call the `mcp__proof__edit` tool to complete the steps. "
    "Continue building the proof until `proof.yaml` contains no remaining errors."
)
