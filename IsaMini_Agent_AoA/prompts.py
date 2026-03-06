"""
Centralized prompt strings and templates for ClaudeCode driver.
All user-facing messages, error messages, and prompt texts are defined here.
"""

from typing import Any
from .model import Node, Root
from io import StringIO

# ============================================================================
# MCP Tool Descriptions
# ============================================================================

EDIT_TOOL_DESCRIPTION = "Edit the proof.yaml file"


# ============================================================================
# Edit Action Response Messages
# ============================================================================

def filled_step_message(step: str, root: Root, node: Node) -> str:
    """Message returned when a step is successfully filled."""
    file = StringIO()
    file.write(f"Filled step {step}:\n")
    node.print(1, file)
    file.write("Outline:\n")
    root.quickview(1, file)
    root._print_all_warnings(file)
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
