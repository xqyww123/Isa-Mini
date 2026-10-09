"""The base `edit` schema, `tools/cc_edit.jsonc`, loaded once.

Shared by model.py, whose decorator checks a plugin's `construct_schema` against
its `$defs`, and by mcp_http_server.py, which builds each call's `edit` schema
from it (docs/USER_OPERATIONS.md, sections 4.1 and 5.3).
"""
import os

import jsoncomment

_tools_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tools")
_json = jsoncomment.JsonComment()


def load_schema(filename: str) -> dict:
    """A tool schema from `tools/`, its comments stripped."""
    with open(os.path.join(_tools_dir, filename), "r", encoding="utf-8") as f:
        return _json.load(f)


BASE_EDIT_SCHEMA: dict = load_schema("cc_edit.jsonc")
