"""
Singleton multi-session MCP HTTP server for proof tools.

Architecture:
- One HTTP server, one port, multiple proof sessions on different URL paths
- Each session (including forks) gets its own endpoint: /mcp/<session_id>
- Each endpoint has its own low-level mcp.server.Server with hand-written schemas
- Tool handlers close over their Session instance and set _session_var per-request
- Both embedded (Agent SDK) and standalone (CLI in tmux) modes connect via HTTP URL

Usage:
    server = await ProofMCPHTTPServer.get_or_create()
    url = await server.register_session("my_session_id", session)
    # Claude Code connects to url via --mcp-config
    await server.unregister_session("my_session_id")
"""

from __future__ import annotations

import asyncio
import copy
import json
import os
import sys
import socket
from time import time
from typing import Any

import jsoncomment
import uvicorn
from mcp.server.lowlevel import Server as MCPServer
from mcp.server.streamable_http_manager import StreamableHTTPSessionManager
from mcp.types import Tool, ToolAnnotations, TextContent, CallToolResult

from Isabelle_RPC_Host import pretty_unicode
from .model import (
    _session_var, Session, Node, NonLeaf_Node,
    InteractionExpanded,
    AoA_Error, ArgumentError, IsabelleError, InternalError,
    CannotDelete_Root, NodeNotFound,
    EvaluationStatus,
    Parse_Op_List, normalize_answer, Interaction_BadAnswer,
    TOOL_EDIT, TOOL_DELETE, TOOL_ANSWER, TOOL_READ, TOOL_SURRENDER, ALL_PROOF_TOOLS,
)
import yaml as _yaml
from .retrieval import (
    BATCHED_SEMANTIC_SEARCH,
    _query_tool_logic,
    _cc_query_schema,
)
from . import prompts as P


# ============================================================================
# Schema Loading
# ============================================================================

_current_dir = os.path.dirname(os.path.abspath(__file__))
_json = jsoncomment.JsonComment()

def _load_schema(filename: str) -> dict:
    with open(os.path.join(_current_dir, "tools", filename), "r", encoding="utf-8") as f:
        return _json.load(f)

_cc_edit_schema_raw = _load_schema("cc_edit.jsonc")
_cc_answer_schema = _load_schema("cc_answer.jsonc")
_cc_delete_schema = _load_schema("cc_delete.jsonc")
_cc_read_schema = _load_schema("cc_recall.jsonc")
_cc_surrender_schema = _load_schema("cc_surrender.jsonc")



def _flatten_edit_schema(schema: dict) -> dict:
    """Produce a Gemini-compatible edit schema: no $defs/$ref, no recursion.

    Proof fields become ``anyOf: [{"const": "GivenLater"}, Obvious]``.
    FactByName.discharge_premises items become ``{"type": "string"}``.
    """
    flat = copy.deepcopy(schema)
    defs: dict[str, Any] = flat.pop("$defs", {})

    for d in defs.values():
        if isinstance(d, dict):
            d.pop("additionalProperties", None)

    flat_fact_by_name: dict | None = None

    def _make_flat_fact_by_name() -> dict:
        nonlocal flat_fact_by_name
        if flat_fact_by_name is not None:
            return copy.deepcopy(flat_fact_by_name)
        fbn = copy.deepcopy(defs["FactByName"])
        fbn.pop("additionalProperties", None)
        props = fbn.get("properties", {})
        if "instantiations" in props:
            props["instantiations"]["items"] = _resolve(
                props["instantiations"]["items"])
        if "discharge_premises" in props:
            props["discharge_premises"]["items"] = {
                "anyOf": [{"type": "string"}, {"type": "null"}]
            }
        flat_fact_by_name = fbn
        return copy.deepcopy(fbn)

    def _make_flat_obvious() -> dict:
        obv = copy.deepcopy(defs["Obvious"])
        obv.pop("additionalProperties", None)
        facts_items = obv.get("properties", {}).get("facts", {}).get("items")
        if facts_items and "anyOf" in facts_items:
            facts_items["anyOf"] = [
                _resolve(alt) for alt in facts_items["anyOf"]
            ]
        return obv

    def _make_flat_proof() -> dict:
        return {"anyOf": [{"const": "GivenLater"}, _make_flat_obvious()]}

    def _resolve_operation() -> dict:
        """Inline the full Operation anyOf (all 16 operation types)."""
        op_def = defs["Operation"]
        return _resolve(copy.deepcopy(op_def), in_proof=False)

    def _resolve(node: Any, in_proof: bool = False) -> Any:
        if isinstance(node, dict):
            ref = node.get("$ref")
            if ref and isinstance(ref, str) and ref.startswith("#/$defs/"):
                name = ref[len("#/$defs/"):]
                if name == "Proof":
                    return _make_flat_proof()
                if name == "Operation":
                    if in_proof:
                        return _make_flat_proof()
                    return _resolve_operation()
                if name == "GivenLater":
                    return copy.deepcopy(defs["GivenLater"])
                if name == "FactByName":
                    return _make_flat_fact_by_name()
                if name in defs:
                    resolved = copy.deepcopy(defs[name])
                    if isinstance(resolved, dict):
                        resolved.pop("additionalProperties", None)
                    return _resolve(resolved, in_proof)
                return node
            return {k: _resolve(v, in_proof) for k, v in node.items()}
        if isinstance(node, list):
            return [_resolve(item, in_proof) for item in node]
        return node

    flat = _resolve(flat, in_proof=False)
    flat.pop("additionalProperties", None)

    po = flat.get("properties", {}).get("proof_operations")
    if po and po.get("type") == "array":
        po["type"] = ["array", "string"]

    return flat


_cc_edit_schema_flat = _flatten_edit_schema(_cc_edit_schema_raw)


def _assert_no_refs(schema: dict) -> None:
    """Import-time check: flat schema must contain no $ref or $defs."""
    def _check(node: Any, path: str = "") -> None:
        if isinstance(node, dict):
            if "$ref" in node:
                raise AssertionError(f"$ref found at {path}: {node['$ref']}")
            if "$defs" in node:
                raise AssertionError(f"$defs found at {path}")
            for k, v in node.items():
                _check(v, f"{path}.{k}")
        elif isinstance(node, list):
            for i, v in enumerate(node):
                _check(v, f"{path}[{i}]")
    _check(schema)

_assert_no_refs(_cc_edit_schema_flat)


# ============================================================================
# Permission Check (both modes)
# ============================================================================

def _check_tool_permission(session: Session, tool_name: str) -> str | None:
    """Check interaction state. Returns error message or None.

    Only the fork session assigned to answer an interaction may call the
    ``answer`` tool. The parent session never has a pending interaction
    because all interactions are delegated to forks via ``fork_interaction``.

    Fork sessions are additionally restricted to the tools declared in
    ``interaction.fork_allowed_tools`` — typically ``answer`` + ``query``.
    """
    if tool_name == "answer" and (
            session.fork_pending is None or session.fork_pending.answer.done()):
        answer_tn = session.tool_name(TOOL_ANSWER)
        return f"No question pending. The `{answer_tn}` tool can only be used when there is a question for you to answer."
    if session.fork_pending is not None and tool_name in ALL_PROOF_TOOLS:
        allowed = session.fork_pending.interaction.fork_allowed_tools
        if tool_name not in allowed:
            allowed_list = ", ".join(f"`{session.tool_name(t)}`" for t in allowed)
            answer_tn = session.tool_name(TOOL_ANSWER)
            return (f"Tool `{session.tool_name(tool_name)}` is not allowed. "
                    f"Only {allowed_list} {'is' if len(allowed) == 1 else 'are'} available. "
                    f"Use the `{answer_tn}` tool to submit your answer.")
    return None


# ============================================================================
# Tool Logic Functions (shared, no framework dependency)
# ============================================================================

async def _edit_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    ops = args.get("proof_operations")
    if isinstance(ops, str):
        try:
            ops = json.loads(ops)
        except (json.JSONDecodeError, ValueError):
            pass
    if isinstance(ops, dict):
        ops = [ops]
    if ops is not args.get("proof_operations"):
        args = {**args, "proof_operations": ops}
    _tn = session.tool_name(TOOL_EDIT)
    session.log_tool_call(_tn, args)
    try:
        step = args.get("target_step")
        if step is not None:
            step = str(step)
        action = args.get("action")
        ops_list = args.get("proof_operations")
        if not step:
            error_msg = "target_step must be a non-empty string"
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        if not isinstance(action, str):
            error_msg = "action must be a string"
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        if not isinstance(ops_list, list) or not ops_list:
            error_msg = "proof_operations must be a non-empty array of proof operations"
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        # Parse atomically: validation, splice, and Parsed_Opr construction
        # all happen in one pass — on any failure, no tree mutation has
        # occurred.
        try:
            gns = Parse_Op_List(ops_list, "proof_operations")
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)

        root = session.root
        root.session.age += 1
        match action:
            case "fill":
                outcome = await root.fill(step, gns)
            case "insert_before":
                outcome = await root.insert_before(step, gns)
            case "amend":
                outcome = await root.amend(step, gns)
            case _:
                error_msg = P.invalid_action_error(action)
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)

        session.refresh_YAML()
        response = await P.edit_message(root, outcome, session)
        is_error = outcome.failure is not None and outcome.failure.is_error
        session.log_tool_response(_tn, response)
        session.log_proof_tree_snapshot(f"after_{action}_step_{step}")
        return (response, is_error)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(pretty_unicode(err) for err in e.errors)}"
        session.log_tool_response(_tn, f"ERROR: {error_msg}")
        return (error_msg, True)
    except (ConnectionError, EOFError):
        raise asyncio.CancelledError("connection lost")
    except Exception as e:
        session.log_tool_response(
            _tn,
            f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


async def _delete_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_DELETE)
    session.log_tool_call(_tn, args)
    try:
        target_steps = args.get("target_steps")
        if isinstance(target_steps, str):
            try:
                parsed = json.loads(target_steps)
                target_steps = parsed if isinstance(parsed, list) else [target_steps]
            except (json.JSONDecodeError, ValueError):
                target_steps = [target_steps]
        if isinstance(target_steps, int):
            target_steps = [target_steps]
        if not isinstance(target_steps, list) or not target_steps:
            error_msg = "target_steps must be a non-empty array of strings"
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        session.root.session.age += 1
        steps = [str(s) for s in target_steps]
        try:
            not_found = await session.root.delete(steps)
            if len(not_found) == len(steps):
                noun = "step" if len(not_found) == 1 else "steps"
                error_msg = f"Error: {noun} {', '.join(not_found)} not found."
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
            deleted = [s for s in steps if s not in not_found]
            session.refresh_YAML()
            response = await P.deleted_steps_message(deleted, session.root, session)
            if not_found:
                noun = "step" if len(not_found) == 1 else "steps"
                response += f"\nWarning: {noun} {', '.join(not_found)} not found and skipped."
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        session.log_tool_response(_tn, response)
        session.log_proof_tree_snapshot("after_delete")
        return (response, False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(pretty_unicode(err) for err in e.errors)}"
        session.log_tool_response(_tn, f"ERROR: {error_msg}")
        return (error_msg, True)
    except (ConnectionError, EOFError):
        raise asyncio.CancelledError("connection lost")
    except Exception as e:
        session.log_tool_response(_tn, f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


async def _answer_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """Handle an ``answer`` tool call from a forked sub-agent.

    On success: completes ``session.fork_pending.answer`` with the computed
    answer and interrupts the session so ``fork_interaction`` can return.
    On ``InteractionExpanded``: returns the new prompt so the same fork
    re-submits with the expanded list.
    """
    _tn = session.tool_name(TOOL_ANSWER)
    session.log_tool_call(_tn, args)
    try:
        pending = session.fork_pending
        if pending is None or pending.answer.done():
            answer_tn = session.tool_name(TOOL_ANSWER)
            error_msg = f"No question pending. The `{answer_tn}` tool can only be used when there is a question for you to answer"
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)

        indexes = args.get("indexes")
        if isinstance(indexes, str):
            try:
                indexes = json.loads(indexes)
            except (json.JSONDecodeError, ValueError):
                indexes = None
        if isinstance(indexes, int):
            indexes = [indexes]
        if indexes is not None and not isinstance(indexes, list):
            indexes = None

        instantiations = args.get("instantiations")
        if isinstance(instantiations, str):
            try:
                instantiations = json.loads(instantiations)
            except (json.JSONDecodeError, ValueError):
                instantiations = None
        if isinstance(instantiations, dict):
            instantiations = [instantiations]
        if instantiations is not None and not isinstance(instantiations, list):
            instantiations = None

        normalized = normalize_answer(
            indexes,
            args.get("name"),
            args.get("statement"),
            instantiations)

        try:
            result = await pending.interaction.answer(normalized)
        except Interaction_BadAnswer as e:
            error_msg = str(e)
            session.log_tool_response(_tn, f"BAD ANSWER: {error_msg}")
            return (error_msg, True)
        except InteractionExpanded as exp:
            session.log_tool_response(
                _tn, f"[INTERACTION PROMPT]\n{exp.new_prompt}")
            return (exp.new_prompt, False)

        pending.answer.set_result(result)
        session.log_interaction(_tn, f"interaction answered: {result}")
        session.log_tool_response(_tn, f"[INTERACTION RESOLVED] {result}")
        if not session.is_major:
            await session.interrupt()
        return (str(result), False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(pretty_unicode(err) for err in e.errors)}"
        session.log_tool_response(_tn, f"ERROR: {error_msg}")
        return (error_msg, True)
    except (ConnectionError, EOFError):
        raise asyncio.CancelledError("connection lost")
    except Exception as e:
        session.log_tool_response(_tn, f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


def _node_end_line(node: Node, total_lines: int) -> int:
    """End line of a node's printed representation (1-indexed, inclusive)."""
    parent = node.parent
    if parent is None:
        return total_lines
    assert isinstance(parent, NonLeaf_Node)
    idx = next(i for i, c in enumerate(parent.sub_nodes) if c is node)
    if idx + 1 < len(parent.sub_nodes):
        nxt = parent.sub_nodes[idx + 1]
        if nxt.line > 0:
            return nxt.line - 1
    return _node_end_line(parent, total_lines)


async def _read_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """Read proof.yaml around a step_id or line number."""
    _tn = session.tool_name(TOOL_READ)
    session.log_tool_call(_tn, args)
    session.refresh_YAML()

    step_id = args.get("step_id")
    if step_id is not None:
        step_id = str(step_id).strip() or None
    line_num = args.get("line")
    if line_num is not None:
        line_num = int(line_num)
    explicit_range = args.get("range")
    range_lines = int(explicit_range or 50)

    if step_id is None and line_num is None:
        yaml_path: str | None = getattr(session, "YAML_path", None)
        if yaml_path is None:
            raise InternalError("proof.yaml path not configured")
        try:
            with open(yaml_path, encoding="utf-8") as f:
                all_lines = f.readlines()
        except FileNotFoundError:
            raise InternalError(f"proof.yaml not found at {yaml_path}")
        if len(all_lines) > 100:
            error_msg = (
                f"The proof contains {len(all_lines)} lines. "
                "Provide `step_id` or `line number` to read a specific section.")
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        end_line = len(all_lines)
        result = f"[Line 1-{end_line}]\n" + "".join(all_lines)
        session.log_tool_response(_tn, result)
        return (result, False)

    node = None
    if step_id is not None:
        try:
            node = session.root.locate_node(step_id)
            if node.line == 0:
                error_msg = (
                    f"Step '{step_id}' has no line information (proof not yet printed). "
                    "Read by line number instead.")
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
            line_num = node.line
        except NodeNotFound:
            yaml_path_fb: str | None = getattr(session, "YAML_path", None)
            if yaml_path_fb is not None:
                try:
                    with open(yaml_path_fb, encoding="utf-8") as f:
                        fb_lines = f.readlines()
                    if len(fb_lines) <= 40:
                        result = (f"WARNING: Step '{step_id}' doesn't exist.\n"
                                  f"[Line 1-{len(fb_lines)}]\n"
                                  + "".join(fb_lines))
                        session.log_tool_response(_tn, result)
                        return (result, False)
                except FileNotFoundError:
                    pass
            error_msg = f"Step '{step_id}' doesn't exist. Read the proof by line number instead."
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)

    assert line_num is not None
    yaml_path: str | None = getattr(session, "YAML_path", None)
    if yaml_path is None:
        raise InternalError("proof.yaml path not configured")

    try:
        with open(yaml_path, encoding="utf-8") as f:
            all_lines = f.readlines()
    except FileNotFoundError:
        raise InternalError(f"proof.yaml not found at {yaml_path}")

    total_lines = len(all_lines)
    if node is not None:
        if explicit_range is None:
            node_end = _node_end_line(node, total_lines)
            start = max(1, line_num - 5)
            end = min(node_end + 5, total_lines)
        else:
            start = max(1, line_num - 5)
            end = start + range_lines
    else:
        start = line_num
        end = start + range_lines

    selected = all_lines[start - 1 : end]
    end_line = start + len(selected) - 1
    if node is not None:
        result = f"[Step {node.id} is at Line {line_num}, showing Line {start}-{end_line}]\n" + "".join(selected)
    else:
        result = f"[Line {start}-{end_line}]\n" + "".join(selected)
    session.log_tool_response(_tn, result)
    return (result, False)


async def _refute_or_surrender_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_SURRENDER)
    session.log_tool_call(_tn, args)
    reason = args.get("reason", "surrender")
    detail = args.get("detail", "")
    if reason not in ("refute", "surrender"):
        msg = f"Invalid reason: {reason!r}. Must be `refute` or `surrender`."
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)
    if reason == "surrender" and not session.refute_or_surrender_warned:
        session.refute_or_surrender_warned = True
        msg = ("You are a strong prover and you've been doing well. "
               "Don't give up yet — take a step back, rethink your approach, "
               "and try again. You may be closer than you think.")
        session.log_tool_response(_tn, msg)
        return (msg, False)
    session.root.quit_info = (reason, detail)
    msg = f"Proof attempt concluded ({reason})."
    session.log_tool_response(_tn, msg)
    await session.interrupt()
    return (msg, False)


# ============================================================================
# ToolExecutor — Direct In-Process Tool Dispatch
# ============================================================================

_RO  = ToolAnnotations(readOnlyHint=True,  destructiveHint=False, openWorldHint=False)
_MUT = ToolAnnotations(readOnlyHint=False, destructiveHint=True,  openWorldHint=False)
_ACT = ToolAnnotations(readOnlyHint=False, destructiveHint=False, openWorldHint=False)

_TOOL_SCHEMAS: dict[str, dict[str, Any]] = {
    "edit":   {"description": "Edit the proof.yaml file", "schema": _cc_edit_schema_raw, "annotations": _MUT},
    "delete": {"description": "Delete proof steps", "schema": _cc_delete_schema, "annotations": _MUT},
    "answer": {"description": "Answer a pending question", "schema": _cc_answer_schema, "annotations": _ACT},
    "query":  {"description": "Search for Isabelle entities by semantic similarity, patterns, or exact name/term. "
                "Use exact_name to look up definitions; "
                "use exact_term to unfold fancy syntax and retrieve semantic explanations; "
                "use long_description and filters for discovery.",
               "schema": _cc_query_schema, "annotations": _RO},
    "recall": {"description": "Recall proof state from `proof.yaml`. Use only when you have lost track.", "schema": _cc_read_schema, "annotations": _RO},
    "refute_or_surrender": {"description": "Conclude the proof attempt. Use with reason 'refute' if the goal appears buggy or unprovable from the given premises, or 'surrender' if no viable strategy remains.",
                            "schema": _cc_surrender_schema, "annotations": _ACT},
}


class ToolExecutor:
    """Direct in-process tool dispatch. Used by both MCP server and APIDriver."""

    _SEARCH_HINT = (
        "\n\n---\n"
        "Hint: You've spent a while searching. What you need might not be "
        "in the library. Consider shifting focus to writing the proof."
    )
    _SEARCH_HINT_THRESHOLD = 180  # seconds
    _BATCH_CANCEL_MSG = "Cancelled: a prior edit/delete in this batch failed. Review the error before continuing."

    def __init__(self, session: Session):
        self._session = session
        self._tool_lock = asyncio.Lock()
        self._last_mutate_fail_time: float = 0.0

    async def execute(self, name: str, arguments: dict) -> tuple[str, bool]:
        """Execute a tool call. Returns (result_text, is_error).

        Handles permission checks, serialization locks, cooldown logic,
        and the search hint — same semantics as the MCP call_tool handler.
        """
        session = self._session
        _session_var.set(session)

        perm_error = _check_tool_permission(session, name)
        if perm_error:
            return (perm_error, True)

        if name != "refute_or_surrender":
            session.refute_or_surrender_warned = False

        is_error = False
        match name:
            case "edit":
                async with self._tool_lock:
                    ops = arguments.get("proof_operations") if isinstance(arguments, dict) else None
                    is_batch = isinstance(ops, list) and len(ops) > 1
                    if not is_batch and time() - self._last_mutate_fail_time < 0.7:
                        result, is_error = self._BATCH_CANCEL_MSG, True
                    else:
                        result, is_error = await _edit_tool_logic(session, arguments)
                        if is_error and not is_batch:
                            self._last_mutate_fail_time = time()
                session.last_proof_op_time = time()
            case "delete":
                async with self._tool_lock:
                    if time() - self._last_mutate_fail_time < 0.7:
                        result, is_error = self._BATCH_CANCEL_MSG, True
                    else:
                        result, is_error = await _delete_tool_logic(session, arguments)
                        if is_error:
                            self._last_mutate_fail_time = time()
                session.last_proof_op_time = time()
            case "answer":
                async with self._tool_lock:
                    result, is_error = await _answer_tool_logic(session, arguments)
            case "query":
                result, is_error = await _query_tool_logic(session, arguments)
            case "recall":
                result, is_error = await _read_tool_logic(session, arguments)
            case "refute_or_surrender":
                result, is_error = await _refute_or_surrender_tool_logic(session, arguments)
            case _:
                return (f"Unknown tool: {name}", True)

        if name == "query" and not is_error:
            if time() - session.last_proof_op_time >= self._SEARCH_HINT_THRESHOLD:
                result += self._SEARCH_HINT

        return (result, is_error)

    @staticmethod
    def tool_schemas() -> dict[str, dict[str, Any]]:
        """Return {name: {"description": ..., "schema": ...}} for all built-in tools."""
        return _TOOL_SCHEMAS


# ============================================================================
# Per-Session MCP Server Creation
# ============================================================================

def _create_mcp_server(session: Session, extra_sdk_tools: list | None = None) -> MCPServer:
    """Create a low-level MCP Server with tools bound to ``session`` via closure.

    ``extra_sdk_tools`` can carry ``SdkMcpTool`` instances (e.g. from
    Isabelle_Semantic_Embedding) whose schemas and handlers are extracted
    and registered alongside the built-in proof tools.
    """
    server = MCPServer(f"proof-{id(session)}")
    executor = ToolExecutor(session)

    # Build tool list: built-in + extras
    tools: list[Tool] = [
        Tool(name=name, description=t["description"],
             inputSchema=t["schema"], annotations=t["annotations"])
        for name, t in _TOOL_SCHEMAS.items()
    ]

    # Extract schema/handler from SdkMcpTool extras
    extra_handlers: dict[str, Any] = {}
    if extra_sdk_tools:
        for sdk_tool in extra_sdk_tools:
            schema = sdk_tool.input_schema if isinstance(sdk_tool.input_schema, dict) else {}
            tools.append(Tool(
                name=sdk_tool.name,
                description=sdk_tool.description,
                inputSchema=schema,
            ))
            extra_handlers[sdk_tool.name] = sdk_tool.handler

    @server.list_tools()
    async def list_tools() -> list[Tool]:
        return tools

    @server.call_tool()
    async def call_tool(name: str, arguments: dict) -> CallToolResult:
        _session_var.set(session)

        # Permission check
        perm_error = _check_tool_permission(session, name)
        if perm_error:
            return CallToolResult(
                content=[TextContent(type="text", text=perm_error)], isError=True)

        # Built-in tools: delegate to executor
        if name in _TOOL_SCHEMAS:
            result, is_error = await executor.execute(name, arguments)
            return CallToolResult(
                content=[TextContent(type="text", text=result)], isError=is_error)

        # Extra SDK tools
        handler = extra_handlers.get(name)
        if handler is not None:
            ret = await handler(arguments)
            content = ret.get("content", [])
            return CallToolResult(
                content=[TextContent(type="text", text=c.get("text", "")) for c in content])
        return CallToolResult(
            content=[TextContent(type="text", text=f"Unknown tool: {name}")], isError=True)

    return server


# ============================================================================
# Streamable HTTP App from Low-Level Server
# ============================================================================

class _ManagedMCPApp:
    """ASGI app wrapping a low-level MCP Server with StreamableHTTPSessionManager.

    The manager's ``run()`` context uses anyio task groups internally, so its
    lifecycle must stay within a single asyncio task.  We spawn a dedicated
    background task that keeps the manager alive.
    """

    def __init__(self, mcp_server: MCPServer):
        self._manager = StreamableHTTPSessionManager(app=mcp_server, stateless=False)
        self._task: asyncio.Task | None = None
        self._ready = asyncio.Event()
        self._stop_event = asyncio.Event()

    async def start(self):
        self._start_error: BaseException | None = None

        async def _run():
            try:
                async with self._manager.run():
                    self._ready.set()
                    await self._stop_event.wait()
            except BaseException as e:
                self._start_error = e
                self._ready.set()  # unblock start() so it can raise
                raise

        self._task = asyncio.create_task(_run())
        await self._ready.wait()
        if self._start_error is not None:
            raise self._start_error

    async def stop(self):
        if self._task is not None:
            self._stop_event.set()
            try:
                await self._task
            except Exception:
                pass
            self._task = None

    async def __call__(self, scope, receive, send):
        """ASGI interface — delegates to StreamableHTTPSessionManager.handle_request."""
        if scope["type"] in ("http", "websocket"):
            await self._manager.handle_request(scope, receive, send)


# ============================================================================
# ASGI Session Router
# ============================================================================

class _SessionRouter:
    """ASGI middleware that dispatches /mcp/<session_id>/... to per-session apps."""

    def __init__(self):
        self.apps: dict[str, _ManagedMCPApp] = {}
        self.sessions: dict[str, Session] = {}

    async def __call__(self, scope, receive, send):
        if scope["type"] not in ("http", "websocket"):
            return

        path: str = scope["path"]

        # Handle /reset_cache/<session_id> — clears view caches on context compaction
        if scope["type"] == "http" and path.startswith("/reset_cache/"):
            session_id = path[len("/reset_cache/"):]
            session = self.sessions.get(session_id)
            if session is not None:
                session.seen_commands.clear()
                session.seen_entities.clear()
                session.seen_opaque_note = False
                session.root.session.showed_suffices_notice = False
                session.root.session.showed_cancelled_notice = False
            await send({
                "type": "http.response.start",
                "status": 200,
                "headers": [(b"content-type", b"text/plain")],
            })
            await send({
                "type": "http.response.body",
                "body": b"OK",
            })
            return

        for session_id, app in list(self.apps.items()):
            prefix = f"/mcp/{session_id}"
            if path == prefix or path.startswith(prefix + "/"):
                inner_scope = dict(scope)
                inner_scope["path"] = path[len(prefix):] or "/"
                inner_scope["root_path"] = scope.get("root_path", "") + prefix
                await app(inner_scope, receive, send)
                return

        # 404
        if scope["type"] == "http":
            await send({
                "type": "http.response.start",
                "status": 404,
                "headers": [(b"content-type", b"text/plain")],
            })
            await send({
                "type": "http.response.body",
                "body": b"Session not found",
            })


# ============================================================================
# Singleton Multi-Session HTTP Server
# ============================================================================

class ProofMCPHTTPServer:
    """Singleton HTTP server hosting multiple proof sessions on different endpoints."""

    _instance: 'ProofMCPHTTPServer | None' = None
    _lock: asyncio.Lock = asyncio.Lock()

    def __init__(self, port: int = 0):
        self._port = port or self._find_free_port()
        self._router = _SessionRouter()
        self._server: uvicorn.Server | None = None
        self._serve_task: asyncio.Task | None = None
        self._next_id = 0

    def allocate_session_id(self) -> str:
        """Return a short, unique session ID (for HTTP routing, not Claude --session-id)."""
        self._next_id += 1
        return str(self._next_id)

    @classmethod
    async def get_or_create(cls, port: int = 0) -> 'ProofMCPHTTPServer':
        async with cls._lock:
            if cls._instance is None:
                cls._instance = cls(port)
            await cls._instance._ensure_serving()
        return cls._instance

    @staticmethod
    def _find_free_port() -> int:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(('127.0.0.1', 0))
            return s.getsockname()[1]

    @property
    def port(self) -> int:
        return self._port

    async def register_session(self, session_id: str, session: Session,
                               extra_sdk_tools: list | None = None) -> str:
        """Register a proof session. Returns its MCP endpoint URL."""
        mcp_server = _create_mcp_server(session, extra_sdk_tools=extra_sdk_tools)
        app = _ManagedMCPApp(mcp_server)
        await app.start()
        self._router.apps[session_id] = app
        self._router.sessions[session_id] = session
        return f"http://127.0.0.1:{self._port}/mcp/{session_id}"

    async def unregister_session(self, session_id: str):
        app = self._router.apps.pop(session_id, None)
        self._router.sessions.pop(session_id, None)
        if app is not None:
            await app.stop()

    def mcp_config_json(self, session_id: str) -> dict:
        """Return JSON config suitable for Claude CLI --mcp-config."""
        return {
            "mcpServers": {
                "proof": {
                    "type": "http",
                    "url": f"http://127.0.0.1:{self._port}/mcp/{session_id}",
                }
            }
        }

    async def _ensure_serving(self):
        """Start the HTTP server if not already running."""
        if self._serve_task is not None:
            if self._serve_task.done():
                # Previous attempt failed — reset and retry
                self._serve_task = None
                self._server = None
            else:
                return
        config = uvicorn.Config(
            self._router,
            host="127.0.0.1",
            port=self._port,
            log_level="warning",
        )
        self._server = uvicorn.Server(config)
        self._serve_task = asyncio.create_task(self._server.serve())
        # Give uvicorn a moment to bind
        await asyncio.sleep(0.5)
        # Check if server failed to start
        if self._serve_task.done():
            exc = self._serve_task.exception()
            self._serve_task = None
            self._server = None
            if exc is not None:
                raise exc

    async def shutdown(self):
        """Shut down the HTTP server."""
        if self._server is not None:
            self._server.should_exit = True
        if self._serve_task is not None:
            await self._serve_task
        self._serve_task = None
        self._server = None
        ProofMCPHTTPServer._instance = None
