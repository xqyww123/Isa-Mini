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
from io import StringIO
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
    IsaTerm, ContinuingInteraction, ImmediateAnswer,
    AoA_Error, ArgumentError, IsabelleError, InternalError,
    CannotDelete_Root, NodeNotFound, ProofTreeTooDeep,
    EvaluationStatus,
    Parse_Op_List, Interaction_BadAnswer,
    AnswerIndexes, AnswerIndex, AnswerIndexesOrName, AnswerIndexesOrSpec,
    AnswerInstantiate, AnswerTargetGoal, AnswerRefutation,
    TOOL_EDIT, TOOL_DELETE, TOOL_READ, TOOL_REQUEST_LEMMAS,
    TOOL_COMPLAIN,
    TOOL_ANSWER_INDEXES, TOOL_ANSWER_INDEX, TOOL_ANSWER_INDEXES_OR_NAME,
    TOOL_ANSWER_INDEXES_OR_SPEC, TOOL_ANSWER_INSTANTIATE,
    TOOL_ANSWER_TARGET_GOAL, TOOL_ANSWER_REFUTATION,
    ANSWER_TOOLS,
    ALL_PROOF_TOOLS, Have_ToolArg, Have,
    Role_Worker,
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
_cc_delete_schema = _load_schema("cc_delete.jsonc")
_cc_read_schema = _load_schema("cc_recall.jsonc")
_cc_request_lemmas_schema = _load_schema("cc_request_lemmas.jsonc")
_cc_complain_schema = _load_schema("cc_complain.jsonc")
_cc_answer_indexes_schema = _load_schema("cc_answer_indexes.jsonc")
_cc_answer_index_schema = _load_schema("cc_answer_index.jsonc")
_cc_answer_indexes_or_name_schema = _load_schema("cc_answer_indexes_or_name.jsonc")
_cc_answer_indexes_or_spec_schema = _load_schema("cc_answer_indexes_or_spec.jsonc")
_cc_answer_instantiate_schema = _load_schema("cc_answer_instantiate.jsonc")
_cc_answer_target_goal_schema = _load_schema("cc_answer_target_goal.jsonc")
_cc_answer_refutation_schema = _load_schema("cc_answer_refutation.jsonc")



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

    Only the fork session assigned to answer an interaction may call an
    ``answer_*`` tool. The parent session never has a pending interaction
    because all interactions are delegated to forks via ``fork_interaction``.

    Fork sessions are additionally restricted to the tools declared in
    ``interaction.fork_allowed_tools`` — typically one ``answer_*`` tool
    plus ``query``.
    """
    if tool_name in ANSWER_TOOLS and (
            session.fork_pending is None or session.fork_pending.answer.done()):
        answer_tn = session.tool_name(tool_name)
        return f"No question pending. The `{answer_tn}` tool can only be used when there is a question for you to answer."
    if session.fork_pending is not None and tool_name in ALL_PROOF_TOOLS:
        allowed = session.fork_pending.interaction.fork_allowed_tools
        if tool_name not in allowed:
            allowed_list = ", ".join(f"`{session.tool_name(t)}`" for t in allowed)
            interaction = session.fork_pending.interaction
            answer_tn = session.tool_name(interaction.answer_tool_name)
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
    # IsabelleError is caught here (not in ToolExecutor.execute) so it stays a
    # recoverable (msg, True) return: a malformed/ill-typed term in a block
    # statement (HAVE/OBTAIN/Induction/Intro) escapes root.fill/amend as an
    # IsabelleError, and the agent should see it and retry — and the mutate
    # cooldown in execute must still fire on it. ConnectionError/EOFError and
    # truly-unexpected exceptions propagate to execute for unified handling.
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
        session.age += 1
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
        response, finished = await P.edit_message(root, outcome, session)
        if finished and session.is_planning:
            # Proof structure complete → hand off to the FINISHING flow. Snapshot
            # now (this edit's tree state), but log the TOOL_RESPONSE only AFTER
            # complete_proof returns, so it records what the agent actually
            # receives: the edit message when everything proves, or a Worker
            # outcome (surrender / failure / refutation) otherwise — not this
            # edit's possibly-stale "all proven" message.
            session.log_proof_tree_snapshot(f"after_{action}_step_{step}")
            # NOTE: complete_proof runs while ToolExecutor._tool_lock is held
            # (the `edit` case in execute() wraps this whole function in that
            # lock). It dispatches Worker agents and can take many minutes and
            # LLM round-trips, so the planning session's tool lock is held for
            # that entire span. Intentional and safe: the planning loop is
            # single-flight and already blocked awaiting this result, and each
            # Worker fork uses its OWN executor/lock — no contention, no deadlock.
            result = await session.complete_proof(response)
            session.log_tool_response(_tn, result[0])
            return result
        if finished:
            await session.interrupt()
        is_error = outcome.failure is not None and outcome.failure.is_error
        session.log_tool_response(_tn, response)
        session.log_proof_tree_snapshot(f"after_{action}_step_{step}")

        depth_exceeded = session._depth_limit_exceeded
        session._depth_limit_exceeded = False
        if depth_exceeded:
            session._depth_limit += 5
            session._retry_count += 1
            session.log_AoA_opr(
                f"Proof tree depth exceeded limit, "
                f"new limit: {session._depth_limit}")
            if session._retry_count >= session.max_retries:
                session.root.quit_info = (
                    "surrender",
                    f"proof tree depth exceeded limit {session._depth_limit - 5}")
                await session.interrupt()
            else:
                await session.request_restart()

        return (response, is_error)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(pretty_unicode(err) for err in e.errors)}"
        session.log_tool_response(_tn, f"ERROR: {error_msg}")
        return (error_msg, True)


async def _delete_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_DELETE)
    session.log_tool_call(_tn, args)
    # IsabelleError caught here (not in execute) so it stays a recoverable
    # (msg, True) return and still triggers the mutate cooldown; other
    # exceptions propagate to ToolExecutor.execute for unified handling.
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
        session.age += 1
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
            response, finished = await P.deleted_steps_message(deleted, session.root, session)
            if not_found:
                noun = "step" if len(not_found) == 1 else "steps"
                response += f"\nWarning: {noun} {', '.join(not_found)} not found and skipped."
            if finished and session.is_planning:
                # See _edit_tool_logic: snapshot now, but log the TOOL_RESPONSE
                # after complete_proof so it records the agent-visible result;
                # complete_proof runs under the held _tool_lock.
                session.log_proof_tree_snapshot("after_delete")
                result = await session.complete_proof(response)
                session.log_tool_response(_tn, result[0])
                return result
            if finished:
                await session.interrupt()
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


def _extract_indexes(args: dict) -> list[int]:
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
    return sorted(set(indexes)) if indexes else []

def _extract_instantiations(args: dict) -> list[tuple[str, str]]:
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
    return [(i["variable"], i["term"]) for i in instantiations] if instantiations else []


async def _answer_tool_dispatch(session: Session, tool_name: str, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(tool_name)
    session.log_tool_call(_tn, args)
    # IsabelleError caught here (not in execute) so it stays a recoverable
    # (msg, True) return; other exceptions propagate to ToolExecutor.execute
    # for unified handling.
    try:
        pending = session.fork_pending
        if pending is None or pending.answer.done():
            error_msg = f"No question pending. The `{_tn}` tool can only be used when there is a question for you to answer"
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)

        allowed = pending.interaction.fork_allowed_tools
        if tool_name not in allowed:
            answer_tools = [t for t in allowed if t in ANSWER_TOOLS]
            error_msg = f"Wrong answer tool. Use: {', '.join(f'`{session.tool_name(t)}`' for t in answer_tools)}"
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)

        match tool_name:
            case "answer_indexes":
                payload = AnswerIndexes(indexes=_extract_indexes(args))
            case "answer_index":
                raw = args.get("index")
                payload = AnswerIndex(index=raw if isinstance(raw, int) else None)
            case "answer_indexes_or_name":
                payload = AnswerIndexesOrName(
                    indexes=_extract_indexes(args),
                    name=args.get("name") or None)
            case "answer_indexes_or_spec":
                payload = AnswerIndexesOrSpec(
                    indexes=_extract_indexes(args),
                    statement=args.get("statement") or None)
            case "answer_instantiate":
                payload = AnswerInstantiate(
                    instantiations=_extract_instantiations(args))
            case "answer_target_goal":
                payload = AnswerTargetGoal(
                    index=args["index"],
                    suggestions=args["suggestions"],
                    useful_lemmas=args["useful_lemmas"])
            case "answer_refutation":
                payload = AnswerRefutation(
                    accept=bool(args["accept"]),
                    reason=args["reason"])
            case _:
                error_msg = f"Unknown answer tool: {tool_name}"
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)

        try:
            result = await pending.interaction.answer(payload)
        except Interaction_BadAnswer as e:
            error_msg = str(e)
            session.log_tool_response(_tn, f"BAD ANSWER: {error_msg}")
            return (error_msg, True)
        except ContinuingInteraction as exp:
            if exp.new_interaction is None:                       # re-prompt the SAME interaction
                assert exp.new_prompt is not None, \
                    "ContinuingInteraction needs new_prompt or new_interaction"
                session.log_tool_response(
                    _tn, f"[INTERACTION PROMPT]\n{exp.new_prompt}")
                return (exp.new_prompt, False)
            new_it = exp.new_interaction
            try:
                # Render BEFORE swap. NOTE: a replacement interaction's prompt()
                # must not mutate shared/session state — on the ImmediateAnswer
                # branch below the swap is abandoned, but any such mutation would
                # already have happened and would persist.
                text = await new_it._render_prompt()
            except ImmediateAnswer as ia:                         # replacement resolves without the LLM
                pending.answer.set_result(ia.answer)              # reuse the existing future; do NOT swap
                resolved = ia.answer.unicode if isinstance(ia.answer, IsaTerm) else str(ia.answer)
                session.log_interaction(
                    _tn, f"interaction replaced+resolved: {type(new_it).__name__}")
                session.log_tool_response(_tn, f"[INTERACTION RESOLVED] {resolved}")
                if not session.is_major:
                    await session.interrupt()
                return (resolved, False)
            session.replace_pending_interaction(new_it)           # mode-check (InternalError) + swap
            answer_tn = session.tool_name(new_it.answer_tool_name)
            text += f"\nAnswer the question above by calling the `{answer_tn}` tool."
            session.log_interaction(_tn, f"interaction replaced: {type(new_it).__name__}")
            session.log_tool_response(_tn, f"[INTERACTION REPLACED]\n{text}")
            return (text, False)

        pending.answer.set_result(result)
        # ``answer()`` may legitimately return None (e.g. all FINISHING targets
        # proved) — surface it as an empty tool response, not the string "None".
        if result is None:
            result_str = ""
        elif isinstance(result, IsaTerm):
            result_str = result.unicode
        else:
            result_str = str(result)
        session.log_interaction(_tn, f"interaction answered: {result_str}")
        session.log_tool_response(_tn, f"[INTERACTION RESOLVED] {result_str}")
        if not session.is_major:
            await session.interrupt()
        return (result_str, False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(pretty_unicode(err) for err in e.errors)}"
        session.log_tool_response(_tn, f"ERROR: {error_msg}")
        return (error_msg, True)


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


async def _complain_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_COMPLAIN)
    session.log_tool_call(_tn, args)
    reason = args.get("reason", "surrender")
    detail = args.get("detail", "")
    if reason not in ("refute", "surrender"):
        msg = f"Invalid reason: {reason!r}. Must be `refute` or `surrender`."
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)

    suggested_lemmas = args.get("suggested_lemmas")

    if isinstance(session.role, Role_Worker):
        from .language_model_driver import WorkerRefute, WorkerSurrender
        handle = session.role.worker_handle
        if handle is None:
            # A worker is always spawned via WorkerHandle, which sets
            # role.worker_handle. A missing handle is a programming error, not a
            # runtime condition to paper over.
            raise InternalError(
                "Role_Worker has no worker_handle (worker must be spawned "
                "via WorkerHandle).")

        if reason == "refute":
            # Stay alive and block until the planning agent reviews the claim.
            fut: asyncio.Future = asyncio.get_running_loop().create_future()
            handle._event_queue.put_nowait(
                WorkerRefute(detail=detail, suggested_lemmas=suggested_lemmas,
                             response_future=fut))
            accepted, review_reason = await fut
            if accepted:
                await session.interrupt()
                msg = "Refutation accepted; concluding this goal."
                session.log_tool_response(_tn, msg)
                return (msg, False)
            tail = f" {review_reason}" if review_reason else ""
            msg = (f"Refutation rejected.{tail} Keep working on the goal.")
            session.log_tool_response(_tn, msg)
            return (msg, False)

        # reason == "surrender": terminal — notify, then wind down.
        handle._event_queue.put_nowait(
            WorkerSurrender(detail=detail, suggested_lemmas=suggested_lemmas))
        await session.interrupt()
        msg = f"Complaint recorded ({reason})."
        session.log_tool_response(_tn, msg)
        return (msg, False)

    # Role_Plan: conclude / restart the planning session.
    if reason == "surrender":
        session._retry_count += 1
        if session._retry_count >= session.max_retries:
            session.root.quit_info = ("surrender", detail)
            msg = f"Proof attempt concluded ({reason})."
            session.log_tool_response(_tn, msg)
            await session.interrupt()
            return (msg, False)
        msg = "Restarting session with fresh context."
        session.log_tool_response(_tn, msg)
        await session.request_restart()
        return (msg, False)
    # reason == "refute"
    session.root.quit_info = (reason, detail)
    msg = f"Proof attempt concluded ({reason})."
    session.log_tool_response(_tn, msg)
    await session.interrupt()
    return (msg, False)


async def _request_lemmas_tool_logic(
    session: Session, args: dict, tool_lock: asyncio.Lock,
) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_REQUEST_LEMMAS)
    session.log_tool_call(_tn, args)
    lemmas = args.get("lemmas")
    if not isinstance(lemmas, list) or not lemmas:
        msg = "lemmas must be a non-empty array"
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)

    root = session.root
    results: list[str] = []

    for i, lemma in enumerate(lemmas):
        name = lemma.get("name", "")
        english = lemma.get("english", "")
        conclusion = lemma.get("conclusion", "")
        if not name or not conclusion:
            results.append(f"Lemma {i+1}: skipped (name and conclusion required)")
            continue

        statement: dict = {
            "english": english,
            "conclusion": conclusion,
        }
        if "for_any" in lemma:
            statement["for_any"] = lemma["for_any"]
        if "premises" in lemma:
            statement["premises"] = lemma["premises"]

        have_arg: Have_ToolArg = {
            "thought": f"Sub-agent lemma: {english}",
            "statement": statement,  # type: ignore[typeddict-item]
            "name": name,
        }

        try:
            gns = Parse_Op_List([{"operation": "Have", **have_arg}],
                                f"lemmas[{i}]")
        except AoA_Error as e:
            results.append(f"Lemma '{name}': parse error: {e}")
            continue

        async with tool_lock:
            session.age += 1
            if session.is_worker and isinstance(session.role.target, Have):
                outcome = await session.role.target.insert_before_me(gns)
            else:
                outcome = await root.global_env.append(gns)
            session.refresh_YAML()

        if not outcome.committed:
            results.append(f"Lemma '{name}': insertion failed")
            continue

        have_node = outcome.committed[-1]
        if not isinstance(have_node, Have):
            results.append(f"Lemma '{name}': unexpected node type after insertion")
            continue

        if have_node.status.status == EvaluationStatus.Status.FAILURE or \
           have_node.status.status == EvaluationStatus.Status.CANCELLED:
            results.append(
                f"Lemma '{name}': HAVE failed: {have_node.status}")
            async with tool_lock:
                rp = have_node._delete_me()
                await rp._refresh_me_alone(auto_intro=False)
                if rp.parent is not None:
                    await rp._refresh_all_after_me()
                session.refresh_YAML()
            continue

        session.shown_HAVE_fact_names[name] = list(have_node.for_any)

        success = await session.spawn_lemma_subagent(have_node, name)

        if not success:
            results.append(f"Lemma '{name}': sub-agent failed to prove")
            session.shown_HAVE_fact_names.pop(name, None)
            async with tool_lock:
                rp = have_node._delete_me()
                await rp._refresh_me_alone(auto_intro=False)
                if rp.parent is not None:
                    await rp._refresh_all_after_me()
                session.refresh_YAML()
        else:
            results.append(f"Lemma '{name}': proved successfully")

    file = P.MyIO(StringIO())
    file.write("request_lemmas results:\n")
    for r in results:
        file.write(f"  - {r}\n")
    file.write("\nOutline:\n")
    session.quickview_proof_scope(1, file)
    root.reset_changed()

    response = file.getvalue()
    session.log_tool_response(_tn, response)
    return (response, False)


# ============================================================================
# ToolExecutor — Direct In-Process Tool Dispatch
# ============================================================================

_RO  = ToolAnnotations(readOnlyHint=True,  destructiveHint=False, openWorldHint=False)
_MUT = ToolAnnotations(readOnlyHint=False, destructiveHint=True,  openWorldHint=False)
_ACT = ToolAnnotations(readOnlyHint=False, destructiveHint=False, openWorldHint=False)

_TOOL_SCHEMAS: dict[str, dict[str, Any]] = {
    "edit":   {"description": "Edit the proof.yaml file", "schema": _cc_edit_schema_raw, "annotations": _MUT},
    "delete": {"description": "Delete proof steps", "schema": _cc_delete_schema, "annotations": _MUT},
    "query":  {"description": "Search for Isabelle entities by semantic similarity, patterns, or exact name/term. "
                "Use exact_name to look up definitions; "
                "use exact_term to unfold fancy syntax and retrieve semantic explanations; "
                "use long_description and filters for discovery.",
               "schema": _cc_query_schema, "annotations": _RO},
    "recall": {"description": "Recall proof state from `proof.yaml`. Use only when you have lost track.", "schema": _cc_read_schema, "annotations": _RO},
    # NOTE: `request_lemmas` is intentionally NOT registered here — the tool is
    # disabled (not exposed to the LLM) pending a redesign that moves it to a
    # worker→planner channel via `complain`. The logic (`_request_lemmas_tool_logic`),
    # its dispatch case, schema file, and driver mapping are retained as dead code.
    "complain": {"description": "Report that the goal cannot be proved: 'refute' if buggy/unprovable, 'surrender' if no strategy remains. Optionally suggest lemmas that would help.",
                 "schema": _cc_complain_schema, "annotations": _ACT},
    "answer_indexes": {"description": "Answer by selecting indexes from the presented options", "schema": _cc_answer_indexes_schema, "annotations": _ACT},
    "answer_index": {"description": "Answer by selecting a single index, or null to skip", "schema": _cc_answer_index_schema, "annotations": _ACT},
    "answer_indexes_or_name": {"description": "Answer by selecting indexes or providing an exact fact name", "schema": _cc_answer_indexes_or_name_schema, "annotations": _ACT},
    "answer_indexes_or_spec": {"description": "Answer by selecting indexes or providing an Isabelle proposition", "schema": _cc_answer_indexes_or_spec_schema, "annotations": _ACT},
    "answer_instantiate": {"description": "Answer by providing schematic-variable instantiations", "schema": _cc_answer_instantiate_schema, "annotations": _ACT},
    "answer_target_goal": {"description": "Select a target goal for the worker agent and provide proof suggestions", "schema": _cc_answer_target_goal_schema, "annotations": _ACT},
    "answer_refutation": {"description": "Accept or reject a worker's claim that the goal is unprovable", "schema": _cc_answer_refutation_schema, "annotations": _ACT},
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

        is_error = False
        try:
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
                case n if n in ANSWER_TOOLS:
                    async with self._tool_lock:
                        result, is_error = await _answer_tool_dispatch(session, n, arguments)
                case "query":
                    result, is_error = await _query_tool_logic(session, arguments)
                case "recall":
                    result, is_error = await _read_tool_logic(session, arguments)
                case "request_lemmas":
                    result, is_error = await _request_lemmas_tool_logic(
                        session, arguments, self._tool_lock)
                    session.last_proof_op_time = time()
                case "complain":
                    result, is_error = await _complain_tool_logic(session, arguments)
                case _:
                    return (f"Unknown tool: {name}", True)
        except (ConnectionError, EOFError):
            raise asyncio.CancelledError("connection lost")
        except Exception as e:
            session.log_tool_response(
                session.tool_name(name),
                f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
            sys.exit(1)

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
                session.seen_abbreviations.clear()
                session.showed_suffices_notice = False
                session.showed_fill_hint = False
                session.showed_cancelled_notice = False
                session.shown_HAVE_fact_names.clear()
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
