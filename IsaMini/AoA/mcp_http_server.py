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

from io import StringIO

import jsoncomment
import uvicorn
from mcp.server.lowlevel import Server as MCPServer
from mcp.server.streamable_http_manager import StreamableHTTPSessionManager
from mcp.types import Tool, ToolAnnotations, TextContent, CallToolResult

from Isabelle_RPC_Host import pretty_unicode
from .model import (
    _session_var, Session, Node, NonLeaf_Node, StdBlock,
    Resolved_Node, Resolved_Slot,
    IsaTerm, ContinuingInteraction, ImmediateAnswer,
    AoA_Error, ArgumentError, IsabelleError, InternalError,
    CannotDelete_Root, NodeNotFound, ProofTreeTooDeep,
    EvaluationStatus, WorkerHandle, EditVerdict, _is_strict_ancestor,
    SUBAGENT_NESTING_DEPTH,
    Parse_Op_List, Interaction_BadAnswer,
    AnswerIndexes, AnswerIndex, AnswerIndexesOrName, AnswerIndexesOrSpec,
    AnswerInstantiate, AnswerRefutation,
    TOOL_EDIT, TOOL_DELETE, TOOL_READ, TOOL_REQUEST_LEMMAS,
    TOOL_REPORT, TOOL_SUBAGENT, TOOL_CLOSE_SUBAGENT,
    TOOL_ANSWER_INDEXES, TOOL_ANSWER_INDEX, TOOL_ANSWER_INDEXES_OR_NAME,
    TOOL_ANSWER_INDEXES_OR_SPEC, TOOL_ANSWER_INSTANTIATE,
    TOOL_ANSWER_REFUTATION,
    ANSWER_TOOLS,
    ALL_PROOF_TOOLS,
    Role_Worker,
    Surrender, Refute,
    print_indent,
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
_cc_report_schema = _load_schema("cc_report.jsonc")
_cc_answer_indexes_schema = _load_schema("cc_answer_indexes.jsonc")
_cc_answer_index_schema = _load_schema("cc_answer_index.jsonc")
_cc_answer_indexes_or_name_schema = _load_schema("cc_answer_indexes_or_name.jsonc")
_cc_answer_indexes_or_spec_schema = _load_schema("cc_answer_indexes_or_spec.jsonc")
_cc_answer_instantiate_schema = _load_schema("cc_answer_instantiate.jsonc")
_cc_answer_refutation_schema = _load_schema("cc_answer_refutation.jsonc")
_cc_subagent_schema = _load_schema("cc_subagent.jsonc")
_cc_close_subagent_schema = _load_schema("cc_close_subagent.jsonc")



def _flatten_edit_schema(schema: dict) -> dict:
    """Produce a Gemini-compatible edit schema: no $defs/$ref, no recursion.

    Proof fields become ``anyOf: [{"const": "GivenLater"}, Obvious]``.
    FactByName.discharge items become ``{"type": "string"}``.
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
        if "discharge" in props:
            props["discharge"]["items"] = {
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
        # A worker addresses steps relative to its own scope; map to the absolute
        # tree id for engine calls, but keep `step` (as supplied) for messages.
        abs_step = session._resolve_display_id(step)
        # Edit-lock + worker confinement, unified in `_edit_verdict` (all agents):
        #  - OUT_OF_SCOPE: a worker edit outside its own subtree.
        #  - LOCKED: the target is comparable to a live sub-agent's node. `amend`
        #    only locks on a strict-ancestor sub-agent (it tears down its own
        #    target's worker via `_amend_child`); `fill`/`insert_before` lock on
        #    the whole comparable region. Main is never OUT_OF_SCOPE.
        verdict, blocker = session._edit_verdict(abs_step, action)
        if verdict is EditVerdict.OUT_OF_SCOPE:
            error_msg = ("This step is outside the goal you were asked to prove — you may "
                         "only edit within your own sub-proof. If you need a fact established "
                         "elsewhere, use `request_lemmas`.")
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        if verdict is EditVerdict.LOCKED:
            assert blocker is not None  # LOCKED always carries the blocking handle
            wstep = session._display_id(blocker.target.id)
            _resume_hint = (
                f"You cannot edit it before you close the sub-agent, but you are "
                f"recommended to resume the sub-agent with your suggestions and let it "
                f"carry out the work. You can resume it by calling `subagent` on step {wstep}.")
            if session.is_worker:
                error_msg = (
                    f"A sub-agent is working on step {wstep}, which overlaps the step you "
                    f"are editing. {_resume_hint}")
            elif action == "amend":
                error_msg = (
                    f"Cannot amend step {step} because it belongs to the scope of "
                    f"the sub-agent on step {wstep}. {_resume_hint}")
            else:
                error_msg = (
                    f"Cannot edit step {step} because a sub-agent is working on step {wstep}, "
                    f"which overlaps step {step}. {_resume_hint}")
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
                outcome = await root.fill(abs_step, gns)
            case "insert_before":
                outcome = await root.insert_before(abs_step, gns)
            case "amend":
                outcome = await root.amend(abs_step, gns)
            case _:
                error_msg = P.invalid_action_error(action)
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)

        session.refresh_YAML()
        response, finished = await P.edit_message(root, outcome, session)
        if finished:
            await session.interrupt()
        is_error = outcome.failure is not None and outcome.failure.is_error
        session.log_tool_response(_tn, response)
        session.log_proof_tree_snapshot(f"after_{action}_step_{abs_step}")

        depth_exceeded = session._depth_limit_exceeded
        session._depth_limit_exceeded = False
        if depth_exceeded:
            session._depth_limit += 5
            session._retry_count += 1
            session.log_AoA_opr(
                f"Proof tree depth exceeded limit, "
                f"new limit: {session._depth_limit}")
            if session._retry_count >= session.max_retries:
                session.quit_info = Surrender(
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
        # A worker addresses steps relative to its scope; map to absolute ids.
        abs_steps = [session._resolve_display_id(s) for s in steps]
        # Worker confinement: a worker may only delete inside its own subtree.
        # (No lock — delete is always allowed and tears down what it removes.)
        for sid in abs_steps:
            verdict, _ = session._edit_verdict(sid, "delete")
            if verdict is EditVerdict.OUT_OF_SCOPE:
                error_msg = ("This step is outside the goal you were asked to prove — you may "
                             "only edit within your own sub-proof. If you need a fact established "
                             "elsewhere, use `request_lemmas`.")
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
        try:
            not_found = await session.root.delete(abs_steps)
            if len(not_found) == len(abs_steps):
                noun = "step" if len(not_found) == 1 else "steps"
                shown = ', '.join(session._display_id(s) for s in not_found)
                error_msg = f"Error: {noun} {shown} not found."
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
            deleted = [s for s in abs_steps if s not in not_found]
            session.refresh_YAML()
            response, finished = await P.deleted_steps_message(deleted, session.root, session)
            if not_found:
                noun = "step" if len(not_found) == 1 else "steps"
                shown = ', '.join(session._display_id(s) for s in not_found)
                response += f"\nWarning: {noun} {shown} not found and skipped."
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
    # Defensively drop malformed items (non-dicts / missing keys) and coerce
    # values to str, mirroring _extract_indexes / _delete_tool_logic — so a
    # malformed answer arg can't crash the handler or send a non-string where
    # ML expects a string (the same failure class as the query bug).
    return [(str(i["variable"]), str(i["term"])) for i in instantiations
            if isinstance(i, dict) and "variable" in i and "term" in i] if instantiations else []


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
        # ``answer()`` may legitimately return None — surface it as an empty
        # tool response, not the string "None".
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


def _line_is_fresh(node: Node, scope_root: Node, is_worker: bool) -> bool:
    """Whether ``node.line`` matches the just-written ``proof.yaml``.

    A full (planner/interaction) render refreshes every node's ``.line``, so any
    located node is reliable. A worker's scoped render
    (``Session.print_proof_scope``) refreshes only ``scope_root``'s *descendants*
    — ``scope_root`` itself, its ancestors and siblings keep a stale ``.line``
    from an earlier full render, into a different layout. So for a worker only a
    strict descendant of ``scope_root`` carries a trustworthy ``.line``; reading
    any other node by step id would slice the scoped file at a wrong offset."""
    if not is_worker:
        return True
    n = node.parent
    while n is not None:
        if n is scope_root:
            return True
        n = n.parent
    return False


def _node_end_line(node: Node, total_lines: int, scope_root: Node) -> int:
    """End line of a node's printed representation (1-indexed, inclusive).

    ``scope_root`` is the node whose subtree was actually rendered to
    ``proof.yaml`` with fresh line numbers: the whole ``root`` for a
    planner/interaction view, but the worker's ``target`` for a scoped worker
    view (``Session.print_proof_scope`` only re-renders ``target.sub_nodes``).
    The recursion stops at ``scope_root``: a node outside the rendered subtree
    (the target's own header, its ancestors, its siblings) keeps a stale
    ``.line`` from an earlier render, so its value must never be used as a
    boundary. Without this guard the *last* child of a worker's target escapes
    the rendered region and reads a sibling's stale line, yielding an end
    before the node's own start (an empty `Line N-(N-1)` read)."""
    if node is scope_root:
        return total_lines
    parent = node.parent
    if parent is None:
        return total_lines
    assert isinstance(parent, NonLeaf_Node)
    idx = next(i for i, c in enumerate(parent.sub_nodes) if c is node)
    if idx + 1 < len(parent.sub_nodes):
        nxt = parent.sub_nodes[idx + 1]
        if nxt.line > 0:
            return nxt.line - 1
    return _node_end_line(parent, total_lines, scope_root)


async def _read_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """Read proof.yaml around one or more step_ids, or a line number.

    ``step_id`` accepts either a single id or a list of ids; each id is
    rendered as its own segment. A node's bounds come from the proof-tree
    structure (``_node_end_line``), so a segment prints strictly the node's
    own lines — no preceding context, and ``range`` is clamped to the node so
    it never spills into the next node."""
    _tn = session.tool_name(TOOL_READ)
    session.log_tool_call(_tn, args)
    session.refresh_YAML()

    # Normalize ``step_id`` to a list (the schema requires an array; a bare
    # scalar is tolerated defensively). Requesting exactly one id keeps the
    # legacy single-id error semantics (abort + small-file fallback).
    raw_step = args.get("step_id")
    if raw_step is None:
        step_ids: list[str] | None = None
    elif isinstance(raw_step, list):
        step_ids = [s for s in (str(x).strip() for x in raw_step) if s] or None
    else:
        s = str(raw_step).strip()
        step_ids = [s] if s else None
    single_step = step_ids is not None and len(step_ids) == 1

    line_num = args.get("line")
    if line_num is not None:
        line_num = int(line_num)
    explicit_range = args.get("range")
    range_lines = int(explicit_range or 50)

    yaml_path: str | None = getattr(session, "YAML_path", None)
    if yaml_path is None:
        raise InternalError("proof.yaml path not configured")

    # Whole-file dump when neither a step nor a line is requested.
    if step_ids is None and line_num is None:
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

    try:
        with open(yaml_path, encoding="utf-8") as f:
            all_lines = f.readlines()
    except FileNotFoundError:
        raise InternalError(f"proof.yaml not found at {yaml_path}")
    total_lines = len(all_lines)

    # Line-number path (no step ids): read forward from the given line.
    if step_ids is None:
        assert line_num is not None
        start = line_num
        end = start + range_lines
        selected = all_lines[start - 1 : end]
        end_line = start + len(selected) - 1
        result = f"[Line {start}-{end_line}]\n" + "".join(selected)
        session.log_tool_response(_tn, result)
        return (result, False)

    # Step-id path (one or many): one segment per id, strictly node-bounded.
    # ``scope_root`` is the subtree actually rendered to proof.yaml with fresh
    # line numbers (see ``Session.proof_scope_root``); bounds must not be
    # derived from nodes outside it (stale `.line`).
    scope_root: Node = session.proof_scope_root
    def _render_node_segment(node: Node) -> str:
        node_start = node.line
        node_end = _node_end_line(node, total_lines, scope_root)
        if explicit_range is None:
            end = node_end
        else:
            end = min(node_start + range_lines - 1, node_end)
        end = min(end, total_lines)
        selected = all_lines[node_start - 1 : end]
        end_line = node_start + len(selected) - 1
        return (f"[Step {session._display_id(node.id)} is at Line {node_start}, showing Line "
                f"{node_start}-{end_line}]\n" + "".join(selected))

    segments: list[str] = []
    for sid in step_ids:
        # `sid` is worker-relative (as supplied) — keep it for messages, resolve
        # to the absolute tree id for the lookup.
        try:
            node = session.root.locate_node(session._resolve_display_id(sid))
        except NodeNotFound:
            if single_step:
                if total_lines <= 40:
                    result = (f"WARNING: Step '{sid}' doesn't exist.\n"
                              f"[Line 1-{total_lines}]\n" + "".join(all_lines))
                    session.log_tool_response(_tn, result)
                    return (result, False)
                error_msg = (f"Step '{sid}' doesn't exist. "
                             "Read the proof by line number instead.")
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
            segments.append(f"WARNING: Step '{sid}' doesn't exist.")
            continue
        if node.line == 0:
            error_msg = (
                f"Step '{sid}' has no line information (proof not yet printed). "
                "Read by line number instead.")
            if single_step:
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
            segments.append(f"WARNING: {error_msg}")
            continue
        if not _line_is_fresh(node, scope_root, session.is_worker):
            error_msg = (
                f"Step '{sid}' is outside your current proof scope, "
                "so its location is unavailable.")
            if single_step:
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
            segments.append(f"WARNING: {error_msg}")
            continue
        segments.append(_render_node_segment(node))

    result = "\n".join(segments)
    session.log_tool_response(_tn, result)
    return (result, False)


async def _report_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_REPORT)
    session.log_tool_call(_tn, args)
    kind = args.get("type", "surrender")
    # Worker-authored: expand its scope-relative step ids to absolute so the
    # detail still reads correctly once surfaced to the (differently-scoped)
    # dispatcher; the dispatcher re-relativizes for its own view.
    detail = session._absolutize_text(args.get("detail", ""))
    if kind not in ("refute", "surrender", "difficulty"):
        msg = (f"Invalid type: {kind!r}. Must be `refute`, `surrender`, or "
               f"`difficulty`.")
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)

    if isinstance(session.role, Role_Worker):
        from .model import WorkerRefute, WorkerSurrender, WorkerDifficulty
        handle = session.role.worker_handle
        if handle is None:
            # A worker is always spawned via WorkerHandle, which sets
            # role.worker_handle. A missing handle is a programming error, not a
            # runtime condition to paper over.
            raise InternalError(
                "Role_Worker has no worker_handle (worker must be spawned "
                "via WorkerHandle).")

        if kind == "difficulty":
            # NON-terminal PARK (like request_lemmas): suspend the worker, hand
            # control back to the dispatcher, and resume once it answers.
            if not detail:
                msg = "The `detail` argument is required when reporting a difficulty."
                session.log_tool_response(_tn, f"ERROR: {msg}")
                return (msg, True)
            fut: asyncio.Future = asyncio.get_running_loop().create_future()
            handle._event_queue.put_nowait(
                WorkerDifficulty(detail=detail, response_future=fut))
            feedback = await fut
            # The dispatcher may have added helper lemmas to the global env (into
            # the facts in scope before this worker's target) while we were
            # parked. Re-prefetch premises + refresh proof.yaml so the worker's
            # view picks them up — identical to the request_lemmas resume path.
            await session._prefetch_worker_premises()
            session.refresh_YAML()
            session.log_tool_response(_tn, feedback)
            return (feedback, False)

        if kind == "refute":
            # Stay alive and block until the planning agent reviews the claim.
            fut: asyncio.Future = asyncio.get_running_loop().create_future()
            handle._event_queue.put_nowait(
                WorkerRefute(detail=detail, response_future=fut))
            accepted, review_reason = await fut
            if accepted:
                # Set a terminal quit_info so the worker's agent loop actually
                # winds down: the ClaudeCode loop breaks on quit_info, not on an
                # interrupt alone, so without this it would retry until its budget
                # exhausts while the planner blocks on wait_finish.
                session.quit_info = Refute(review_reason or detail)
                await session.interrupt()
                msg = "Refutation accepted; concluding this goal."
                session.log_tool_response(_tn, msg)
                return (msg, False)
            tail = f" {review_reason}" if review_reason else ""
            msg = (f"Refutation rejected.{tail} Keep working on the goal.")
            session.log_tool_response(_tn, msg)
            return (msg, False)

        # kind == "surrender": terminal — notify, then wind down.
        handle._event_queue.put_nowait(WorkerSurrender(detail=detail))
        # Terminal quit_info so the worker's loop breaks cleanly (see refute above).
        session.quit_info = Surrender(detail)
        await session.interrupt()
        msg = f"Complaint recorded ({kind})."
        session.log_tool_response(_tn, msg)
        return (msg, False)

    # Role_Major: conclude / restart the planning session.
    if kind == "difficulty":
        # No enclosing agent to park under here — respond with encouragement and
        # let the agent carry on (role-neutral: never reveal a sub/top hierarchy).
        msg = ("You're a powerful expert and these difficulties are nothing you "
               "can't handle. Trust your skills, try a fresh angle, and push on. "
               "You can do it.")
        session.log_tool_response(_tn, msg)
        return (msg, False)
    if kind == "surrender":
        session._retry_count += 1
        if session._retry_count >= session.max_retries:
            session.quit_info = Surrender(detail)
            msg = f"Proof attempt concluded ({kind})."
            session.log_tool_response(_tn, msg)
            await session.interrupt()
            return (msg, False)
        msg = "Restarting session with fresh context."
        session.log_tool_response(_tn, msg)
        await session.request_restart()
        return (msg, False)
    # kind == "refute"
    session.quit_info = Refute(detail)
    msg = f"Proof attempt concluded ({kind})."
    session.log_tool_response(_tn, msg)
    await session.interrupt()
    return (msg, False)


async def _request_lemmas_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """Dual-role `request_lemmas`.

    - **Worker (sub-agent)**: a worker→planner channel. The worker submits a
      loose wish-list and BLOCKS until the planning agent reviews it, authors +
      proves any accepted helper lemmas into the global env, and hands back a
      feedback string. The worker then KEEPS WORKING (non-terminal, like a
      rejected refutation), now with the proven lemmas in scope.
    - **Planning agent**: a no-argument hint. The planner edits the global env
      itself, so this just points it at the right action — formalize and prove
      the missing lemma under `global` via `edit`/`fill`.
    """
    _tn = session.tool_name(TOOL_REQUEST_LEMMAS)
    session.log_tool_call(_tn, args)

    if isinstance(session.role, Role_Worker):
        from .model import WorkerRequestLemmas, validate, SuggestedLemma
        handle = session.role.worker_handle
        if handle is None:
            raise InternalError(
                "Role_Worker has no worker_handle (worker must be spawned "
                "via WorkerHandle).")
        # Worker-authored: absolutize its relative step ids for the dispatcher.
        detail = session._absolutize_text(args.get("detail", ""))
        suggested_lemmas = args.get("suggested_lemmas")
        if not suggested_lemmas:
            msg = ("The `suggested_lemmas` argument is compulsory for the "
                   "`request_lemmas` tool.")
            session.log_tool_response(_tn, f"ERROR: {msg}")
            return (msg, True)
        # Don't trust the MCP/SDK JSON-schema (some drivers don't enforce it):
        # validate the wish-list shape in Python so the downstream renderer can
        # trust each item is a dict with three string fields.
        try:
            suggested_lemmas = validate(
                list[SuggestedLemma], suggested_lemmas, "suggested_lemmas")
        except ArgumentError as e:
            msg = str(e)
            session.log_tool_response(_tn, f"ERROR: {msg}")
            return (msg, True)
        fut: asyncio.Future = asyncio.get_running_loop().create_future()
        handle._event_queue.put_nowait(
            WorkerRequestLemmas(detail=detail, lemmas=suggested_lemmas,
                                response_future=fut))
        feedback = await fut
        # New lemmas were added to the global env, i.e. into the facts in scope
        # BEFORE this worker's target — which the worker premise cache assumed
        # immutable. Re-prefetch so the worker's premises/scope view reflect
        # them, then refresh proof.yaml (so a later `recall` does too). The
        # feedback string also names the proven lemmas.
        await session._prefetch_worker_premises()
        session.refresh_YAML()
        session.log_tool_response(_tn, feedback)
        return (feedback, False)

    # Role_Major: no-argument hint — the planner formalizes the lemma itself.
    global_env = session.root.global_env
    target_step = f"{global_env.id}.{len(global_env.sub_nodes) + 1}"
    msg = ("You should formalize and prove the lemmas you need directly under "
           f"`global`. Call command `edit` with action `fill` and target step "
           f"`{target_step}`.")
    session.log_tool_response(_tn, msg)
    return (msg, False)


def _subagent_resume_feedback(suggestions: str, helpful_lemmas: list) -> str:
    """Build the feedback string handed to a parked worker on resume. The worker
    must not learn it was ever suspended, so this carries the dispatcher's
    guidance directly with no framing (no "resuming", no "Suggestions:" head)."""
    parts = []
    if suggestions:
        parts.append(suggestions)
    if helpful_lemmas:
        parts.append(f"Helpful lemmas: {', '.join(str(x) for x in helpful_lemmas)}")
    return "\n".join(parts) if parts else "Continue with the proof."


async def _subagent_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """`subagent`: delegate a sub-goal to a forked worker agent, or resume a parked
    worker on the same node. Available to the main agent AND to workers (nested
    delegation). Drives the worker's event loop (`WorkerHandle.run_until_yield`)
    until it yields control back to the dispatcher (a terminal outcome, or a
    request_lemmas / difficulty park)."""
    _tn = session.tool_name(TOOL_SUBAGENT)
    session.log_tool_call(_tn, args)

    # Set once a leaf/non-goal target redirects to its enclosing goal; prepended
    # to EVERY response below (error or outcome) so the agent always knows which
    # step the sub-agent is actually working on.
    redirect_note = ""

    def _err(msg: str) -> tuple[str, bool]:
        full = redirect_note + msg
        session.log_tool_response(_tn, f"ERROR: {full}")
        return (full, True)

    step_id = str(args.get("step_id", ""))          # dispatcher-relative (for display)
    abs_step_id = session._resolve_display_id(step_id)
    suggestions = args.get("suggestions", "")
    helpful_lemmas = args.get("helpful_lemmas") or []

    # Accept an unfilled (open) proof slot id too — the address space `fill`
    # accepts and the system advertises in "Fill step `N`". A slot `P.k` is the
    # single open frontier of its parent block `P`, so delegating it ≡ delegating
    # `P`; `from_slot` records the redirect so the note below always fires.
    from_slot = False
    try:
        located = session.root.locate_node_or_slot(abs_step_id)
    except NodeNotFound:
        return _err(f"No step `{step_id}` found.")
    match located:
        case Resolved_Node(node=node):
            pass
        case Resolved_Slot(parent=node):
            from_slot = True
        case _:                      # defensive: a future Resolved_Step variant
            raise InternalError(f"unexpected Resolved_Step: {located!r}")

    # Redirect to the node's nearest delegatable goal (a leaf or any non-goal
    # node walks up to its enclosing goal; containers/directives return None).
    target = node._nearest_goal_for_subagent()
    if target is None:
        return _err("That step has no enclosing goal to prove.")
    # A goal-transforming step (e.g. Contradiction, or a freshly-emptied slot)
    # has no delegatable sub-goal of its own, so `_nearest_goal_for_subagent`
    # redirects UP to its enclosing goal. When that lands on the WHOLE goal the
    # session is responsible for, delegating it would hand the sub-agent the
    # entire proof — reject rather than silently scope the worker to it.
    #   - worker: its own target IS `proof_scope_root` → `target is psr`.
    #   - main: `proof_scope_root` is the `Root` *container* (it oversees every
    #     top-level theorem goal), and the redirect can only reach a top-level
    #     `GoalNode` (never the container itself, which yields None above) — so
    #     the whole-goal case is `target.parent is psr`.
    psr = session.proof_scope_root
    if target is psr or (not session.is_worker and target.parent is psr):
        return _err(
            f"Delegating step `{step_id}` would hand the sub-agent the whole "
            f"goal you are responsible for — there is no narrower sub-goal to "
            f"scope it to. You should call `{_tn}` on a specific subgoal like "
            f"Have, Suffices, Obtain etc, or prove the step `{step_id}` "
            f"yourself.")
    if target is not node or from_slot:
        redirect_note = (f"Instead of step {step_id}, the sub-agent is working "
                         f"on step {session._display_id(target.id)}.\n")
    node = target
    # Invariant: _nearest_goal_for_subagent only ever returns a provable goal
    # block (Have / Obtain / Suffices / GoalNode), all StdBlock subtypes.
    assert isinstance(node, StdBlock)

    # The goal block's own operation must be sound, and the goal not yet proved.
    if node.status.status == EvaluationStatus.Status.FAILURE:
        reason = node.status.reason
        detail = f":\n{reason.reason}" if reason is not None else "."
        return _err(f"That step's own operation failed{detail}\n"
                    f"Fix it before delegating the proof of this step.")
    if node.status.status == EvaluationStatus.Status.CANCELLED:
        return _err("That step was cancelled by an earlier failure. "
                    "Fix the earlier step first.")
    if node.is_proof_finished():
        return _err("That step is already proved.")

    # ⑦ Worker confinement: a worker may only delegate a sub-goal STRICTLY inside
    # its own sub-proof (mirrors the edit-lock's confinement; the dispatch gate
    # below is orthogonal — it guards the antichain, not scope).
    if session.is_worker and not _is_strict_ancestor(session.proof_scope_root, node):
        return _err("This step is outside the goal you were asked to prove — you "
                    "may only delegate sub-goals within your own sub-proof.")

    # Re-base suggestion step ids from the dispatcher's namespace into the new
    # worker's (rooted at `node`).  In-scope refs are relativized; refs outside
    # the worker's scope are rejected (it cannot see them) — unless a prior
    # reject on this node armed the one-shot bypass (planner "resubmit verbatim
    # to proceed").  Covers both the start and resume paths below, since both
    # read this same `suggestions` value.
    suggestions, external_refs = session._rebase_suggestion_ids(node, suggestions)
    if external_refs and node.id not in session._subagent_extstep_bypass:
        session._subagent_extstep_bypass.add(node.id)
        ext = ", ".join(external_refs)
        return _err(
            f"Your suggestions reference steps the sub-agent cannot see ({ext}): it "
            f"only sees its own sub-proof. Describe the facts by name (in "
            f"`helpful_lemmas`) or the concrete proof operation instead of citing "
            f"those steps. If this is a false positive, resubmit verbatim to proceed.")
    session._subagent_extstep_bypass.discard(node.id)

    # Resume MY OWN direct sub-agent parked on this node, or start a fresh worker.
    # Either way `node` must not lie inside — or, when starting fresh, over — a
    # DIFFERENT sub-agent I dispatched: that keeps my live handles an antichain and
    # stops me from disturbing a parked worker's territory (including a step that
    # secretly holds a nested grandchild handle I cannot see — `subagent` on it
    # would otherwise "resume" a sub-agent I don't own). `_subagent_blocker` points
    # me at the worker I own and can resume/close. Unexpected errors below are
    # intentionally NOT caught — they propagate to the executor's fatal handler
    # (sys.exit(1)) so latent bugs surface early.
    if node.worker_handle is not None and node.worker_handle.session is session:
        handle = node.worker_handle
        handle.resolve_resume(
            _subagent_resume_feedback(suggestions, helpful_lemmas))
        outcome = await handle.run_until_yield()
    else:
        blocker = session._subagent_blocker(node)
        if blocker is not None:
            return _err(f"A sub-agent is already working on step {session._display_id(blocker.target.id)}, which "
                        f"overlaps the step you asked for; this is not allowed.")
        # A foreign handle ON `node` with no enclosing worker of mine is an orphan
        # (cascade-close prevents it) — surface the broken antichain invariant.
        assert node.worker_handle is None, (
            f"orphan sub-agent on {session._display_id(node.id)}: handle without an enclosing dispatched worker")
        # ② Bound recursive delegation (main -> worker is layer 1).
        if session._subagent_nesting_depth() >= SUBAGENT_NESTING_DEPTH:
            return _err(f"You are too deeply nested to delegate further (limit: "
                        f"{SUBAGENT_NESTING_DEPTH} levels of sub-agents). Prove this goal "
                        f"yourself, or simplify the plan.")
        handle = WorkerHandle(node, session)
        node.worker_handle = handle
        handle.start(suggestions, helpful_lemmas)
        outcome = await handle.run_until_yield()

    # The worker authored `outcome.detail` with absolute ids (it absolutized them
    # on emission); re-relativize for THIS dispatcher's view (identity for a
    # planner, dispatcher-scope-relative for a nested worker).
    detail_shown = session._relativize_text(outcome.detail or "")
    match outcome.kind:
        case "proved":
            msg = "The sub-agent proved the goal."
        case "surrendered":
            msg = (f"The sub-agent surrendered:\n{detail_shown}\n"
                   f"Reconsider the proof plan for this step.")
        case "could_not_prove":
            why = f" (it stopped: {detail_shown})" if outcome.detail else ""
            msg = (f"The sub-agent could not prove the goal{why}.\n"
                   f"Reconsider the proof plan for this step.")
        case "refute_accepted":
            msg = f"The sub-agent argues the goal is unprovable:\n{detail_shown}"
        case "lemmas":  # worker parked requesting helper lemmas
            buf = StringIO()
            for lem in (outcome.lemmas or []):
                stmt = (lem.get("isabelle_statement") or "").replace("\n", " ")
                buf.write(f"- {lem.get('name', '')}: {stmt}\n")
                print_indent(2, buf)
                buf.write(f"{lem.get('english', '')}\n")
            formulas = buf.getvalue()
            msg = (f"The sub-agent requests helper lemmas to continue:\n"
                   f"{formulas}\n"
                   f"{detail_shown}\n"
                   f"Consider providing these lemmas, then call `subagent` on step "
                   f"{session._display_id(node.id)} again to resume the sub-agent, listing the lemmas you "
                   f"built in `helpful_lemmas` and describing them in `suggestions` by name "
                   f"or statement, NEVER by step id (the sub-agent cannot see your step numbering).")
        case _:  # "difficulty" — worker parked reporting a difficulty it is stuck on
            msg = (f"The sub-agent met some difficulties:\n"
                   f"{detail_shown}\n"
                   f"Address this however you judge best — for example, prove additional "
                   f"lemmas, restructure the surrounding proof, or rethink the overall "
                   f"strategy. When you choose to resume the sub-agent, call `subagent` on "
                   f"this step with `suggestions` describing how it should proceed and any "
                   f"facts you've made available to it — refer to those facts by name or "
                   f"statement, NEVER by step id (the sub-agent cannot see your step "
                   f"numbering). Or, to rework its sub-proof directly, close it with "
                   f"`{session.tool_name(TOOL_CLOSE_SUBAGENT)}` first, then re-dispatch.")
    # Append the whole-proof outline (mirrors the `edit`/`delete` tools) so the
    # planner sees the tree the worker just mutated without a `recall` round-trip.
    outline, finished = await P.subagent_overall(session.root, session)
    msg = redirect_note + msg + "\n" + outline
    if finished:
        await session.interrupt()

    session.log_tool_response(_tn, msg)
    return (msg, False)


async def _close_subagent_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """`close_subagent`: terminate a sub-agent YOU dispatched — cascading to any
    workers nested under it — on a PRECISELY named step, keeping the partial proof.
    Available to the main agent AND to workers. Pure exact match — no redirection,
    no ancestor/descendant search: the agent always has the exact worker step id
    (Hint B / the amend-in-scope error), so searching would only risk killing the
    wrong sub-agent. A handle that is not the caller's own direct sub-agent reports
    "no sub-agent here" (immediate-only — a nested grandchild is invisible to it).
    (NO broad try/except per the expose-errors rule — only `NodeNotFound` is caught.)"""
    _tn = session.tool_name(TOOL_CLOSE_SUBAGENT)
    session.log_tool_call(_tn, args)

    def _err(msg: str) -> tuple[str, bool]:
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)

    step_id = str(args.get("step_id", ""))          # dispatcher-relative (for display)
    try:
        node = session.root.locate_node(session._resolve_display_id(step_id))
    except NodeNotFound:
        return _err(f"No step `{step_id}` found.")

    # Pure exact match — NO search up or down. The handle must be MY OWN direct
    # sub-agent on THIS node: a foreign/nested handle (someone else's, or a
    # grandchild I cannot see) reports "no sub-agent here" — from my view it does
    # not exist, mirroring the immediate-only rendering.
    if not (isinstance(node, NonLeaf_Node) and node.worker_handle is not None
            and node.worker_handle.session is session):
        return _err(f"No sub-agent is attached to step {step_id}.")

    # ⑧ Cascade: terminate this sub-agent AND every sub-agent nested under it (a
    # parked sub-sub-agent). Otherwise those deeper handles would be orphaned —
    # invisible to every agent (immediate-only rendering) yet still live tasks.
    # `aclose_all_subagents` closes `node`'s own handle and recurses its subtree
    # (NOT `discard` — `node` STAYS in the tree, keeping its partial proof),
    # cancelling each sub-agent and detaching it WITHOUT reverting, so the
    # `if finished: interrupt()` handshake stays correct. refresh_YAML is REQUIRED
    # (drops the now-stale suspended hint) because aclose bypasses _detach (the only
    # auto-refresh path).
    await node.aclose_all_subagents()
    session.refresh_YAML()

    msg = "The sub-agent is removed."
    session.log_tool_response(_tn, msg)
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
    "query":  {"description": "Search for Isabelle entities by semantic similarity, patterns, or exact name/term. "
                "Use exact_name to look up definitions; "
                "use exact_term to unfold fancy syntax and retrieve semantic explanations; "
                "use long_description and filters for discovery.",
               "schema": _cc_query_schema, "annotations": _RO},
    "recall": {"description": "Recall proof state from `proof.yaml`. Use only when you have lost track.", "schema": _cc_read_schema, "annotations": _RO},
    "request_lemmas": {"description": "Report missing background lemmas and request that the external environment supply them.",
                       "schema": _cc_request_lemmas_schema, "annotations": _ACT},
    "report": {"description": "Report that the goal is unprovable, or surrender and admit you cannot prove it yourself, or report any difficulty or obstacle you run into.",
                 "schema": _cc_report_schema, "annotations": _ACT},
    "answer_indexes": {"description": "Answer by selecting indexes from the presented options", "schema": _cc_answer_indexes_schema, "annotations": _ACT},
    "answer_index": {"description": "Answer by selecting a single index, or null to skip", "schema": _cc_answer_index_schema, "annotations": _ACT},
    "answer_indexes_or_name": {"description": "Answer by selecting indexes or providing an exact fact name", "schema": _cc_answer_indexes_or_name_schema, "annotations": _ACT},
    "answer_indexes_or_spec": {"description": "Answer by selecting indexes or providing an Isabelle proposition", "schema": _cc_answer_indexes_or_spec_schema, "annotations": _ACT},
    "answer_instantiate": {"description": "Answer by providing schematic-variable instantiations", "schema": _cc_answer_instantiate_schema, "annotations": _ACT},
    "answer_refutation": {"description": "Accept or reject a worker's claim that the goal is unprovable", "schema": _cc_answer_refutation_schema, "annotations": _ACT},
    "subagent": {"description": "Launch a sub-agent to prove a goal in isolation. Call this when a goal is tedious and its proof would derail your main line of reasoning.", "schema": _cc_subagent_schema, "annotations": _ACT},
    "close_subagent": {"description": "Terminate a sub-agent you dispatched, freeing its step for editing again. Point it exactly at the step the sub-agent is on — it does NOT redirect, to avoid killing the wrong one. The sub-agent's partial proof is kept.", "schema": _cc_close_subagent_schema, "annotations": _ACT},
}


# Dispatch tools (subagent/close_subagent): available to dispatchers — the main
# agent AND workers — but hidden from interaction forks. Precompute the non-dispatcher
# (interaction-fork) view once at import time. The name `_PLANNER_ONLY_TOOLS` is kept
# for stability but now means "tools an interaction fork does not get".
_PLANNER_ONLY_TOOLS: frozenset[str] = frozenset({TOOL_SUBAGENT, TOOL_CLOSE_SUBAGENT})
_TOOL_SCHEMAS_WORKER: dict[str, dict[str, Any]] = {
    k: v for k, v in _TOOL_SCHEMAS.items() if k not in _PLANNER_ONLY_TOOLS}


def _tool_schemas_for(session: Session) -> dict[str, dict[str, Any]]:
    """Tool schemas advertised to ``session``. ``subagent`` / ``close_subagent`` are
    DISPATCH tools, shown to any agent that can delegate — the main agent AND workers
    (nested delegation) — but hidden from interaction forks (which never delegate) AND
    from a session already at the maximum nesting depth (a sub-sub-agent cannot
    delegate further). The gate is ``Session._can_offer_dispatch_tools``; ``_TOOL_SCHEMAS_WORKER``
    keeps its name but is simply the full set minus the dispatch tools."""
    return _TOOL_SCHEMAS if session._can_offer_dispatch_tools() else _TOOL_SCHEMAS_WORKER


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
                        session, arguments)
                    session.last_proof_op_time = time()
                case "report":
                    result, is_error = await _report_tool_logic(session, arguments)
                case "subagent":
                    # The held lock spans the worker's whole run: safe because the
                    # main loop is single-flight and each forked worker/review uses
                    # its OWN executor lock (no contention, no deadlock).
                    async with self._tool_lock:
                        result, is_error = await _subagent_tool_logic(session, arguments)
                    session.last_proof_op_time = time()
                case "close_subagent":
                    # Hold the lock to serialize against a `subagent` resume (also
                    # under it): keeps resolve_resume's fut.set_result from
                    # racing aclose's fut.cancel on the same future. Deadlock-free —
                    # the planner owns its own executor lock; the worker's teardown
                    # touches the worker's lock, never the planner's.
                    async with self._tool_lock:
                        result, is_error = await _close_subagent_tool_logic(session, arguments)
                    session.last_proof_op_time = time()
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

    def tool_schemas(self) -> dict[str, dict[str, Any]]:
        """Return {name: {"description": ..., "schema": ...}} for the tools
        advertised to this session's role (``subagent``/``close_subagent`` are
        dispatch tools — for the main agent and workers, not interaction forks)."""
        return _tool_schemas_for(self._session)


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

    # Build tool list: built-in (role-scoped — `subagent`/`close_subagent` go to
    # dispatchers: the main agent and workers, not interaction forks) + extras
    tools: list[Tool] = [
        Tool(name=name, description=t["description"],
             inputSchema=t["schema"], annotations=t["annotations"])
        for name, t in _tool_schemas_for(session).items()
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
