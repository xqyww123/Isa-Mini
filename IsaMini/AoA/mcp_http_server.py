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
import contextlib
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
    Root, GlobalEnv, GoalNode,
    Resolved_Node, Resolved_Slot,
    IsaTerm, ContinuingInteraction, ImmediateAnswer,
    AoA_Error, ArgumentError, IsabelleError, InternalError,
    CannotDelete_Root, NodeNotFound, ProofTreeTooDeep,
    EvaluationStatus, WorkerHandle, WorkerYield, Have, EditVerdict, _is_strict_ancestor,
    _is_direct_global_decl, _enclosing_global_decl,
    Parse_Op_List, Interaction_BadAnswer,
    AnswerIndexes, AnswerIndex, AnswerIndexesOrName, AnswerIndexesOrSpec,
    AnswerInstantiate, AnswerRefutation, AnswerStruggleAssessment,
    AnswerMissingLemmas, AnswerConstraintRequest,
    TOOL_EDIT, TOOL_DELETE, TOOL_SEARCH, TOOL_READ, TOOL_RECALL_REMOVED,
    TOOL_REQUEST_LEMMAS, TOOL_REPORT, TOOL_SUBAGENT, TOOL_CLOSE_SUBAGENT,
    DeletedEntry,
    TOOL_ANSWER_INDEXES, TOOL_ANSWER_INDEX, TOOL_ANSWER_INDEXES_OR_NAME,
    TOOL_ANSWER_INDEXES_OR_SPEC, TOOL_ANSWER_INSTANTIATE,
    TOOL_ANSWER_REFUTATION, TOOL_ANSWER_STRUGGLE_ASSESSMENT,
    TOOL_ANSWER_CONSTRAINT_REQUEST,
    Interaction_StruggleCheckpoint, Interaction_DifficultyEvaluation,
    Interaction_ConfirmLargeDelete,
    LARGE_DELETE_PROVED_THRESHOLD, LARGE_DELETE_TOTAL_THRESHOLD,
    InteractionPrompt, InteractionError, EditResult, InteractionChannel,
    executor_msg,
    ANSWER_TOOLS,
    ALL_PROOF_TOOLS,
    Role_Worker,
    Surrender, Refute, Refresh,
    LMUnreachable, ResourceUnavailable,
    TOOL_REFRESH, TOOL_WRITE_MEMORY,
    print_indent, print_goal, MyIO,
)
import yaml as _yaml
from dataclasses import dataclass, field
from .retrieval import (
    BATCHED_SEMANTIC_SEARCH,
    _query_tool_logic,
    _cc_query_schema,
)
from . import prompts as P
from . import config


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
_cc_request_lemmas_schema = _load_schema(
    "cc_request_no_general.jsonc"
    if config.DISABLE_REQUEST_GENERAL_LEMMAS
    else "cc_request.jsonc")
_cc_report_schema = _load_schema("cc_report.jsonc")
_cc_answer_indexes_schema = _load_schema("cc_answer_indexes.jsonc")
_cc_answer_index_schema = _load_schema("cc_answer_index.jsonc")
_cc_answer_indexes_or_name_schema = _load_schema("cc_answer_indexes_or_name.jsonc")
_cc_answer_indexes_or_spec_schema = _load_schema("cc_answer_indexes_or_spec.jsonc")
_cc_answer_instantiate_schema = _load_schema("cc_answer_instantiate.jsonc")
_cc_answer_refutation_schema = _load_schema("cc_answer_refutation.jsonc")
_cc_answer_struggle_assessment_schema = _load_schema("cc_answer_struggle_assessment.jsonc")
_cc_answer_missing_lemmas_schema = _load_schema("cc_answer_missing_lemmas.jsonc")
_cc_answer_constraint_request_schema = _load_schema("cc_answer_constraint_request.jsonc")
_cc_subagent_schema = _load_schema("cc_subagent.jsonc")
_cc_close_subagent_schema = _load_schema("cc_cancel_subagent.jsonc")
_cc_recall_removed_schema = _load_schema("cc_recall_removed.jsonc")
_cc_refresh_schema = _load_schema("cc_refresh.jsonc")
_cc_write_memory_schema = _load_schema("cc_write_memory.jsonc")



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


def _merge_edit_operations_schema(flat: dict) -> dict:
    """Codex variant of the ``edit`` schema: collapse the ``proof_operations``
    item UNION into a SINGLE permissive object.

    codex-cli 0.141.0's MCP->model schema sanitizer empties every ``anyOf``/
    ``oneOf`` branch (and every ``$ref``) to ``{}`` (wire-verified), so a
    discriminated union reaches the model as ``items: {anyOf: [{}, ...]}`` — the
    ``operation`` discriminator and all field names lost, leaving the model to
    guess. Merging the operation members into one object — ``operation`` as an
    enum of the member consts, plus the union of all member properties (first wins
    on key collision), ``required: ["operation"]`` — survives the sanitizer: the
    model receives the discriminator enum and every field name. codex still
    empties nested object/array property *values* to ``{}``, so structured
    sub-fields keep only their name (their shape must be conveyed in the tool
    description); the model's emitted ops are unchanged and still validated
    against the real schema server-side."""
    import copy
    flat = copy.deepcopy(flat)
    items = flat["properties"]["proof_operations"]["items"]
    members = items.get("anyOf") or items.get("oneOf") or [items]
    op_consts: list = []
    merged_props: dict = {}
    for m in members:
        props = m.get("properties", {})
        const = props.get("operation", {}).get("const")
        if const is not None and const not in op_consts:
            op_consts.append(const)
        for k, v in props.items():
            if k != "operation":
                merged_props.setdefault(k, v)  # first wins on collision
    flat["properties"]["proof_operations"]["items"] = {
        "type": "object",
        "properties": {"operation": {"type": "string", "enum": op_consts},
                       **merged_props},
        "required": ["operation"],
        "additionalProperties": False,
    }
    return flat


_cc_edit_schema_codex = _merge_edit_operations_schema(_cc_edit_schema_flat)
_assert_no_refs(_cc_edit_schema_codex)


# ============================================================================
# Permission Check (both modes)
# ============================================================================

_MUTATION_TOOLS = frozenset({
    TOOL_EDIT, TOOL_DELETE, TOOL_SUBAGENT, TOOL_CLOSE_SUBAGENT,
    # `request` is channel-routed (it can become the `_suspended_task`) and both its
    # auto-prove-general path (global env) and its constraint path (an amend on a
    # delegated block) mutate the tree — so, like the others, it must be blocked by
    # `_check_tool_permission` while a non-forking interaction is pending (else it
    # would slip past and hit the generic busy-guard instead).
    TOOL_REQUEST_LEMMAS,
})

def _check_tool_permission(session: Session, tool_name: str) -> str | None:
    """Check interaction state. Returns error message or None.

    Uses the unified ``session.pending_interaction`` which covers both
    forking (fork session with ``Role_Interaction``) and non-forking
    (main session with ``_nf_pending_interaction``) paths.

    Fork sessions are additionally restricted to the tools declared in
    ``interaction.fork_allowed_tools``.
    """
    pi = session.pending_interaction
    if pi is not None:
        if tool_name in ANSWER_TOOLS:
            if tool_name == pi.answer_tool_name:
                return None
            answer_tn = session.tool_name(pi.answer_tool_name)
            return (f"Wrong answer tool. Use `{answer_tn}` "
                    f"to answer the current question.")
        if session.fork_pending is not None and tool_name in ALL_PROOF_TOOLS:
            allowed = pi.fork_allowed_tools
            if tool_name not in allowed:
                allowed_list = ", ".join(
                    f"`{session.tool_name(t)}`" for t in allowed)
                answer_tn = session.tool_name(pi.answer_tool_name)
                return (f"Tool `{session.tool_name(tool_name)}` is not allowed. "
                        f"Only {allowed_list} "
                        f"{'is' if len(allowed) == 1 else 'are'} available. "
                        f"Use the `{answer_tn}` tool to submit your answer.")
        if session._nf_pending_interaction is not None:
            if tool_name in _MUTATION_TOOLS:
                answer_tn = session.tool_name(pi.answer_tool_name)
                return (f"An interaction question is pending. "
                        f"Answer it with `{answer_tn}` first.")
        return None
    if tool_name in ANSWER_TOOLS:
        answer_tn = session.tool_name(tool_name)
        return (f"No question pending. The `{answer_tn}` tool can only "
                f"be used when there is a question for you to answer.")
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

    # Tolerant redirect: the LLM sometimes calls `edit` with delete-style args
    # (`action: "delete"` + `target_steps` instead of `target_step`).  Proxy to
    # the real delete handler instead of erroring on missing `target_step`.
    if args.get("action") == "delete" and "target_steps" in args:
        return await _delete_tool_logic(session, args)

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
                         "elsewhere, use `request`.")
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
        # Global-lemma delegation gate (opt-in, non-worker-major only): block a
        # fill/insert_before/amend that writes INTO a global declaration's proof
        # body, steering the major to dispatch a sub-agent instead. delete and
        # one-shot inline-proof declarations stay allowed (location-only gate).
        if (session.is_major and not session.is_worker
                and session.gate_global_lemma_proofs):
            _blocked, _gtarget = session._global_lemma_gate(abs_step, action)
            if _blocked and _gtarget is not None:
                error_msg = (
                    "Declaring global lemmas is great though you shouldn't prove a global "
                    "lemma yourself. Dispatch a sub-agent with `subagent` on step "
                    f"{session._display_id(_gtarget.id)} to prove it.")
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
        if not is_error:
            session._session_edit_count += 1
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


def _archive_node(node: Node, session: Session) -> DeletedEntry:
    title = node.quickview_title()
    goal_str = ""
    if isinstance(node, StdBlock):
        try:
            goal = node.goal()
            if goal is not None:
                goal_str = f" | {goal.conclusion.unicode}"
        except Exception:
            pass
    if isinstance(node, StdBlock):
        was_proved = node.is_proof_finished()
    else:
        was_proved = node.status.status == EvaluationStatus.Status.SUCCESS
    proved_str = "proved" if was_proved else "unproved"
    summary = f"{title}{goal_str} [{proved_str}]"
    rendered_yaml = node.print_string(0)
    return DeletedEntry(summary=summary, rendered_yaml=rendered_yaml, was_proved=was_proved)


async def _delete_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_DELETE)
    session.log_tool_call(_tn, args)
    # IsabelleError caught here (not in execute) so it stays a recoverable
    # (msg, True) return and still triggers the mutate cooldown; other
    # exceptions propagate to ToolExecutor.execute for unified handling.
    archive_len_before = len(session.runtime.deleted_archive)
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
                             "elsewhere, use `request`.")
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
        # Locate every unique target once; reused by the large-delete gate and
        # the archive loop. Unfound ids fall through to root.delete's
        # not-found handling below.
        located: dict[str, Node] = {}
        for sid in abs_steps:
            if sid in located:
                continue
            try:
                located[sid] = session.root.locate_node(sid)
            except NodeNotFound:
                pass

        # Large-delete gate: when the targets carry substantial proved work,
        # ask the agent to reconsider before anything is torn down. Skipped
        # without a channel (`launch_interaction` would fork a sub-agent
        # instead of asking inline — e.g. test sessions) and in interaction
        # forks (which must never nest a non-forking interaction; today they
        # cannot reach `delete` at all — this is a defensive guard).
        if session._channel is not None and not session.is_interaction:
            # Stats must not double-count nested targets: keep only targets
            # with no targeted proper ancestor (order-independent).
            nodes = set(located.values())
            entries = [
                (sid, *node.subtree_stats())
                for sid, node in located.items()
                if not any(anc is not node and _is_strict_ancestor(anc, node)
                           for anc in nodes)]
            total = sum(t for _, t, _ in entries)
            proved = sum(p for _, _, p in entries)
            if (proved >= LARGE_DELETE_PROVED_THRESHOLD
                    and total >= LARGE_DELETE_TOTAL_THRESHOLD):
                choice = await session.launch_interaction(
                    Interaction_ConfirmLargeDelete(entries))
                if choice == "cancel":
                    response = P.delete_cancelled_message()
                    session.log_tool_response(_tn, response)
                    return (response, False)
                # choice == "proceed": fall through to the normal delete path.

        archived_indices: list[int] = []
        archived_ids: set[str] = set()
        for sid in abs_steps:
            node = located.get(sid)
            if node is None or sid in archived_ids:
                continue
            idx = len(session.runtime.deleted_archive)
            entry = _archive_node(node, session)
            session.runtime.deleted_archive.append(entry)
            archived_ids.add(sid)
            archived_indices.append(idx)
        try:
            not_found = await session.root.delete(abs_steps)
            if len(not_found) == len(abs_steps):
                del session.runtime.deleted_archive[archive_len_before:]
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
            if archived_indices:
                _tn_rr = session.tool_name(TOOL_RECALL_REMOVED)
                if len(archived_indices) == 1:
                    response += f"\nArchived as entry {archived_indices[0]}. Use `{_tn_rr}` to review."
                else:
                    idx_str = ", ".join(str(i) for i in archived_indices)
                    response += f"\nArchived as entries {idx_str}. Use `{_tn_rr}` to review."
            if finished:
                await session.interrupt()
            if deleted:
                session._session_delete_count += 1
            if (not finished
                    and session.is_worker
                    and session._should_struggle_checkpoint()):
                checkpoint_feedback = await _run_struggle_checkpoint(session)
                if checkpoint_feedback is not None:
                    response = response + "\n\n---\n" + checkpoint_feedback
        except AoA_Error as e:
            del session.runtime.deleted_archive[archive_len_before:]
            error_msg = str(e)
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        session.log_tool_response(_tn, response)
        session.log_proof_tree_snapshot("after_delete")
        return (response, False)
    except IsabelleError as e:
        del session.runtime.deleted_archive[archive_len_before:]
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


def _parse_answer_payload(tool_name: str, args: dict):
    """Parse raw tool arguments into a typed answer payload.

    Returns the payload on success, or an error message string on unknown tool.
    """
    match tool_name:
        case "answer_indexes":
            return AnswerIndexes(indexes=_extract_indexes(args))
        case "answer_index":
            raw = args.get("index")
            return AnswerIndex(index=raw if isinstance(raw, int) else None)
        case "answer_indexes_or_name":
            return AnswerIndexesOrName(
                indexes=_extract_indexes(args),
                name=args.get("name") or None)
        case "answer_indexes_or_spec":
            return AnswerIndexesOrSpec(
                indexes=_extract_indexes(args),
                statement=args.get("statement") or None)
        case "answer_instantiate":
            return AnswerInstantiate(
                instantiations=_extract_instantiations(args))
        case "answer_refutation":
            return AnswerRefutation(
                accept=bool(args["accept"]),
                reason=args["reason"])
        case "answer_struggle_assessment":
            return AnswerStruggleAssessment(
                is_stuck=bool(args["is_stuck"]),
                summary=args.get("summary", ""))
        case "answer_missing_lemmas":
            raw = args.get("missing_lemmas")
            if isinstance(raw, str):
                try:
                    raw = json.loads(raw)
                except (json.JSONDecodeError, ValueError):
                    raw = None
            # Defensive (mirrors _extract_indexes): keep only dict items so a
            # malformed answer can't crash the logger downstream.
            items = ([i for i in raw if isinstance(i, dict)]
                     if isinstance(raw, list) else [])
            return AnswerMissingLemmas(missing_lemmas=items)
        case "answer_constraint_request":
            raw = args.get("constraints")
            # Defensive (mirrors answer_missing_lemmas): keep only dict items so a
            # malformed answer can't crash the interaction's `answer()`.
            cons = ([i for i in raw if isinstance(i, dict)]
                    if isinstance(raw, list) else [])
            return AnswerConstraintRequest(
                verdict=str(args.get("verdict") or ""),
                constraints=cons,
                reason=str(args.get("reason") or ""))
        case _:
            return f"Unknown answer tool: {tool_name}"


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

        payload = _parse_answer_payload(tool_name, args)
        if isinstance(payload, str):
            session.log_tool_response(_tn, f"ERROR: {payload}")
            return (payload, True)

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
                resolved = IsaTerm.to_unicode(ia.answer)
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
        # tool response, not the string "None" (``to_unicode`` maps None → "").
        result_str = IsaTerm.to_unicode(result)
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
    if session._nf_pending_interaction is None:
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
        # ``line`` is 1-indexed; 0 is not a valid line, so treat it as the
        # first line rather than letting ``start - 1 == -1`` wrap to the file's
        # tail (negative ``line`` still indexes from the end intentionally).
        if line_num == 0:
            line_num = 1
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
    def _segment_range(node: Node) -> tuple[int, int, list[str]]:
        """Return the (start, end_line, lines) actually printed for ``node``."""
        node_start = node.line
        node_end = _node_end_line(node, total_lines, scope_root)
        if explicit_range is None:
            end = node_end
        else:
            end = min(node_start + range_lines - 1, node_end)
        end = min(end, total_lines)
        selected = all_lines[node_start - 1 : end]
        end_line = node_start + len(selected) - 1
        return node_start, end_line, selected

    # First pass: resolve/validate each id. Failures become inline warnings;
    # successes record the node and its printed range so the second pass can
    # detect containment.
    entries: list[tuple[str, Any]] = []   # ("warn", text) | ("node", (node, start, end, lines))
    for sid in step_ids:
        # `sid` is worker-relative (as supplied) — keep it for messages, resolve
        # to the absolute tree id for the lookup.
        try:
            node = session.root.locate_node(session._resolve_display_id(sid))
        except NodeNotFound:
            abs_id = session._resolve_display_id(sid)
            try:
                slot = session.root.locate_node_or_slot(abs_id)
            except NodeNotFound:
                slot = None
            if isinstance(slot, Resolved_Slot):
                parent = slot.parent
                if isinstance(parent, StdBlock):
                    goal_info = parent.should_I_show_pending_goal()
                    if goal_info is not None:
                        goal, to_fill = goal_info
                        buf = StringIO()
                        f = MyIO(buf)
                        f.write(f"Step '{sid}' is a filling slot.\n")
                        f.write("pending proof goal:\n")
                        print_goal(goal, 1, False, f, parent._ctxt_of_filling())
                        result_text = buf.getvalue()
                        if single_step:
                            session.log_tool_response(_tn, result_text)
                            return (result_text, False)
                        entries.append(("warn", result_text))
                        continue
                error_msg = (f"Step '{sid}' is a filling slot that has not been "
                             "written yet.")
                if single_step:
                    session.log_tool_response(_tn, f"ERROR: {error_msg}")
                    return (error_msg, True)
                entries.append(("warn", f"WARNING: {error_msg}"))
                continue
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
            entries.append(("warn", f"WARNING: Step '{sid}' doesn't exist."))
            continue
        if node.line == 0:
            error_msg = (
                f"Step '{sid}' has no line information (proof not yet printed). "
                "Read by line number instead.")
            if single_step:
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
            entries.append(("warn", f"WARNING: {error_msg}"))
            continue
        if not _line_is_fresh(node, scope_root, session.is_worker):
            error_msg = (
                f"Step '{sid}' is outside your current proof scope, "
                "so its location is unavailable.")
            if single_step:
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
            entries.append(("warn", f"WARNING: {error_msg}"))
            continue
        start, end_line, selected = _segment_range(node)
        entries.append(("node", (node, start, end_line, selected)))

    # Second pass: a step whose printed range is strictly inside another
    # requested step's printed range is already shown within that enclosing
    # segment, so we print only its header (not its content).
    ranges = [e[1] for e in entries if e[0] == "node"]
    segments: list[str] = []
    for kind, payload in entries:
        if kind == "warn":
            segments.append(payload)
            continue
        node, start, end_line, selected = payload
        disp = session._display_id(node.id)
        contained = any(
            o_node is not node and o_start <= start and end_line <= o_end
            and (o_start < start or o_end > end_line)
            for o_node, o_start, o_end, _ in ranges)
        if contained:
            segments.append(
                f"[Step {disp} is at Line {start}-{end_line}; "
                f"content already shown above]")
        else:
            segments.append(
                f"[Step {disp} is at Line {start}, showing Line "
                f"{start}-{end_line}]\n" + "".join(selected))

    result = "\n".join(segments)
    session.log_tool_response(_tn, result)
    return (result, False)


async def _recall_removed_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_RECALL_REMOVED)
    session.log_tool_call(_tn, args)

    archive = session.runtime.deleted_archive
    if not archive:
        msg = "The archive is empty — no proof steps have been deleted yet."
        session.log_tool_response(_tn, msg)
        return (msg, False)

    index = args.get("index")
    line_num = args.get("line")
    range_lines = int(args.get("range", 50))

    if index is None and line_num is not None:
        msg = "`line` requires `index`. Call with no arguments to list all entries."
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)

    if index is None:
        lines = []
        for i, entry in enumerate(archive):
            lines.append(f"  {i}: {entry.summary}")
        result = f"Deleted node archive ({len(archive)} entries):\n" + "\n".join(lines)
        session.log_tool_response(_tn, result)
        return (result, False)

    index = int(index)
    if index < 0 or index >= len(archive):
        msg = f"Invalid index {index}. Archive has {len(archive)} entries (0–{len(archive) - 1})."
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)

    entry = archive[index]
    yaml_lines = entry.rendered_yaml.splitlines(keepends=True)
    total = len(yaml_lines)

    if line_num is None:
        header = f"Archived entry {index} ({entry.summary}):\n"
        if total <= 200:
            result = header + entry.rendered_yaml
        else:
            shown = "".join(yaml_lines[:200])
            result = (header + f"[Line 1–200 of {total}]\n" + shown
                      + f"\n... ({total - 200} more lines. Use `line` and `range` to navigate.)")
        session.log_tool_response(_tn, result)
        return (result, False)

    line_num = int(line_num)
    if line_num < 1:
        line_num = 1
    if line_num > total:
        msg = f"Line {line_num} is past the end of the entry ({total} lines)."
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)
    start = line_num
    end = min(start + range_lines - 1, total)
    selected = yaml_lines[start - 1 : end]
    end_line = start + len(selected) - 1
    header = f"Archived entry {index} ({entry.summary}):\n"
    result = header + f"[Line {start}–{end_line} of {total}]\n" + "".join(selected)
    session.log_tool_response(_tn, result)
    return (result, False)


async def _run_struggle_checkpoint(session: Session) -> str | None:
    """Fork an assessment of whether the worker is stuck, and if so park it
    via ``WorkerDifficulty`` so the dispatcher can intervene.

    Returns the dispatcher's feedback string when the worker was parked and
    resumed, or ``None`` if the assessment concluded the worker is not stuck
    (or the assessment fork failed)."""
    from .model import WorkerDifficulty, Role_Worker, MyIO
    if not isinstance(session.role, Role_Worker):
        return None
    handle = session.role.worker_handle
    target = session.role.target
    if handle is None:
        return None

    delete_count = session._session_delete_count
    edit_count = session._session_edit_count
    checkpoint_num = session._struggle_checkpoint_count + 1

    interaction = Interaction_StruggleCheckpoint(
        target=target,
        delete_count=delete_count,
        edit_count=edit_count,
        checkpoint_number=checkpoint_num,
    )

    try:
        is_stuck, summary = await session.launch_interaction(interaction)
    except Exception as e:
        session.warn_AoA_opr(
            f"Struggle checkpoint fork failed: {type(e).__name__}: {e}")
        session._reset_struggle_counters()
        return None

    session._struggle_checkpoint_count = checkpoint_num
    session._reset_struggle_counters()

    if not is_stuck:
        session.log_interaction("struggle_checkpoint",
            f"checkpoint #{checkpoint_num}: not stuck. {summary}")
        return None

    buf = StringIO()
    session.quickview_proof_scope(0, MyIO(buf))
    quickview = buf.getvalue()
    detail = (
        f"[System checkpoint #{checkpoint_num}] "
        f"After {edit_count} edit calls and {delete_count} delete calls, "
        f"an assessment found this worker is stuck:\n{summary}\n\n"
        f"Current proof state:\n{quickview}")

    fut: asyncio.Future = asyncio.get_running_loop().create_future()
    handle._event_queue.put_nowait(
        WorkerDifficulty(detail=detail, response_future=fut))
    feedback = await fut

    await session._prefetch_worker_premises()
    session.refresh_YAML()
    # Append a notice of any facts the planner added to this worker's scope while it
    # was parked (appended at the end for LLM recency/salience). Reached only when the
    # checkpoint actually parked+resumed the worker, so no extra guard is needed.
    notice = session.consume_new_scope_facts_notice()
    if notice:
        feedback = feedback + "\n\n" + notice
    session.log_interaction("struggle_checkpoint",
        f"checkpoint #{checkpoint_num}: stuck, parked, resumed with: {feedback}")
    return feedback


async def _report_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_REPORT)
    session.log_tool_call(_tn, args)
    kind = args.get("type", "surrender")
    # Worker-authored: expand its scope-relative step ids to absolute so the
    # detail still reads correctly once surfaced to the (differently-scoped)
    # dispatcher; the dispatcher re-relativizes for its own view.
    detail = session._absolutize_text(args.get("detail", ""))
    if kind not in ("refute", "surrender"):
        msg = f"Invalid type: {kind!r}. Must be `refute` or `surrender`."
        session.log_tool_response(_tn, f"ERROR: {msg}")
        return (msg, True)

    if isinstance(session.role, Role_Worker):
        from .model import WorkerRefute, WorkerSurrender
        handle = session.role.worker_handle
        if handle is None:
            # A worker is always spawned via WorkerHandle, which sets
            # role.worker_handle. A missing handle is a programming error, not a
            # runtime condition to paper over.
            raise InternalError(
                "Role_Worker has no worker_handle (worker must be spawned "
                "via WorkerHandle).")

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


async def _lemma_statement_is_general(state, statement) -> 'tuple[bool, list[str]]':
    """Judge whether a requested lemma (a ``LongStatement``) is GENERAL by term
    structure: every free variable occurring in its ``conclusion`` and in each
    ``premises[].term`` must be declared in ``for_any``, and no schematic variable
    (``?x``) may appear anywhere. Returns ``(is_general, blocking_names)`` — the
    second element lists the offending variable names (undeclared frees, plus any
    schematic base names, deduped in first-seen order) used to build the rejection
    message; empty when general or when the statement does not parse.

    Each term is parsed against ``state`` — the proof state at the global fill slot
    the lemma would occupy (``GlobalEnv._resulting_state_of_all_children()``), so a
    constant from a PRIOR global ``Define`` resolves (not wrongly flagged) while a
    worker-local fix does NOT mask an undeclared reference. A parse failure or an
    uninitialised ``state`` ⟹ non-general (conservative: an unparseable/unanchored
    lemma is never auto-proved; it falls through to the planner-park path)."""
    from .model import InternalError_UnparsedTerm
    if not state.initialized():
        return (False, [])
    declared = {v.get("name") for v in (statement.get("for_any") or [])}
    terms = [statement["conclusion"]]
    terms += [p["term"] for p in (statement.get("premises") or [])]
    blocking: list[str] = []
    for term in terms:
        try:
            _typ, frees, schematics = await state.check_term(term)
        except InternalError_UnparsedTerm:
            return (False, [])
        except IsabelleError as e:
            # `check_term` re-raises a bare IsabelleError for a read_term failure
            # (the ML callback tags it "Unparsed: ..."); a top-level unbound
            # schematic `?x` arrives this way too, so it lands here rather than the
            # `schematics`-set branch below. Treat an "Unparsed" failure as
            # non-general (the lemma can't be cleanly anchored at this slot), but let
            # a genuine infrastructure fault (connection drop, state-not-found, ...)
            # PROPAGATE rather than silently classifying every requested lemma
            # non-general.
            if e.errors and str(e.errors[0]).startswith("Unparsed"):
                return (False, [])
            raise
        # A schematic ?x.i is reported as "?x.i"; its base name `x` is what the
        # agent would declare in for_any (and write as a fixed `x`).
        for s in schematics:
            base = s.unicode.lstrip("?").split(".", 1)[0]
            if base and base not in blocking:
                blocking.append(base)
        for f in frees:
            nm = f.unicode
            if nm not in declared and nm not in blocking:
                blocking.append(nm)
    return (len(blocking) == 0, blocking)


def _requested_lemma_failed_line(name: str, reason: str) -> str:
    """§G4 failed-outcome line, relaying the prover's actual terminal reason."""
    reason = (reason or "").strip()
    if not reason:
        return f"Requested lemma `{name}` could not be established."
    if not reason.endswith((".", "!", "?")):
        reason += "."
    return f"Requested lemma `{name}` could not be established: {reason}"


def _requested_lemma_undeclared_line(name: str, blocking: 'list[str]') -> str:
    """Force-general rejection line: a requested `general_lemmas` item has free
    variables not declared in `for_any`. Singular/plural is COMPUTED (no lazy
    "(s)"); "all its variables" stays plural — it is the rule."""
    vlist = ", ".join(f"`{v}`" for v in blocking)
    noun = "a free variable" if len(blocking) == 1 else "free variables"
    return (f"A general lemma must declare all its variables in `for_any`, but "
            f"the requested `{name}` has {noun} {vlist}.")


async def _request_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """Dual-role `request`.

    - **Worker (sub-agent)**: a worker→dispatcher channel with two parameters:
      - `general_lemmas`: genuinely GENERAL helper lemmas (every free variable
        declared in `for_any`). FORCE-checked — a non-general item is REJECTED
        upfront (process nothing; the worker resubmits with `for_any` complete),
        never parked. General items are auto-declared in the global env and proved
        by a headless prover, synchronously; the worker resumes with them in scope.
      - `constraints`: conditions the worker's sub-goal needs but was not given
        (the dispatcher under-provisioned it). Each is routed to the DISPATCHER
        via ``WorkerRequestConstraints`` → ``Interaction_ReviewConstraint``
        (resolved IN-LOOP in ``run_until_yield``); on accept for an amendable
        target the condition is added as a premise of the delegated block.
      The worker BLOCKS until both are processed, then KEEPS WORKING — UNLESS the
      processed lemmas/constraints discharge its ENTIRE target scope, in which case
      the response announces completion and the worker terminates via the interrupt
      handshake (conditionally terminal, mirroring `edit`'s finish path).
    - **Planning agent**: a no-argument hint pointing it at the right action —
      formalize and prove the missing lemma under `global` via `edit`/`fill`, or,
      when the global-lemma gate is on, declare it under `global` and dispatch a
      sub-agent to prove it.
    """
    _tn = session.tool_name(TOOL_REQUEST_LEMMAS)
    session.log_tool_call(_tn, args)

    if isinstance(session.role, Role_Worker):
        from .model import (WorkerRequestConstraints, validate, SuggestedLemma,
                            RequestConstraint)
        handle = session.role.worker_handle
        if handle is None:
            raise InternalError(
                "Role_Worker has no worker_handle (worker must be spawned "
                "via WorkerHandle).")
        # Worker-authored: absolutize its relative step ids for the dispatcher.
        detail = session._absolutize_text(args.get("detail", ""))
        general_lemmas = args.get("general_lemmas")
        constraints = args.get("constraints")
        if not general_lemmas and not constraints:
            msg = ("Provide at least one constraint (a condition your sub-goal "
                   "is missing)."
                   if config.DISABLE_REQUEST_GENERAL_LEMMAS else
                   "Provide at least one of `general_lemmas` (helper lemmas to be "
                   "proved by an auto-dispatched sub-agent) or `constraints` "
                   "(conditions your sub-goal is missing).")
            session.log_tool_response(_tn, f"ERROR: {msg}")
            return (msg, True)
        # Don't trust the MCP/SDK JSON-schema (some drivers don't enforce it):
        # validate both argument shapes in Python before reading them.
        try:
            general_lemmas = validate(
                list[SuggestedLemma], general_lemmas or [], "general_lemmas")
            constraints = validate(
                list[RequestConstraint], constraints or [], "constraints")
        except ArgumentError as e:
            msg = str(e)
            session.log_tool_response(_tn, f"ERROR: {msg}")
            return (msg, True)
        # Mirror every requested general lemma into missing_lemmas.yaml — a worker
        # asking for a lemma is a free signal for the external import-expansion
        # loop. Keep the FLAT {name, english, isabelle_statement} shape that loop's
        # watcher reads (tools/missing_lemma_loop/watcher.py), deriving the two
        # strings from the LongStatement; do NOT leak the nested shape into it.
        if general_lemmas:
            session.log_missing_lemmas(
                "request",
                [{"name": l["name"],
                  "english": l["statement"].get("english", ""),
                  "isabelle_statement": l["statement"].get("conclusion", ""),
                  "detail": detail}
                 for l in general_lemmas])

        # Gate: general-lemma requests are disabled for this case. The lemmas were
        # already mirrored into missing_lemmas.yaml above (the external loop's
        # signal is kept); here we DROP them from the auto-prove path and nudge the
        # worker to prove the needed special case directly. Any `constraints` in
        # the same call are still processed below. Emptying the list makes the
        # force-general check and the GENERAL auto-prove loop no-op cleanly.
        gated_general_msg = ""
        if config.DISABLE_REQUEST_GENERAL_LEMMAS and general_lemmas:
            gated_general_msg = config.DISABLED_GENERAL_LEMMA_REQUEST_MSG
            general_lemmas = []

        # Where do auto-proved general lemmas go? They MUST land BEFORE the
        # requesting worker's target so the worker can SEE them (a worker's scope is
        # only the declarative facts of siblings PRECEDING its target —
        # `_all_fixed_facts_before_a_child` stops at the target). A worker on a
        # top-level goal has its target after every global child, so the END of the
        # global env is already before it. But a worker whose target lives INSIDE
        # the global env — a headless prover on a global Have, or a worker on a
        # deferred global Define — would get an end-appended lemma placed AFTER its
        # target, out of scope. For that case insert each lemma immediately before
        # `gl_anchor`, the global-env-direct-child ancestor of the target.
        global_env = session.root.global_env
        _tgt = session.role.target
        gl_anchor = (_tgt if _is_direct_global_decl(_tgt)
                     else _enclosing_global_decl(_tgt))
        # FORCE-GENERAL (all workers): classify each requested lemma against the
        # state at its ACTUAL insertion slot — the anchor's pre-state when inserting
        # in-env (so a constant the anchor or a later global child declares is
        # correctly out of scope), else the global end state. Prior global
        # declarations visible; worker-local fixes excluded. Any non-general item
        # REJECTS the whole call upfront (process nothing) so it resubmits with every
        # free variable declared in `for_any` — the already-general items are then
        # auto-proved cleanly on the retry, with no duplicate global Haves. This
        # replaces v3's non-general planner-park branch entirely.
        slot_state = (gl_anchor.ml_state if gl_anchor is not None
                      else global_env._resulting_state_of_all_children())
        nongeneral_lines: list[str] = []
        for lem in general_lemmas:
            ok, blocking = await _lemma_statement_is_general(
                slot_state, lem["statement"])
            if not ok:
                if blocking:
                    nongeneral_lines.append(
                        _requested_lemma_undeclared_line(lem["name"], blocking))
                else:
                    # Non-general only because the statement does not parse.
                    nongeneral_lines.append(
                        f"The requested lemma `{lem['name']}` could not be parsed "
                        f"as an Isabelle term.")
        if nongeneral_lines:
            msg = "\n".join(nongeneral_lines)
            session.log_tool_response(_tn, f"ERROR: {msg}")
            return (msg, True)

        outcome_lines: list[str] = []
        any_scope_change = False

        # `root.fill` retargets `session.working_block` to the fill's parent (the
        # global env); save the worker's own working block and restore it after, so
        # the worker's retrieval context (the `query` tool) is unaffected by the
        # global-Have declarations we make here.
        saved_working_block = session.working_block

        # --- GENERAL path: auto-declare a global Have + prove it with a headless
        # prover, synchronously. proved → keep; otherwise → delete + relay reason. ---
        for lem in general_lemmas:
            nm = lem["name"]
            stmt = lem["statement"]
            parsed = Have.gen_single({
                "thought": detail or "requested helper lemma",
                "statement": stmt,
                "name": nm})
            # Land the lemma where the worker can see it (see `gl_anchor` above). An
            # in-env target: insert before the anchor. That re-evaluates the anchor
            # and everything after it (the edit cascade) with the new fact in scope;
            # the anchor keeps its live `worker_handle` (StdBlock._refresh_me_alone
            # never clears it) and re-runs its partial proof against the superset
            # state. Safe for a Have anchor (StdBlock reuses its children) and for a
            # Define anchor (a Define's obligation count comes from its equations,
            # not from preceding global facts, so re-exec stays on the child-reuse
            # branch and the worker's partial proof survives). A mid-cascade Isabelle
            # error would propagate out of insert_before — the same pre-existing
            # exposure the end-append path already carries.
            if gl_anchor is not None:
                # Insert against the held anchor OBJECT, not a re-resolved id
                # string. `insert_before(gl_anchor.id, …)` round-trips the id
                # through `locate_node`, which returns the FIRST sibling matching
                # that local_step — so were a duplicate id ever to exist it would
                # silently retarget the wrong node. We already hold the exact
                # anchor; use it. `insert_before`'s one side effect is setting
                # working_block to the anchor's parent (always the global env
                # here); replicate it so behavior is otherwise identical (the loop
                # saves/restores working_block across all iterations).
                session.working_block = global_env
                fill_outcome = await gl_anchor.insert_before_me([parsed])
            else:
                # Ask the global env for its real open slot rather than assuming
                # dense 1..N numbering. An earlier in-env request (above) may have
                # left a fractional global child via insert_before (e.g. `global.0A`),
                # so `len(sub_nodes)+1` could miss the actual append slot and make the
                # fill spuriously fail. `_id_of_openning_prf_to_fill` returns
                # `global.{incr(last local_step)}` — identical to `len+1` for dense
                # children, correct for fractional ones. (GlobalEnv never ends, so it
                # is always opening ⇒ never None.)
                slot = global_env._id_of_openning_prf_to_fill()
                assert slot is not None  # GlobalEnv is always opening
                fill_outcome = await session.root.fill(slot, [parsed])
            node = fill_outcome.committed[0] if fill_outcome.committed else None
            if node is None or node.status.status == EvaluationStatus.Status.FAILURE:
                # The statement itself is ill-formed / failed to open — no provable
                # node. Clean up a committed-but-failed node and relay the reason.
                reason = ""
                if node is not None:
                    r = node.status.reason
                    reason = r.reason if r is not None else ""
                    await session.root.delete([node.id])
                elif fill_outcome.failure is not None:
                    reason = getattr(fill_outcome.failure, "reason", "") or ""
                outcome_lines.append(_requested_lemma_failed_line(nm, reason))
                continue
            assert isinstance(node, Have)  # just filled a Have at the global slot
            # Defense-in-depth backstop: the Have's beginning op auto-FIXES any
            # undeclared free into for_any, so extra fixes beyond the agent's
            # `_input_for_any` mean the lemma was actually non-general (a predicate
            # false positive). Drop it and report the offending frees.
            if len(node.for_any) > len(node._input_for_any):
                extra = [n.unicode for n, _ in node.for_any[len(node._input_for_any):]]
                await session.root.delete([node.id])
                outcome_lines.append(_requested_lemma_undeclared_line(nm, extra))
                continue
            # Synchronously dispatch the headless prover on the fresh global Have.
            # The node is freshly created under GlobalEnv (disjoint from this
            # worker's target subtree), so it holds no handle and blocks nobody.
            assert node.worker_handle is None
            outcome = await _run_worker_on(session, node, "", [], headless=True)
            # A headless prover yields ONLY terminal outcomes (建议1 removes the
            # difficulty park; refute forks an autonomous adjudicator; a constraint
            # it raises on its OWN global Have is resolved IN-LOOP, never a park). A
            # park kind here would mean that invariant broke — fail loudly.
            assert outcome.kind in {"proved", "could_not_prove",
                                    "surrendered", "refute_accepted"}, (
                f"headless prover yielded non-terminal {outcome.kind!r}")
            if outcome.kind == "proved" and node.is_proof_finished():
                any_scope_change = True
                # Render the REAL (possibly constraint-amended) statement, not the
                # originally-submitted bare conclusion — a constraint the prover
                # raised on its own global Have may have made it conditional.
                outcome_lines.append(
                    f"Requested lemma `{nm}` has been proved and is now available: "
                    f"{node.conditional_fact_statement()}.")
            else:
                # PROVED ⟺ no unfinished nodes, so proved-but-unfinished cannot
                # happen; surrendered / could_not_prove / refute_accepted land here.
                reason = outcome.detail or outcome.reason or ""
                await session.root.delete([node.id])
                outcome_lines.append(_requested_lemma_failed_line(nm, reason))

        session.working_block = saved_working_block

        # --- CONSTRAINTS path: route each to the DISPATCHER (the agent that
        # dispatched this worker) for adjudication. The worker BLOCKS until the
        # dispatcher's verdict comes back through run_until_yield's in-loop
        # Interaction_ReviewConstraint (accept → amended in place / restructured;
        # reject → rejection message). ---
        constraint_feedback = ""
        if constraints:
            fut: asyncio.Future = asyncio.get_running_loop().create_future()
            handle._event_queue.put_nowait(
                WorkerRequestConstraints(detail=detail, constraints=constraints,
                                         response_future=fut))
            constraint_feedback = await fut
            any_scope_change = True

        # New facts may now sit in scope BEFORE this worker's target (auto-proved
        # general Haves) and/or its OWN target may have gained a premise (an
        # accepted constraint) — the premise cache assumed that set immutable.
        # Re-prefetch + refresh proof.yaml so the worker's view (and a later
        # `recall`) reflect them.
        if any_scope_change:
            await session._prefetch_worker_premises()
            session.refresh_YAML()

        # Worker's-own-target completion, mirroring `edit`'s finish handshake —
        # but UNCONDITIONAL (not gated on any_scope_change): a worker is dispatched
        # only on an UNfinished target, so an empty scope here means this work is
        # genuinely done and the worker should terminate, regardless of whether
        # THIS call is what closed it (a cascade/constraint can close the target on
        # the failed-lemma path, which sets no any_scope_change flag). The absolute
        # `proof_scope_unfinished_nodes()` empty-check is the worker-target signal —
        # a before/after delta is unnecessary because the only way the scope is
        # already empty at entry is a genuinely-finished target (e.g. a `True`-goal
        # block, which carries no obligation), on which terminating is still right.
        # `_write_newly_completed` separately reports newly-proved SUB-steps; it
        # structurally excludes the scope root (== the worker's target), so it never
        # carries the target itself — that is the empty-check's job.
        comp_buf = MyIO(StringIO())
        P._write_newly_completed(session, comp_buf)
        finished = False
        if not session.proof_scope_unfinished_nodes():
            comp_buf.write("Congratulations! All goals are proven.\n")
            finished = True
        completion = comp_buf.getvalue()

        # Assemble ONE synchronous response: per-lemma outcomes, then the
        # constraint verdict, then the completion announcement, then a notice of the
        # BEFORE-TARGET facts now newly in scope (auto-proved general lemmas;
        # appended at the end for LLM recency). The completion line is folded into
        # `parts` (before the "Nothing was processed." fallback) so a genuine
        # completion suppresses the fallback. The constraint-amend of the worker's
        # OWN target is NOT a before-target fact, so the notice does not cover it —
        # `constraint_feedback` states it.
        parts = list(outcome_lines)
        if gated_general_msg:
            parts.insert(0, gated_general_msg)
        if constraint_feedback:
            parts.append(constraint_feedback)
        if completion:
            parts.append(completion.rstrip("\n"))
        feedback = "\n".join(p for p in parts if p)
        notice = session.consume_new_scope_facts_notice(
            banner="The following facts are now available in your scope "
                   "(possibly modified from your original request)")
        if notice:
            feedback = (feedback + "\n\n" + notice) if feedback else notice
        if not feedback:
            feedback = "Nothing was processed."
        session.log_tool_response(_tn, feedback)
        # Whole worker-target scope discharged → terminate this worker now. The
        # driver's end-of-turn gate (proof_scope_unfinished_nodes empty → break →
        # WorkerDone) would catch it next turn regardless; this merely ends the
        # current turn immediately, exactly as `edit` does on `finished`.
        if finished:
            await session.interrupt()
        return (feedback, False)

    # Role_Major: no-argument hint — the planner formalizes the lemma itself.
    global_env = session.root.global_env
    # Real open slot — handles fractional global children a prior in-env
    # insert_before may have left (identical to `len+1` for dense children), so the
    # suggested `edit fill` target is one the planner can actually fill. GlobalEnv
    # never ends ⇒ always opening ⇒ never None. (Mirrors the worker-path slot fix.)
    target_step = global_env._id_of_openning_prf_to_fill()
    assert target_step is not None  # GlobalEnv is always opening
    if (session.is_major and not session.is_worker
            and session.gate_global_lemma_proofs):
        msg = ("You should declare the lemmas you need under `global` and dispatch a "
               f"sub-agent to prove each. Call command `edit` with action `fill` and "
               f"target step `{target_step}` to declare it, then call `subagent` on "
               f"that step to prove it.")
    else:
        msg = ("You should formalize and prove the lemmas you need directly under "
               f"`global`. Call command `edit` with action `fill` and target step "
               f"`{target_step}`.")
    session.log_tool_response(_tn, msg)
    return (msg, False)


async def _run_worker_on(session: Session, node: NonLeaf_Node,
                         suggestions: str, helpful_lemmas: list,
                         *, headless: bool = False) -> 'WorkerYield':
    """Fresh-dispatch core: attach a fresh ``WorkerHandle`` to ``node``, start the
    worker, and drive it to its first yield. Shared by the ``subagent`` tool
    (``headless=False``) and the ``request`` auto-prove-general path
    (``headless=True``). The CALLER owns every pre-check (blocker / orphan / depth)
    and the outcome ``match`` — this helper spans only the create→start→yield core.
    Cost settlement is NOT here: it fires in ``WorkerHandle._run``'s finally /
    ``aclose`` (idempotent), so every caller inherits exactly-once settlement."""
    handle = WorkerHandle(node, session)
    node.worker_handle = handle
    handle.start(suggestions, helpful_lemmas, headless=headless)
    try:
        return await handle.run_until_yield()
    except BaseException:
        # On cancellation/error BEFORE a terminal yield, tear the worker down so its
        # task is cancelled+awaited+settled rather than orphaned. This matters most
        # for the auto-prove-general path, whose node (a global Have under GlobalEnv)
        # lies OUTSIDE the dispatcher's own target subtree, so the dispatcher's normal
        # finally-sweep would not reap it. A normal return — including a PARK yield —
        # keeps the handle alive intentionally and is left untouched.
        await handle.aclose()
        raise


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
    until it yields control back to the dispatcher (a terminal outcome, a
    constraint-needs-restructure park, or a difficulty park from a system
    checkpoint). When difficulty is yielded, a non-forking
    ``Interaction_DifficultyEvaluation`` asks the dispatcher to continue or abandon
    (auto-cancel + comment)."""
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

    def _whole_goal_err() -> tuple[str, bool]:
        # Post-A2 the `target is None` case (no narrower named sub-goal above) and the
        # `target is psr` whole-goal case are semantically identical — there is no
        # narrower delegatable sub-goal, so delegating hands over the whole goal. One
        # message, emitted at both sites (`step_id`/`_tn` resolve at call time).
        return _err(
            f"Delegating step `{step_id}` would hand the sub-agent the whole "
            f"goal you are responsible for — there is no narrower sub-goal to "
            f"scope it to. You should call `{_tn}` on a specific subgoal like "
            f"Have, Suffices, Obtain etc, or prove the step `{step_id}` "
            f"yourself.")

    step_id = str(args.get("step_id", "")).strip()   # dispatcher-relative (for display)
    if not step_id:
        return _err("`step_id` is required — specify which step to delegate.")
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
        # No narrower delegatable sub-goal: `_nearest_goal_for_subagent` walked up to
        # the Root container / GlobalEnv without finding a named block or Define.
        # Post-A2 this is how a main agent dispatching a (bare) top-level goal lands
        # here — it IS the whole goal, just with no narrower unit (NOT "no goal").
        return _whole_goal_err()
    # A goal-transforming step (e.g. Contradiction, or a freshly-emptied slot)
    # has no delegatable sub-goal of its own, so `_nearest_goal_for_subagent`
    # redirects UP to its enclosing goal. When that lands on the WHOLE goal the
    # session is responsible for, delegating it would hand the sub-agent the
    # entire proof — reject rather than silently scope the worker to it.
    #   - worker: its own target IS `proof_scope_root` → `target is psr`.
    #   - main: `proof_scope_root` is the `Root` *container*. Post-A2 a top-level
    #     `GoalNode` redirects UP to `Root` (a GoalContainer → None), so it is caught
    #     by the `target is None` arm above. The `target.parent is psr` clause below
    #     is thus unreachable-by-construction (no delegatable node has `.parent is
    #     Root`), KEPT only as a defensive guard should a future node resolve to a
    #     direct child of `Root`.
    psr = session.proof_scope_root
    if target is psr or (not session.is_worker and target.parent is psr):
        return _whole_goal_err()
    if target is not node or from_slot:
        redirect_note = (f"Instead of step {step_id}, the sub-agent is working "
                         f"on step {session._display_id(target.id)}.\n")
    node = target
    # Invariant: _nearest_goal_for_subagent only ever returns a provable goal
    # block (Have / Obtain / Suffices / SetupRewriting / Define), all StdBlock
    # subtypes. (Post-A2 a bare GoalNode is never returned — obligation GoalNodes
    # redirect to the Define; case GoalNodes redirect to the enclosing named block.)
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
        if session._subagent_nesting_depth() >= session.SUBAGENT_NESTING_DEPTH:
            return _err(f"You are too deeply nested to delegate further (limit: "
                        f"{session.SUBAGENT_NESTING_DEPTH} levels of sub-agents). Prove this goal "
                        f"yourself, or simplify the plan.")
        outcome = await _run_worker_on(session, node, suggestions, helpful_lemmas)

    # The worker authored `outcome.detail` with absolute ids (it absolutized them
    # on emission); re-relativize for THIS dispatcher's view (identity for a
    # planner, dispatcher-scope-relative for a nested worker).
    detail_shown = session._postprocess_outbound_text(outcome.detail or "")
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
        case "constraint_needs_restructure":
            # The dispatcher accepted a constraint the sub-agent reported, but the
            # sub-agent's target cannot take it as a premise (Obtain/Suffices) — the
            # proof structure must be reworked. The sub-agent is parked; resuming via
            # `subagent` continues it, `cancel_subagent` drops it.
            accepted = f"\nAccepted condition(s): {detail_shown}" if outcome.detail else ""
            msg = (f"Sub-agent on step {session._display_id(node.id)} is suspended — "
                   f"its sub-goal needs the proof structure reworked.{accepted}\n"
                   f"Adjust the structure, then resume it via "
                   f"`{session.tool_name(TOOL_SUBAGENT)}`, or drop it via "
                   f"`{session.tool_name(TOOL_CLOSE_SUBAGENT)}`.")
        case _:  # "difficulty" — system checkpoint detected worker is struggling
            interaction = Interaction_DifficultyEvaluation(node, detail_shown)
            choice = await session.launch_interaction(interaction)
            if choice == 1:  # abandon
                await node.aclose_all_subagents()
                session.refresh_YAML()
                # Settle the "newly completed" delta HERE. Tearing down the
                # sub-agents can flip the scope's finishedness, but this abandon
                # path does not otherwise flush the delta (unlike `edit`/`delete`).
                # Flushing now attributes any genuine completion to THIS action and
                # marks it announced, so it cannot resurface — misattributed and
                # contradictory — inside a later unrelated edit response (e.g. a
                # failed `fill`). The abandoned node itself stays UNFINISHED (it
                # still has a pending goal), so it is naturally excluded from
                # `Session.newly_completed_topmost`; in the common case this
                # writes nothing.
                buf = MyIO(StringIO())
                buf.write("The sub-agent has been cancelled.\n")
                P._write_newly_completed(session, buf)
                msg = buf.getvalue().rstrip("\n")
            else:  # continue
                msg = (f"Noted. Resume the sub-agent by calling "
                       f"`{session.tool_name(TOOL_SUBAGENT)}` on step "
                       f"{session._display_id(node.id)} with suggestions.")
    # Append the whole-proof outline (mirrors the `edit`/`delete` tools) so the
    # planner sees the tree the worker just mutated without a `recall` round-trip.
    outline, finished = await P.subagent_overall(session.root, session)
    msg = redirect_note + msg + "\n" + outline
    if finished:
        await session.interrupt()

    session.log_tool_response(_tn, msg)
    return (msg, False)


async def _close_subagent_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """`cancel_subagent`: terminate a sub-agent YOU dispatched — cascading to any
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


_REFRESH_COOLDOWN_CALLS = 50

async def _refresh_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_REFRESH)
    session.log_tool_call(_tn, args)
    if session.fork_pending is not None:
        msg = "Refresh is not applicable in this context."
        session.log_tool_response(_tn, msg)
        return (msg, True)
    if session.quit_info is not None:
        msg = "Cannot refresh — another operation is pending."
        session.log_tool_response(_tn, msg)
        return (msg, True)
    calls_since = session.total_tool_calls - session._total_calls_at_last_refresh
    if calls_since < _REFRESH_COOLDOWN_CALLS:
        remaining = _REFRESH_COOLDOWN_CALLS - calls_since
        msg = (f"Cannot refresh yet — you must make at least {remaining} more "
               "tool calls first. Keep working: try a different approach.")
        session.log_tool_response(_tn, msg)
        return (msg, True)
    text = (args.get("briefing") or "").strip()
    if not text:
        msg = "The `briefing` field must not be empty."
        session.log_tool_response(_tn, msg)
        return (msg, True)
    session.quit_info = Refresh(briefing=text)
    await session.interrupt()
    msg = "Context refresh initiated."
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
                "use description and filters for discovery. "
                "If you fail to find a key lemma, increase `number`, retry with only `description`, "
                "and drop all other constraints like `term_patterns`, `exact_name`, and `name_contains`. "
                "Conversely, if a query returns too many irrelevant results, add the constraints to narrow down. "
                "Some trivial facts (e.g. `prime 7`) may not be found by `query` — declare them "
                "with `Have` and prove them with `Obvious`.",
               "schema": _cc_query_schema, "annotations": _RO},
    "recall": {"description": "Recall proof state from `proof.yaml`. Use only when you have lost track.", "schema": _cc_read_schema, "annotations": _RO},
    "recall_removed": {"description": "Browse proof steps that were archived before deletion.", "schema": _cc_recall_removed_schema, "annotations": _RO},
    "request": {"description": config.request_tool_description(),
                "schema": _cc_request_lemmas_schema, "annotations": _ACT},
    "report": {"description": "Report that the goal is unprovable (refute), or surrender when you have exhausted your strategies.",
                 "schema": _cc_report_schema, "annotations": _ACT},
    "answer_indexes": {"description": "Answer by selecting indexes from the presented options", "schema": _cc_answer_indexes_schema, "annotations": _ACT},
    "answer_index": {"description": "Answer by selecting a single index, or null to skip", "schema": _cc_answer_index_schema, "annotations": _ACT},
    "answer_indexes_or_name": {"description": "Answer by selecting indexes or providing an exact fact name", "schema": _cc_answer_indexes_or_name_schema, "annotations": _ACT},
    "answer_indexes_or_spec": {"description": "Answer by selecting indexes or providing an Isabelle proposition", "schema": _cc_answer_indexes_or_spec_schema, "annotations": _ACT},
    "answer_instantiate": {"description": "Answer by providing schematic-variable instantiations", "schema": _cc_answer_instantiate_schema, "annotations": _ACT},
    "answer_refutation": {"description": "Accept or reject a subagent's claim that the goal is unprovable", "schema": _cc_answer_refutation_schema, "annotations": _ACT},
    "answer_struggle_assessment": {"description": "Internal tool; you will be explicitly prompted when to use it.", "schema": _cc_answer_struggle_assessment_schema, "annotations": _ACT},
    "answer_missing_lemmas": {"description": "Internal tool; you will be explicitly prompted when to use it.", "schema": _cc_answer_missing_lemmas_schema, "annotations": _ACT},
    "answer_constraint_request": {"description": "Internal tool; you will be explicitly prompted when to use it.", "schema": _cc_answer_constraint_request_schema, "annotations": _ACT},
    "subagent": {"description": "Launch or resume a sub-agent to prove a goal or repair a proof in isolation. Call this when a goal is tedious and its proof would derail your main line of reasoning. Also call this to resume a suspended sub-agent." + config.subagent_cost_caution(), "schema": _cc_subagent_schema, "annotations": _ACT},
    "cancel_subagent": {"description": "Permanently cancel and delete a sub-agent you dispatched.", "schema": _cc_close_subagent_schema, "annotations": _ACT},
    "refresh": {"description": "Reset the conversation and start over (the proof tree is kept). "
                "Write a briefing for your future self in `briefing` — "
                "it becomes your only memory. Use when your edits keep failing.",
                "schema": _cc_refresh_schema, "annotations": _ACT},
    "write_memory": {"description":
                "Save an experience or a proof strategy so future proofs can reuse it. "
                "Note: what you save must generalize to a specific class of problems — "
                "not a single one-off goal.",
                "schema": _cc_write_memory_schema, "annotations": _MUT},
}


# Dispatch tools (subagent/cancel_subagent): available to dispatchers — the main
# agent AND workers — but hidden from interaction forks. Precompute the non-dispatcher
# (interaction-fork) view once at import time. The name `_PLANNER_ONLY_TOOLS` is kept
# for stability but now means "tools an interaction fork does not get".
_PLANNER_ONLY_TOOLS: frozenset[str] = frozenset({TOOL_SUBAGENT, TOOL_CLOSE_SUBAGENT})
_TOOL_SCHEMAS_WORKER: dict[str, dict[str, Any]] = {
    k: v for k, v in _TOOL_SCHEMAS.items() if k not in _PLANNER_ONLY_TOOLS}


def _tool_schemas_for(session: Session) -> dict[str, dict[str, Any]]:
    """Tool schemas advertised to ``session``. ``subagent`` / ``cancel_subagent`` are
    DISPATCH tools, shown to any agent that can delegate — the main agent AND workers
    (nested delegation) — but hidden from interaction forks (which never delegate) AND
    from a session already at the maximum nesting depth (a sub-sub-agent cannot
    delegate further). The gate is ``Session._can_offer_dispatch_tools``; ``_TOOL_SCHEMAS_WORKER``
    keeps its name but is simply the full set minus the dispatch tools."""
    base = _TOOL_SCHEMAS if session._can_offer_dispatch_tools() else _TOOL_SCHEMAS_WORKER
    # write_memory feature gate (AoA_enable_write_memory, tree-wide via Runtime):
    # when off, drop it from the advertised set entirely so it never appears in the
    # agent's available tools — for BOTH drivers (CC builds its Tool list from here;
    # APIDriver reads it via ToolExecutor.tool_schemas). Retrieval via `query` stays.
    if not session.enable_write_memory:
        base = {k: v for k, v in base.items() if k != TOOL_WRITE_MEMORY}
    # Apply the driver's per-tool schema rewrite (default identity). Drivers whose
    # model/client needs a different schema form override `transform_tool_schema` —
    # e.g. codex-cli DROPS `$ref`/`$defs` (collapsing `cc_edit.jsonc`'s operation
    # union to `{}`), so it swaps `edit` for the pre-flattened, `$ref`-free schema.
    # Rebuilt non-destructively so the shared `_TOOL_SCHEMAS` dicts stay intact.
    return {name: {**t, "schema": session.transform_tool_schema(name, t["schema"])}
            for name, t in base.items()}


def _experience_document_text(patterns: list[str], goal_description: str) -> str:
    """Text embedded for an experience memory (§8.1 of docs/EXPERIENCE_MEMORY.md):
    the goal patterns it targets plus the WHEN-to-use description. The
    how-to-prove payload is deliberately NOT embedded."""
    lines = ["This is an experience that aims to help prove goals of the following forms:"]
    lines += [f"- {p}" for p in patterns]
    lines.append("The experience should be used in the following situation:")
    lines.append(goal_description)
    return "\n".join(lines)


# --- write_memory corpus-dedup (adjacency mechanism, §3.1) -------------------
# Cosine threshold above which an existing experience is treated as a possible
# duplicate of a new one. Named constant (validate the embedding model's
# `normalize` so this sits on a [0,1] cosine — see EXPERIENCE_MEMORY docs).
_EXPERIENCE_DUP_THRESHOLD = 0.7
# How many nearest neighbours to fetch for the dedup check.
_EXPERIENCE_DUP_K = 5

# Tools that may be interleaved between a dedup rejection and the agent's
# confirming re-call without breaking "adjacency": read-only / interaction tools.
# MODULE-PRIVATE — this classification is the dedup mechanism's, and must NOT be
# pushed down into the generic Session.tool_call_log (modularity red line).
_ADJACENCY_SAFE: frozenset = frozenset(
    {TOOL_SEARCH, TOOL_READ, TOOL_RECALL_REMOVED}) | ANSWER_TOOLS


@dataclass
class DedupBlock:
    """A pending write_memory dedup rejection. `log_len` = the tool_call_log index
    just AFTER the rejecting write_memory call (len at rejection + 1, since that
    call's own entry is appended only on dispatch exit); the adjacency window is
    tool_call_log[log_len:]. `shown` = the matches displayed to the agent
    (name -> set of universal keys), authorizing an adjacent overwrite of those
    names."""
    log_len: int
    shown: 'dict[str, set[bytes]]' = field(default_factory=dict)


async def _experience_dup_search(store, doc_text: str, k: int) -> 'list[tuple[bytes, float]]':
    """Corpus-wide near-duplicate search over ALL experience keys (NOT the
    availability-scoped `_experience_hits`), so cross-theory duplicates are found.
    Returns raw (key, cosine) from `topk` — deliberately bypassing lookup()'s
    stage-1 boost and reranker."""
    from Isabelle_Semantic_Embedding.experience_index import Experience_Index
    from Isabelle_Semantic_Embedding import embedding_config as _ecfg
    keys = list(Experience_Index.all_keys())
    if not keys:
        return []
    qvec = (await store.emb_provider.embed(
        [doc_text], role="query",
        task_override=_ecfg.experience_task_description())).vectors[0]
    return await store.topk(qvec, keys, k)


def _render_dup_rejection(session: Session, name: str,
                          matches: 'list[tuple[bytes, Any]]') -> str:
    """[T3] The dedup rejection message: the overlapping experiences plus the
    three next-step options. Agent-facing wording is fixed (approved)."""
    wm = session.tool_name(TOOL_WRITE_MEMORY)
    n = len(matches)
    lines = [
        f"**The memory was NOT written.** {n} existing experience(s) may overlap "
        f"with yours (semantic relevance > {_EXPERIENCE_DUP_THRESHOLD:g}):",
        "",
    ]
    for _uk, rec in matches:
        lines.append(f"- experience `{rec.name}`:")
        if rec.interpretation:
            lines.append(f"    - When to use: {rec.interpretation}")
        try:
            pats = json.loads(rec.expr) if rec.expr else []
        except (json.JSONDecodeError, TypeError):
            pats = [rec.expr] if rec.expr else []
        if pats:
            # rec.expr stores patterns in ASCII (\<notin> ...); render Unicode.
            lines.append("    - Goal patterns:")
            lines += [f"        - {pretty_unicode(p)}" for p in pats]
        if rec.experience:
            lines.append(f"    - Experience: {rec.experience}")
        lines.append("")
    lines += [
        f"- If you are confident yours is genuinely **new** (not covered above), "
        f"call `{wm}` again with the same name (`{name}`) to save it.",
        f"- If one of the above **is** the right memory but is not comprehensive "
        f"enough, call `{wm}` again using **that memory's exact `name`** to "
        f"overwrite and improve it.",
        "- Otherwise, don't save this one.",
    ]
    return "\n".join(lines)


async def _write_memory_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """`write_memory`: save/refresh a reusable proof experience (a strategy for a
    general class of goals; see docs/EXPERIENCE_MEMORY.md).

    Identity is the `name`. Re-writing the same name THIS AoA run overwrites the
    prior record: its old universal key is deleted from the semantic DB, the vector
    store, and the inverted index before the new record is written. A name not in
    ``runtime.created_memories`` is a fresh create that never scans for, nor touches,
    a pre-existing memory from a prior run. The universal key is content-addressed
    (theory-constituent prefix + xxhash of name/patterns/description/experience), so
    an identical re-write is absorbed idempotently."""
    import xxhash
    from Isabelle_RPC_Host.universal_key import xor_theory_prefix, EntityKind
    from Isabelle_Semantic_Embedding.semantics import Semantic_DB, SemanticRecord
    from Isabelle_Semantic_Embedding.experience_index import Experience_Index

    _tn = session.tool_name(TOOL_WRITE_MEMORY)
    session.log_tool_call(_tn, args)

    name = args.get("name")
    patterns = args.get("goal_patterns")
    desc = args.get("goal_description")
    experience = args.get("experience")
    if not isinstance(name, str) or not name.strip():
        return ("`name` must be a non-empty string.", True)
    if (not isinstance(patterns, list) or not patterns
            or not all(isinstance(p, str) and p.strip() for p in patterns)):
        return ("`goal_patterns` must be a non-empty list of Isabelle term pattern strings.", True)
    if not isinstance(desc, str) or not desc.strip():
        return ("`goal_description` must be a non-empty string.", True)
    if not isinstance(experience, str) or not experience.strip():
        return ("`experience` must be a non-empty string.", True)

    # goal_patterns arrive as agent Unicode; model them as IsaTerm so the
    # Unicode<->ASCII boundary is explicit and cannot be skipped. `.ascii` (e.g.
    # `\<notin>`) is the canonical form fed to Isabelle — the ML constituents
    # callback AND the stored rec.expr (which retrieval re-parses). `.unicode` is
    # used only for embedding (semantic form) and agent-facing display. Passing
    # raw Unicode to Isabelle's inner lexer silently fails to parse (∉ ℚ ¬ ...),
    # dropping the pattern and orphaning the memory from the constituent index.
    pats = [IsaTerm.from_agent(p) for p in patterns]
    pats_ascii = [p.ascii for p in pats]
    pats_uni = [p.unicode for p in pats]

    ml_state = session.retrieval_state()
    conn = ml_state.connection

    # 1. minimal-antichain constituent theories of the patterns (ML side).
    try:
        consts_raw = await conn.callback(
            "Experience.constituents", (ml_state.name, pats_ascii))
    except IsabelleError as e:
        # The ML side self-describes (per-pattern "Could not parse pattern ..."),
        # so return it verbatim rather than wrapping in a generic prefix.
        return (e.errors[0] if e.errors else str(e), True)
    constituents = [((n if isinstance(n, str) else n.decode("utf-8")), bytes(h))
                    for n, h in consts_raw]
    # An empty `constituents` list is INTENTIONAL: a valid pattern that resolves to
    # no library theory (e.g. `?P`) becomes a GLOBAL experience — Experience_Index
    # registers it under the _GLOBAL bucket (always a retrieval/dedup candidate),
    # and xor_theory_prefix([]) gives the all-zero key prefix. (Genuinely malformed
    # patterns are rejected upstream by the Experience.constituents callback, which
    # errors on any pattern unparseable even after fallbacks -> `except IsabelleError`.)

    # 2. assemble the content-addressed universal key.
    prefix = xor_theory_prefix([h for _, h in constituents])
    def _norm(s: str) -> str:
        return " ".join(s.split())
    payload = "\x00".join([_norm(name), *(_norm(p) for p in pats_ascii),
                           _norm(desc), _norm(experience)]).encode("utf-8")
    hash15 = xxhash.xxh128(payload).digest()[:15]
    key = prefix + bytes([int(EntityKind.EXPERIENCE)]) + hash15

    # 3. adjacency handshake (§3.1). "adjacent" = a dedup rejection is pending and
    # only read-only / interaction tools have been called since it was raised.
    created = session.runtime.created_memories
    store = await conn.semantic_vector_store()
    block = session.dedup_block
    adjacent = (block is not None and
                all(t in _ADJACENCY_SAFE
                    for t in session.tool_call_log[block.log_len:]))

    def _delete_uk(uk: bytes) -> None:
        old_rec = Semantic_DB[uk]
        Semantic_DB.delete(uk)
        store.delete(uk)
        old_consts = old_rec.theory_constituents if old_rec is not None else None
        if old_consts:
            Experience_Index.remove(uk, [h for _, h in old_consts])
        else:
            Experience_Index.remove_scanning(uk)

    async def _persist(verb: str) -> tuple[str, bool]:
        # Embed FIRST: it is the only fallible/remote step. If it raises, nothing
        # is written to Semantic_DB / Experience_Index (and, on the overwrite
        # path below, the prior memory has not been deleted yet). A written-but-
        # unreferenced vector is harmless; a record/index entry without a vector
        # would be an invisible orphan (retrieval + dedup both need the vector).
        await store.embed([(key, _experience_document_text(pats_uni, desc))])
        Semantic_DB[key] = SemanticRecord(
            EntityKind.EXPERIENCE, name, json.dumps(pats_ascii), desc,
            None, constituents, experience)
        Experience_Index.add(key, [h for _, h in constituents])
        created[name] = key
        session.written_names.append(name)
        session.dedup_block = None
        return (f"{verb} experience `{name}`.", False)

    # Case 1: overwrite an *authorized* same-name memory — this run's own creation
    # (any time), or one shown to the agent during an adjacent dedup rejection.
    # A same-name entry that was NEVER shown is never silently removed.
    targets: set[bytes] = set()
    if name in created:
        targets.add(created[name])
    if adjacent and block is not None:
        targets |= block.shown.get(name, set())
    if targets:
        # Persist the new record durably FIRST, then delete the old one(s): a
        # transient embed failure in _persist must not have already destroyed the
        # prior good memory (concern #4). _delete_uk of the same `key` is guarded.
        result = await _persist("Updated")
        for uk in targets:
            if uk != key:            # never delete the very key we just wrote
                _delete_uk(uk)
        return result

    # Case 2: an adjacent re-call is the agent confirming "not a duplicate" —
    # accept it, even if the content changed since the rejection. One block
    # authorizes exactly one write.
    if adjacent:
        return await _persist("Saved")

    # 4. fresh corpus-wide dedup search (non-adjacent). NOT availability-scoped:
    # Experience_Index.all_keys() so cross-theory duplicates are caught.
    doc_text = _experience_document_text(pats_uni, desc)
    hits = await _experience_dup_search(store, doc_text, _EXPERIENCE_DUP_K)
    matches: list[tuple[bytes, Any]] = []
    for uk, score in hits:
        if uk == key or score <= _EXPERIENCE_DUP_THRESHOLD:
            continue
        rec = Semantic_DB[uk]
        if rec is not None and rec.kind == EntityKind.EXPERIENCE:
            matches.append((uk, rec))
    if matches:
        shown: dict[str, set[bytes]] = {}
        for uk, rec in matches:
            shown.setdefault(rec.name, set()).add(uk)
        # +1 reserves the slot this very write_memory call will occupy: its own
        # tool_call_log entry is appended only on dispatch exit (see execute's
        # `finally`), so at this point len() does not yet count it. Without the +1
        # the rejecting call itself would fall inside the next call's adjacency
        # window and (being write_memory, not _ADJACENCY_SAFE) force adjacent=False.
        session.dedup_block = DedupBlock(log_len=len(session.tool_call_log) + 1, shown=shown)
        return (_render_dup_rejection(session, name, matches), False)

    # No near-duplicate — write it.
    return await _persist("Saved")


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
        self._subagent_lock = asyncio.Lock()
        self._last_mutate_fail_time: float = 0.0
        self._channel = InteractionChannel()
        self._suspended_task: asyncio.Task | None = None
        session._channel = self._channel

    # ------------------------------------------------------------------
    # Channel helpers
    # ------------------------------------------------------------------

    async def _race_outbox(self, task: asyncio.Task) -> executor_msg:
        """Await the next outbox message, or propagate task exception.

        Uses ``asyncio.wait`` to race ``outbox.get()`` against the task.
        If the task completes (normally or with an exception) before a
        message appears, the task's result/exception is propagated.
        ``outbox_fut`` is always cancelled on exit if not consumed.
        """
        outbox_fut = asyncio.ensure_future(self._channel.outbox.get())
        try:
            done, _ = await asyncio.wait(
                [outbox_fut, task], return_when=asyncio.FIRST_COMPLETED)
            if task in done and not outbox_fut.done():
                outbox_fut.cancel()
                task.result()
            return outbox_fut.result()
        finally:
            if not outbox_fut.done():
                outbox_fut.cancel()

    async def _run_tool_via_channel(
            self, coro, session: Session, is_edit: bool,
            is_batch: bool = False) -> tuple[str, bool]:
        """Start *coro* as a Task, communicate via the channel.

        If the tool logic completes without triggering a non-forking
        interaction, the result is returned directly. If an interaction
        fires (``InteractionPrompt`` on the outbox), the task is
        suspended and the prompt returned to the agent.
        """
        if self._suspended_task is not None:
            return ("An operation is in progress. "
                    "Answer the pending interaction question first.", True)

        # Adopted by the session so a task suspended on a non-forking
        # interaction is cancelled at session close instead of dangling.
        task = session.adopt_task(asyncio.create_task(coro))
        try:
            msg = await self._race_outbox(task)
        except BaseException:
            task.cancel()
            with contextlib.suppress(BaseException):
                await task
            raise

        match msg:
            case EditResult(text, ie):
                await task
                if ie and is_edit and not is_batch:
                    self._last_mutate_fail_time = time()
                elif ie and not is_edit:
                    self._last_mutate_fail_time = time()
                session.last_proof_op_time = time()
                return (text, ie)
            case InteractionPrompt():
                self._suspended_task = task
                return (msg.text, False)
            case InteractionError(text):
                # Protocol invariant violation. An InteractionError is emitted
                # ONLY in reply to a submitted answer (model.py
                # _inline_interaction, after channel.inbox.get()). This is the
                # FIRST handshake call: nothing has been put on the inbox yet
                # (that happens only in _handle_nf_answer), so reaching here
                # means the tool task signalled a bad-answer error before any
                # question was ever asked. The task is now parked on the next
                # inbox.get(); cancel it so it does not dangle, then fail loud.
                task.cancel()
                with contextlib.suppress(BaseException):
                    await task
                raise InternalError(
                    f"InteractionError on first channel handshake "
                    f"(is_edit={is_edit}, is_batch={is_batch}): {text!r}. "
                    f"An InteractionError is only valid as a reply to a "
                    f"submitted answer, but none was submitted on this path — "
                    f"the tool task violated the channel protocol.")
            case _:
                raise InternalError(f"Unexpected channel message: {msg!r}")

    async def _handle_nf_answer(
            self, session: Session, tool_name: str,
            arguments: dict) -> tuple[str, bool]:
        """Handle an answer tool call for a suspended non-forking edit/delete."""
        _tn = session.tool_name(tool_name)
        session.log_tool_call(_tn, arguments)
        task = self._suspended_task
        assert task is not None

        pi = session.pending_interaction
        if pi is None:
            error_msg = f"No interaction pending (internal state error)."
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        if tool_name != pi.answer_tool_name:
            expected = session.tool_name(pi.answer_tool_name)
            error_msg = f"Wrong answer tool. Use `{expected}` to answer the current question."
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)

        payload = _parse_answer_payload(tool_name, arguments)
        if isinstance(payload, str):
            session.log_tool_response(_tn, f"ERROR: {payload}")
            return (payload, True)

        await self._channel.inbox.put(payload)

        try:
            msg = await self._race_outbox(task)
        except BaseException:
            self._suspended_task = None
            raise

        match msg:
            case InteractionError(text):
                session.log_tool_response(_tn, f"BAD ANSWER: {text}")
                return (text, True)
            case InteractionPrompt(interaction, text):
                session.log_tool_response(_tn, text)
                return (text, False)
            case EditResult(text, ie):
                await task
                self._suspended_task = None
                session.last_proof_op_time = time()
                session.log_tool_response(_tn, text)
                return (text, ie)
            case _:
                raise InternalError(f"Unexpected channel message: {msg!r}")

    # ------------------------------------------------------------------
    # Main dispatch
    # ------------------------------------------------------------------

    async def execute(self, name: str, arguments: dict) -> tuple[str, bool]:
        """Execute a tool call. Returns (result_text, is_error).

        Handles permission checks, cooldown logic, and the search hint.
        Edit and delete run as channel-connected Tasks (supporting
        non-forking interactions); other tools run inline.
        """
        session = self._session
        _session_var.set(session)

        # Hard budget enforcement at per-tool-call granularity, BEFORE the
        # permission check (so even a would-be-denied call halts immediately).
        # check_budget() reads the runtime-global wall clock + tool-call count
        # (correct on workers/forks too) and, when exhausted, sets
        # quit_info=ResourceExhausted (idempotent). interrupt() then stops the
        # in-flight agent: the API drivers set _interrupted, so the loop breaks
        # at the next boundary. Without this a single overlong tool batch could
        # overshoot the deadline (check_budget otherwise runs only between turns).
        if session.check_budget():
            await session.interrupt()
            return ("Budget exhausted (time/tool-call limit reached). Halting.", True)

        perm_error = _check_tool_permission(session, name)
        if perm_error:
            return (perm_error, True)

        # Generic per-session tool-call log (abstract id). Single dispatch
        # chokepoint for BOTH drivers: the ClaudeCode MCP `call_tool` and the
        # APIDriver both route built-in proof tools through here. Drives the
        # write_memory dedup adjacency check (see _ADJACENCY_SAFE). The append is
        # deferred to the `finally` below (on dispatch exit): a tool must NOT see
        # its own entry while its logic runs — write_memory computing adjacency
        # would otherwise always find itself in the window. The rejection path
        # compensates with block.log_len = len + 1.
        is_error = False
        try:
            match name:
                case "edit":
                    ops = arguments.get("proof_operations") if isinstance(arguments, dict) else None
                    is_batch = isinstance(ops, list) and len(ops) > 1
                    if not is_batch and time() - self._last_mutate_fail_time < 0.7:
                        result, is_error = self._BATCH_CANCEL_MSG, True
                        session.last_proof_op_time = time()
                    else:
                        async def _run_edit():
                            r, e = await _edit_tool_logic(session, arguments)
                            await self._channel.outbox.put(EditResult(r, e))
                        result, is_error = await self._run_tool_via_channel(
                            _run_edit(), session, is_edit=True, is_batch=is_batch)
                case "delete":
                    if time() - self._last_mutate_fail_time < 0.7:
                        result, is_error = self._BATCH_CANCEL_MSG, True
                        session.last_proof_op_time = time()
                    else:
                        async def _run_delete():
                            r, e = await _delete_tool_logic(session, arguments)
                            await self._channel.outbox.put(EditResult(r, e))
                        result, is_error = await self._run_tool_via_channel(
                            _run_delete(), session, is_edit=False)
                case n if n in ANSWER_TOOLS:
                    if self._suspended_task is not None:
                        result, is_error = await self._handle_nf_answer(
                            session, n, arguments)
                    else:
                        result, is_error = await _answer_tool_dispatch(
                            session, n, arguments)
                case "query":
                    result, is_error = await _query_tool_logic(session, arguments)
                    # Missing-lemma survey checkpoint: every N successful
                    # `query` TOOL CALLS (not batched sub-queries; errored
                    # calls deliberately don't count — they carry no retrieval
                    # signal; user-confirmed 2026-06-11) per session,
                    # fork a survey asking what the agent searched for but
                    # could not find. Counts planner and worker sessions;
                    # interaction forks are excluded (run_missing_lemma_survey
                    # also guards, this just avoids counting them).
                    if (not is_error
                            and not session.is_interaction
                            and session._missing_lemma_survey_interval > 0):
                        session._query_calls_since_survey += 1
                        if (session._query_calls_since_survey
                                >= session._missing_lemma_survey_interval):
                            await session.run_missing_lemma_survey(
                                "query_interval")
                case "recall":
                    result, is_error = await _read_tool_logic(session, arguments)
                case "recall_removed":
                    result, is_error = await _recall_removed_tool_logic(session, arguments)
                case "request":
                    # Channel-route like `subagent` (it likewise dispatches a worker):
                    # run as a Task so a non-forking interaction raised mid-call (a
                    # constraint adjudication, or a headless prover's own constraint)
                    # can surface to this agent as a suspend-and-answer, instead of
                    # deadlocking on an un-pumped channel. Under `_subagent_lock` to
                    # keep worker dispatch serialized with `subagent`.
                    async with self._subagent_lock:
                        async def _run_request():
                            r, e = await _request_tool_logic(session, arguments)
                            await self._channel.outbox.put(EditResult(r, e))
                        result, is_error = await self._run_tool_via_channel(
                            _run_request(), session, is_edit=False)
                    session.last_proof_op_time = time()
                case "report":
                    result, is_error = await _report_tool_logic(session, arguments)
                case "subagent":
                    async with self._subagent_lock:
                        async def _run_subagent():
                            r, e = await _subagent_tool_logic(session, arguments)
                            await self._channel.outbox.put(EditResult(r, e))
                        result, is_error = await self._run_tool_via_channel(
                            _run_subagent(), session, is_edit=False)
                    session.last_proof_op_time = time()
                case "cancel_subagent":
                    if self._suspended_task is not None:
                        result = "Answer the pending interaction question first."
                        is_error = True
                    else:
                        async with self._subagent_lock:
                            result, is_error = await _close_subagent_tool_logic(session, arguments)
                    session.last_proof_op_time = time()
                case "refresh":
                    result, is_error = await _refresh_tool_logic(session, arguments)
                case "write_memory":
                    result, is_error = await _write_memory_tool_logic(session, arguments)
                case _:
                    return (f"Unknown tool: {name}", True)
        except LMUnreachable as e:
            # The LM backend (e.g. the openai-oauth proxy, or its ChatGPT
            # credentials) is unreachable. This can surface here when a fork
            # (interaction sub-agent) makes the failing model call. Convert it to
            # a clean terminal give-up via quit_info — the main loop sees
            # quit_info and stops — instead of letting it fall to the
            # `except Exception: sys.exit(1)` below, which would kill the whole
            # (single-process) host. The main agent loop catches LMUnreachable
            # directly (see driver_api._api_loop).
            session.quit_info = ResourceUnavailable(detail=str(e))
            session.log_tool_response(session.tool_name(name), f"LM UNREACHABLE: {e}")
            return (str(e), True)
        except (ConnectionError, EOFError):
            raise asyncio.CancelledError("connection lost")
        except Exception as e:
            session.log_tool_response(
                session.tool_name(name),
                f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
            sys.exit(1)
        finally:
            # Append AFTER dispatch (see the note at the top of execute): the
            # in-flight call must not be part of its own adjacency window. Runs on
            # every exit path (normal return, LMUnreachable return, re-raise,
            # sys.exit), matching the prior always-append-once-dispatched behaviour.
            session.tool_call_log.append(name)

        if name == "query" and not is_error:
            if time() - session.last_proof_op_time >= self._SEARCH_HINT_THRESHOLD:
                result += self._SEARCH_HINT

        return (result, is_error)

    def tool_schemas(self) -> dict[str, dict[str, Any]]:
        """Return {name: {"description": ..., "schema": ...}} for the tools
        advertised to this session's role (``subagent``/``cancel_subagent`` are
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

    # Build tool list: built-in (role-scoped — `subagent`/`cancel_subagent` go to
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
                session.seen_manual_note = False
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
