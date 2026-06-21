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
    Parse_Op_List, Interaction_BadAnswer,
    AnswerIndexes, AnswerIndex, AnswerIndexesOrName, AnswerIndexesOrSpec,
    AnswerInstantiate, AnswerRefutation, AnswerStruggleAssessment,
    AnswerMissingLemmas,
    TOOL_EDIT, TOOL_DELETE, TOOL_COMMENT, TOOL_READ, TOOL_RECALL_REMOVED,
    TOOL_REQUEST_LEMMAS, TOOL_REPORT, TOOL_SUBAGENT, TOOL_CLOSE_SUBAGENT,
    DeletedEntry, CommentOutcome,
    TOOL_ANSWER_INDEXES, TOOL_ANSWER_INDEX, TOOL_ANSWER_INDEXES_OR_NAME,
    TOOL_ANSWER_INDEXES_OR_SPEC, TOOL_ANSWER_INSTANTIATE,
    TOOL_ANSWER_REFUTATION, TOOL_ANSWER_STRUGGLE_ASSESSMENT,
    Interaction_StruggleCheckpoint, Interaction_DifficultyEvaluation,
    Interaction_ConfirmLargeDelete,
    LARGE_DELETE_PROVED_THRESHOLD, LARGE_DELETE_TOTAL_THRESHOLD,
    InteractionPrompt, InteractionError, EditResult, InteractionChannel,
    ANSWER_TOOLS,
    ALL_PROOF_TOOLS,
    Role_Worker,
    Surrender, Refute, Refresh,
    TOOL_REFRESH,
    print_indent, print_goal, MyIO,
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
_cc_answer_struggle_assessment_schema = _load_schema("cc_answer_struggle_assessment.jsonc")
_cc_answer_missing_lemmas_schema = _load_schema("cc_answer_missing_lemmas.jsonc")
_cc_subagent_schema = _load_schema("cc_subagent.jsonc")
_cc_close_subagent_schema = _load_schema("cc_cancel_subagent.jsonc")
_cc_recall_removed_schema = _load_schema("cc_recall_removed.jsonc")
_cc_refresh_schema = _load_schema("cc_refresh.jsonc")
_cc_comment_schema = _load_schema("cc_comment.jsonc")



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

_MUTATION_TOOLS = frozenset({
    TOOL_EDIT, TOOL_DELETE, TOOL_COMMENT, TOOL_SUBAGENT, TOOL_CLOSE_SUBAGENT,
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
                             "elsewhere, use `request_lemmas`.")
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
                comment_available = not any(
                    isinstance(n, (Root, GlobalEnv, GoalNode)) for n in nodes)
                choice = await session.launch_interaction(
                    Interaction_ConfirmLargeDelete(entries, comment_available))
                if choice == "cancel":
                    response = P.delete_cancelled_message()
                    session.log_tool_response(_tn, response)
                    return (response, False)
                if choice == "comment":
                    outcome = await session.root.comment(abs_steps)
                    session.refresh_YAML()
                    response, finished = await P.comment_message(
                        outcome, "comment", session.root, session)
                    if finished:
                        await session.interrupt()
                    session.log_tool_response(_tn, response)
                    session.log_proof_tree_snapshot("after_comment")
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


async def _comment_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    _tn = session.tool_name(TOOL_COMMENT)
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
        action = args.get("action")
        if action not in ("comment", "uncomment"):
            error_msg = f"Invalid action: {action!r}. Must be 'comment' or 'uncomment'."
            session.log_tool_response(_tn, f"ERROR: {error_msg}")
            return (error_msg, True)
        session.age += 1
        steps = [str(s) for s in target_steps]
        abs_steps = [session._resolve_display_id(s) for s in steps]
        for sid in abs_steps:
            verdict, _ = session._edit_verdict(sid, "amend")
            if verdict is EditVerdict.OUT_OF_SCOPE:
                error_msg = ("This step is outside the goal you were asked to prove — you may "
                             "only edit within your own sub-proof. If you need a fact established "
                             "elsewhere, use `request_lemmas`.")
                session.log_tool_response(_tn, f"ERROR: {error_msg}")
                return (error_msg, True)
        if action == "comment":
            outcome = await session.root.comment(abs_steps)
        else:
            outcome = await session.root.uncomment(abs_steps)
        session.refresh_YAML()
        response, finished = await P.comment_message(
            outcome, action, session.root, session)
        if finished:
            await session.interrupt()
        session.log_tool_response(_tn, response)
        session.log_proof_tree_snapshot(f"after_{action}")
        return (response, False)
    except AoA_Error as e:
        error_msg = str(e)
        session.log_tool_response(_tn, f"ERROR: {error_msg}")
        return (error_msg, True)
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
    """§G3 line: a requested lemma's free variables are not declared in for_any."""
    vlist = ", ".join(blocking)
    return (f"Requested lemma `{name}` contains free variable(s) `{vlist}` that "
            f"are not declared in `for_any`.")


async def _request_lemmas_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """Dual-role `request_lemmas`.

    - **Worker (sub-agent)**: a worker→planner channel. The worker submits a
      loose wish-list and BLOCKS until the planning agent reviews it, authors +
      proves any accepted helper lemmas into the global env, and hands back a
      feedback string. The worker then KEEPS WORKING (non-terminal, like a
      rejected refutation), now with the proven lemmas in scope.
    - **Planning agent**: a no-argument hint pointing it at the right action —
      formalize and prove the missing lemma under `global` via `edit`/`fill`, or,
      when the global-lemma gate is on, declare it under `global` and dispatch a
      sub-agent to prove it.
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
        # validate the wish-list shape in Python (each item {name, statement},
        # statement a LongStatement) before the generality check reads it.
        try:
            suggested_lemmas = validate(
                list[SuggestedLemma], suggested_lemmas, "suggested_lemmas")
        except ArgumentError as e:
            msg = str(e)
            session.log_tool_response(_tn, f"ERROR: {msg}")
            return (msg, True)
        # Mirror EVERY requested lemma (general + non-general) into
        # missing_lemmas.yaml — a worker asking for a lemma is a free signal for the
        # external import-expansion loop. Keep the FLAT {name, english,
        # isabelle_statement} shape that loop's watcher reads
        # (tools/missing_lemma_loop/watcher.py), deriving the two strings from the
        # LongStatement; do NOT leak the nested shape into that file.
        session.log_missing_lemmas(
            "request_lemmas",
            [{"name": l["name"],
              "english": l["statement"].get("english", ""),
              "isabelle_statement": l["statement"].get("conclusion", ""),
              "detail": detail}
             for l in suggested_lemmas])

        # Classify each lemma by generality against the GLOBAL fill-slot state
        # (prior global declarations visible; worker-local fixes excluded).
        global_env = session.root.global_env
        slot_state = global_env._resulting_state_of_all_children()
        general_items: list = []
        nongeneral_items: list = []
        blocking_by_name: dict[str, list[str]] = {}
        for lem in suggested_lemmas:
            ok, blocking = await _lemma_statement_is_general(
                slot_state, lem["statement"])
            if ok:
                general_items.append(lem)
            else:
                nongeneral_items.append(lem)
                blocking_by_name[lem["name"]] = blocking

        # 建议2 — a headless prover's request_lemmas is GENERAL-ONLY: it has no
        # planner to author non-general lemmas and must never park. Reject upfront
        # (process nothing) so it resubmits with every free variable declared; the
        # already-general items are then auto-proved cleanly on the retry, with no
        # duplicate global Haves.
        if session.role.headless and nongeneral_items:  # type: ignore[union-attr]
            lines = [_requested_lemma_undeclared_line(lem["name"],
                                                      blocking_by_name[lem["name"]])
                     for lem in nongeneral_items if blocking_by_name.get(lem["name"])]
            # Items non-general only because their term does not parse carry no
            # variable names; relay that plainly so the message is never empty.
            for nm in (lem["name"] for lem in nongeneral_items
                       if not blocking_by_name.get(lem["name"])):
                lines.append(f"Requested lemma `{nm}` could not be parsed as an "
                             f"Isabelle term.")
            msg = "\n".join(lines) + "\nYou must declare every free variable in `for_any`."
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
        for lem in general_items:
            nm = lem["name"]
            stmt = lem["statement"]
            slot = f"{global_env.id}.{len(global_env.sub_nodes) + 1}"
            parsed = Have.gen_single({
                "thought": detail or "requested helper lemma",
                "statement": stmt,
                "name": nm})
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
            # false positive). Drop it and report the offending frees (§G3).
            if len(node.for_any) > len(node._input_for_any):
                extra = [n.unicode for n, _ in node.for_any[len(node._input_for_any):]]
                await session.root.delete([node.id])
                outcome_lines.append(
                    _requested_lemma_undeclared_line(nm, extra)
                    + " You must declare every free variable in `for_any`.")
                continue
            # Synchronously dispatch the headless prover on the fresh global Have.
            # The node is freshly created under GlobalEnv (disjoint from this
            # worker's target subtree), so it holds no handle and blocks nobody.
            assert node.worker_handle is None
            outcome = await _run_worker_on(session, node, "", [], headless=True)
            # A headless prover yields ONLY terminal outcomes (建议1/建议2 remove the
            # difficulty/lemmas park arms; refute forks an autonomous adjudicator). A
            # park kind here would mean that invariant broke — fail loudly instead of
            # silently relaying a still-parked prover as a generic failure.
            assert outcome.kind in {"proved", "could_not_prove",
                                    "surrendered", "refute_accepted"}, (
                f"headless prover yielded non-terminal {outcome.kind!r}")
            if outcome.kind == "proved" and node.is_proof_finished():
                any_scope_change = True
                outcome_lines.append(
                    f"Requested lemma `{nm}` has been proved and is now available: "
                    f"{stmt['conclusion']}.")
            else:
                # PROVED ⟺ no unfinished nodes, so proved-but-unfinished cannot
                # happen; surrendered / could_not_prove / refute_accepted land here.
                reason = outcome.detail or outcome.reason or ""
                await session.root.delete([node.id])
                outcome_lines.append(_requested_lemma_failed_line(nm, reason))

        session.working_block = saved_working_block

        # --- NON-GENERAL path (normal worker only; headless rejected above): park
        # for the planner to author + prove, exactly as before, but only the
        # non-general subset. ---
        planner_feedback = ""
        if nongeneral_items:
            fut: asyncio.Future = asyncio.get_running_loop().create_future()
            handle._event_queue.put_nowait(
                WorkerRequestLemmas(detail=detail, lemmas=nongeneral_items,
                                    response_future=fut))
            planner_feedback = await fut
            any_scope_change = True

        # New facts may now sit in scope BEFORE this worker's target (auto-proved
        # general Haves and/or planner-authored lemmas) — the premise cache assumed
        # that set immutable. Re-prefetch + refresh proof.yaml so the worker's view
        # (and a later `recall`) reflect them.
        if any_scope_change:
            await session._prefetch_worker_premises()
            session.refresh_YAML()

        # Assemble ONE synchronous response: per-lemma outcomes, then the planner's
        # guidance for any non-general subset, then a notice of the facts now newly
        # in scope (appended at the end for LLM recency/salience).
        parts = list(outcome_lines)
        if planner_feedback:
            parts.append(planner_feedback)
        feedback = "\n".join(p for p in parts if p)
        notice = session.consume_new_scope_facts_notice()
        if notice:
            feedback = (feedback + "\n\n" + notice) if feedback else notice
        if not feedback:
            feedback = "No lemmas were processed."
        session.log_tool_response(_tn, feedback)
        return (feedback, False)

    # Role_Major: no-argument hint — the planner formalizes the lemma itself.
    global_env = session.root.global_env
    target_step = f"{global_env.id}.{len(global_env.sub_nodes) + 1}"
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
    (``headless=False``) and the request_lemmas auto-prove-general path
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
    request_lemmas park, or a difficulty park from a system checkpoint).
    When difficulty is yielded, a non-forking ``Interaction_DifficultyEvaluation``
    asks the dispatcher to continue or abandon (auto-cancel + comment)."""
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
    # block (Have / Obtain / Suffices / SetupRewriting / GoalNode), all StdBlock subtypes.
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
        case "lemmas":  # worker parked requesting helper lemmas (non-general subset)
            buf = StringIO()
            for lem in (outcome.lemmas or []):
                lstmt = lem.get("statement") or {}
                concl = (lstmt.get("conclusion") or "").replace("\n", " ")
                buf.write(f"- {lem.get('name', '')}: {concl}\n")
                print_indent(2, buf)
                buf.write(f"{lstmt.get('english', '')}\n")
            formulas = buf.getvalue()
            msg = (f"The sub-agent requests helper lemmas to continue:\n"
                   f"{formulas}\n"
                   f"{detail_shown}\n"
                   f"Consider providing these lemmas, then call `subagent` on step "
                   f"{session._display_id(node.id)} again to resume the sub-agent, listing the lemmas you "
                   f"built in `helpful_lemmas` and describing them in `suggestions` by name "
                   f"or statement, NEVER by step id (the sub-agent cannot see your step numbering).")
        case _:  # "difficulty" — system checkpoint detected worker is struggling
            interaction = Interaction_DifficultyEvaluation(node, detail_shown)
            choice = await session.launch_interaction(interaction)
            if choice == 1:  # abandon
                await node.aclose_all_subagents()
                try:
                    await session.root.comment([node.id])
                except (AoA_Error, IsabelleError):
                    pass  # GoalNode or structural container — just cancel
                session.refresh_YAML()
                # Settle the "newly completed" delta HERE. Auto-commenting the
                # node (and tearing down its sub-agents) can flip the scope's
                # finishedness, but this abandon path does not otherwise flush
                # the delta (unlike `edit`/`comment`/`delete`). Flushing now
                # attributes any genuine completion to THIS action and marks it
                # announced, so it cannot resurface — misattributed and
                # contradictory — inside a later unrelated edit response (e.g. a
                # failed `fill`). The just-commented node itself is excluded from
                # the report by `Session.newly_completed_topmost`, so in the
                # common case this writes nothing.
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
    "comment": {"description": "Comment out or uncomment proof steps", "schema": _cc_comment_schema, "annotations": _MUT},
    "query":  {"description": "Search for Isabelle entities by semantic similarity, patterns, or exact name/term. "
                "Use exact_name to look up definitions; "
                "use exact_term to unfold fancy syntax and retrieve semantic explanations; "
                "use description and filters for discovery. "
                "If you fail to find a key lemma, increase `number`, retry with only `description`, "
                "and drop all other constraints like `term_patterns`, `exact_name`, and `name_contains`. "
                "Conversely, if a query returns too many irrelevant results, add the constraints to narrow down.",
               "schema": _cc_query_schema, "annotations": _RO},
    "recall": {"description": "Recall proof state from `proof.yaml`. Use only when you have lost track.", "schema": _cc_read_schema, "annotations": _RO},
    "recall_removed": {"description": "Browse proof steps that were archived before deletion.", "schema": _cc_recall_removed_schema, "annotations": _RO},
    "request_lemmas": {"description": "Report missing background lemmas and request that the external environment supply them.",
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
    "subagent": {"description": "Launch or resume a sub-agent to prove a goal or repair a proof in isolation. Call this when a goal is tedious and its proof would derail your main line of reasoning. Also call this to resume a suspended sub-agent.", "schema": _cc_subagent_schema, "annotations": _ACT},
    "cancel_subagent": {"description": "Permanently cancel and delete a sub-agent you dispatched.", "schema": _cc_close_subagent_schema, "annotations": _ACT},
    "refresh": {"description": "Reset the conversation and start over (the proof tree is kept). "
                "Write a briefing for your future self in `briefing` — "
                "it becomes your only memory. Use when your edits keep failing.",
                "schema": _cc_refresh_schema, "annotations": _ACT},
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
        self._subagent_lock = asyncio.Lock()
        self._last_mutate_fail_time: float = 0.0
        self._channel = InteractionChannel()
        self._suspended_task: asyncio.Task | None = None
        session._channel = self._channel

    # ------------------------------------------------------------------
    # Channel helpers
    # ------------------------------------------------------------------

    async def _race_outbox(self, task: asyncio.Task):
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
            return ("An edit/delete/comment operation is in progress. "
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

        perm_error = _check_tool_permission(session, name)
        if perm_error:
            return (perm_error, True)

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
                case "comment":
                    async def _run_comment():
                        r, e = await _comment_tool_logic(session, arguments)
                        await self._channel.outbox.put(EditResult(r, e))
                    result, is_error = await self._run_tool_via_channel(
                        _run_comment(), session, is_edit=False)
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
                case "request_lemmas":
                    result, is_error = await _request_lemmas_tool_logic(
                        session, arguments)
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
