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
import os
import sys
import socket
from io import StringIO
from typing import Any, Callable, NamedTuple, TypeVar

import jsoncomment
import uvicorn
from mcp.server.lowlevel import Server as MCPServer
from mcp.server.streamable_http_manager import StreamableHTTPSessionManager
from mcp.types import Tool, TextContent, CallToolResult

from .model import (
    the_session, _session_var, Session, Minilang_State, MyIO,
    ImmediateAnswer, RaiseInteraction, Working_Interactions, Interaction,
    AoA_Error, InternalError, ArgumentError, IsabelleError,
    Parse_Node, parsing_node, _trivial_parsing, normalize_answer, Interaction_BadAnswer, ForkingMode, InteractiveRetrievalMode,
    TOOL_SEARCH,
    EntityKind, print_indent, print_paragraph,
    Interaction_Retrieve,
    IsabelleEntity, IsabelleFact_Presented, FactByName,
    _THEOREM_KINDS,
    AGENT_EXPR_LIMIT,
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

_cc_edit_schema = _load_schema("cc_edit.jsonc")
_cc_answer_schema = _load_schema("cc_answer.jsonc")
_cc_delete_schema = _load_schema("cc_delete.jsonc")

BATCHED_SEMANTIC_SEARCH = True

from Isabelle_Semantic_Embedding.semantics import trunc_expr as _trunc_expr_base

def _trunc_expr(s: str) -> str:
    return _trunc_expr_base(s, AGENT_EXPR_LIMIT)

_cc_semantic_search_schema = _load_schema(
    "cc_semantic_search.jsonc" if BATCHED_SEMANTIC_SEARCH
    else "cc_semantic_search_single.jsonc")


# ============================================================================
# Tool Logic Helpers
# ============================================================================

class _Prompt(NamedTuple):
    """A prompt string to return to the LLM."""
    text: str

class _Result(NamedTuple):
    """A resolved result (gen_node or Any)."""
    value: Any


async def _handle_raise_interaction(
    session: Session,
    e: RaiseInteraction,
    tool_name: str,
) -> '_Prompt | _Result':
    """Dispatch a RaiseInteraction. Returns _Prompt (for LLM) or _Result (all done)."""
    wi = Working_Interactions(
        interactions=e.interactions,
        results=[None] * len(e.interactions),
        result_set=[False] * len(e.interactions),
        kontinuation=e.kontinuation,
    )
    session.working_interactions.append(wi)
    forking = [(i, inter) for i, inter in enumerate(e.interactions)
               if inter.forking != ForkingMode.NO]
    n_inline = len(e.interactions) - len(forking)
    session.log_interaction(tool_name,
        f"{len(e.interactions)} interactions ({len(forking)} forking, {n_inline} inline)")
    if forking:
        session._launch_forks(forking, wi)

    # 2. Find first unfinished non-forking interaction
    for i, inter in enumerate(wi.interactions):
        if wi.result_set[i] is False:
            buffer = StringIO()
            try:
                await inter.prompt(0, MyIO(buffer))
            except ImmediateAnswer as imm:
                wi.results[i] = imm.answer
                wi.result_set[i] = True
                continue
            session.log_tool_response(tool_name, f"[INTERACTION PROMPT]\n{buffer.getvalue()}")
            return _Prompt(buffer.getvalue())

    # 3. All non-forking done — await forks and call continuation
    session.log_interaction("continuation", "all interactions resolved")
    try:
        result = await wi.run_continuation()
    except RaiseInteraction as nested:
        session.working_interactions.pop()
        return await _handle_raise_interaction(session, nested, tool_name)
    session.working_interactions.pop()
    session.log_interaction(tool_name, "interaction resolved")
    return _Result(result)


async def _execute_proof_action(
    session: Session,
    action: str,
    step: str,
    pn: parsing_node,
    tool_name: str,
    log_prefix: str,
) -> str:
    """Execute a proof action with complete error handling."""
    session.root.session.age += 1
    if not callable(pn):
        raise TypeError(f"parsing_node must be callable, got {type(pn)}")

    try:
        match action:
            case "fill":
                node = await session.root.fill(step, pn)
                session.refresh_YAML()
                response = await P.filled_step_message(step, session.root, node, session)
            case "insert_before":
                node = await session.root.insert_before(step, pn)
                session.refresh_YAML()
                response = await P.inserted_before_step_message(step, session.root, node, session)
            case "amend":
                node = await session.root.amend(step, pn)
                session.refresh_YAML()
                response = await P.amended_step_message(step, session.root, node, session)
            case _:
                raise ArgumentError({"action": action}, P.invalid_action_error(action))

        session.log_tool_response(tool_name, response)
        session.log_proof_tree_snapshot(f"{log_prefix}_step_{step}")
        return response

    except RaiseInteraction as e:
        original_kont = e.kontinuation
        async def wrapped_kont(results: list[Any]) -> str:
            result_gn = await original_kont(results)
            assert callable(result_gn), \
                "Continuation from _execute_proof_action must return gen_node (callable)"
            return await _execute_proof_action(
                session, action, step, _trivial_parsing(result_gn), tool_name, log_prefix) # type: ignore[arg-type]
        wrapped_e = RaiseInteraction(e.interactions, wrapped_kont)
        result = await _handle_raise_interaction(session, wrapped_e, tool_name)
        if isinstance(result, _Prompt):
            return result.text
        return result.value

    except AoA_Error as e:
        error_msg = str(e)
        session.log_tool_response(tool_name, f"ERROR: {error_msg}")
        return error_msg


# ============================================================================
# Permission Check (both modes)
# ============================================================================

_BLOCKED_DURING_INTERACTION = {"edit", "delete"}

def _check_tool_permission(session: Session, tool_name: str) -> str | None:
    """Check interaction state. Returns error message or None."""
    if session.working_interactions:
        if tool_name in _BLOCKED_DURING_INTERACTION:
            return "Pending interaction — use the answer tool first."
    elif tool_name == "answer":
        return "No pending interaction."
    return None


# ============================================================================
# Tool Logic Functions (shared, no framework dependency)
# ============================================================================

async def _edit_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call("mcp__proof__edit", args)
    try:
        step = args["target_step"]
        try:
            gn = Parse_Node(args["proof_operation"])
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__edit", f"ERROR: {error_msg}")
            return (error_msg, True)
        result = await _execute_proof_action(
            session, args["action"], step, gn,
            "mcp__proof__edit", "after_fill")
        return (result, False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(e.errors)}"
        session.log_tool_response("mcp__proof__edit", f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response("mcp__proof__edit", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


async def _delete_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call("mcp__proof__delete", args)
    try:
        session.root.session.age += 1
        steps = args["target_steps"]
        try:
            not_found = await session.root.delete(steps)
            if len(not_found) == len(steps):
                noun = "step" if len(not_found) == 1 else "steps"
                error_msg = f"Error: {noun} {', '.join(not_found)} not found."
                session.log_tool_response("mcp__proof__delete", f"ERROR: {error_msg}")
                return (error_msg, True)
            deleted = [s for s in steps if s not in not_found]
            session.refresh_YAML()
            response = await P.deleted_steps_message(deleted, session.root, session)
            if not_found:
                noun = "step" if len(not_found) == 1 else "steps"
                response += f"\nWarning: {noun} {', '.join(not_found)} not found and skipped."
        except AoA_Error as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__delete", f"ERROR: {error_msg}")
            return (error_msg, True)
        session.log_tool_response("mcp__proof__delete", response)
        session.log_proof_tree_snapshot("after_delete")
        return (response, False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(e.errors)}"
        session.log_tool_response("mcp__proof__delete", f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response("mcp__proof__delete", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


async def _answer_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call("mcp__proof__answer", args)
    try:
        if not session.working_interactions:
            error_msg = "No pending interaction to answer"
            session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
            return (error_msg, True)
        wi = session.working_interactions[-1]

        current_idx = None
        for i, inter in enumerate(wi.interactions):
            if wi.result_set[i] is False:
                current_idx = i
                break

        if current_idx is None:
            error_msg = "No pending interaction to answer"
            session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
            return (error_msg, True)

        current_inter = wi.interactions[current_idx]
        normalized = normalize_answer(args.get("indexes"), args.get("text"))

        try:
            result = await current_inter.answer(normalized)
        except Interaction_BadAnswer as e:
            error_msg = str(e)
            session.log_tool_response("mcp__proof__answer", f"BAD ANSWER: {error_msg}")
            return (error_msg, True)
        except RaiseInteraction as e:
            r = await _handle_raise_interaction(session, e, "mcp__proof__answer")
            if isinstance(r, _Prompt):
                return (r.text, False)
            result = r.value

        wi.results[current_idx] = result
        wi.result_set[current_idx] = True
        n_done = sum(1 for f in wi.result_set if f is True)
        session.log_interaction("mcp__proof__answer",
            f"answered interaction {current_idx} ({n_done}/{len(wi.interactions)} done)")

        for i, inter in enumerate(wi.interactions):
            if wi.result_set[i] is False:
                buffer = StringIO()
                try:
                    await inter.prompt(0, MyIO(buffer))
                except ImmediateAnswer as imm:
                    wi.results[i] = imm.answer
                    wi.result_set[i] = True
                    continue
                session.log_tool_response("mcp__proof__answer", f"[INTERACTION PROMPT]\n{buffer.getvalue()}")
                return (buffer.getvalue(), False)

        session.log_interaction("continuation", "all interactions resolved")
        final = await wi.run_continuation()
        session.working_interactions.pop()
        session.log_tool_response("mcp__proof__answer", f"[INTERACTION RESOLVED] {final}")
        if not session.is_major:
            await session.interrupt()
        return (str(final), False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(e.errors)}"
        session.log_tool_response("mcp__proof__answer", f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response("mcp__proof__answer", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


def _format_query_header(q: dict) -> str:
    """Pretty-print a query dict into a header line."""
    parts: list[str] = []
    desc = q.get("long_description", "")
    if desc:
        parts.append(desc)
    for key, label in [
        ("term_patterns", "term patterns"),
        ("type_patterns", "type patterns"),
        ("theories_include", "theories"),
        ("name_contains", "name contains"),
    ]:
        vals = q.get(key, [])
        if vals:
            parts.append(f"{label}: {', '.join(vals)}")
    return "; ".join(parts) if parts else "(no filters)"


_T = TypeVar("_T")

def _format_multi_query_grouped(
    queries: list[dict],
    groups: list[list[_T]],
    name_of: Callable[[_T], str],
    format_entity: Callable[[_T], str],
    seen: set[str],
    empty_msg: str = "No relevant entities found.",
    preamble_of: Callable[[dict, list[_T]], list[str]] | None = None,
    show_repeated: bool = True,
) -> list[str]:
    """Format grouped multi-query results with cross-query dedup by reference.

    ``seen`` is mutated: names of formatted entities are added.
    ``preamble_of(query, items)`` may return extra lines (e.g. warnings)
    inserted right after the ``Query:`` header.
    ``show_repeated``: if False, silently skip repeated entities instead of listing them.
    """
    lines: list[str] = []
    for q, items in zip(queries, groups):
        lines.append(f"Query: {_format_query_header(q)}")
        if preamble_of is not None:
            lines.extend(preamble_of(q, items))
        new_items: list[_T] = []
        repeated_names: list[str] = []
        for item in items:
            name = name_of(item)
            if name in seen:
                repeated_names.append(name)
            else:
                new_items.append(item)
                seen.add(name)
        if not new_items and not repeated_names:
            lines.append(f"  {empty_msg}")
        elif not new_items:
            lines.append(f"  {empty_msg}")
        for item in new_items:
            lines.append(format_entity(item))
        if show_repeated and repeated_names:
            if new_items:
                lines.append(f"  {', '.join(repeated_names)} are also relevant")
            else:
                lines.append(f"  {', '.join(repeated_names)} are relevant. No new entities found.")
        lines.append("")
    return lines


class _KnnResult(NamedTuple):
    fetched: list[Interaction_Retrieve.FetchedEntity]
    warnings: list[str]
    error: str | None


async def _run_knn_for_query(
    ml_state: Minilang_State, q: dict, k: int,
) -> _KnnResult:
    """Run semantic_knn for a single query dict and resolve entities via RPC."""
    try:
        kinds = [EntityKind.from_label(label) for label in q["kinds"]]
    except KeyError as e:
        return _KnnResult([], [], f"Invalid entity kind: {e}")
    results, warnings = await ml_state.semantic_knn(
        q.get("long_description") or None, k, kinds,
        term_patterns=q.get("term_patterns", []),
        type_patterns=q.get("type_patterns", []),
        theories_include=q.get("theories_include", []),
        name_contains=q.get("name_contains", []))
    if not results:
        return _KnnResult([], warnings, None)
    entities = [(rec.kind, rec.name) for _, rec in results]
    infos = await ml_state._retrieve_entity(entities)
    out: list[Interaction_Retrieve.FetchedEntity] = []
    for (score, rec), info in zip(results, infos):
        if info is None:
            continue
        short_name, exprs = info
        if rec.kind in _THEOREM_KINDS:
            entity: IsabelleEntity = IsabelleFact_Presented(
                full_name=rec.name, short_name=short_name,
                fact=FactByName(refer_by="name", name=short_name),
                expression=exprs)
        else:
            entity = IsabelleEntity(
                full_name=rec.name, short_name=short_name,
                expression=exprs)
        out.append(Interaction_Retrieve.FetchedEntity(
            entity=entity,
            score=score,
            interpretation=' '.join(rec.interpretation.split()) if rec.interpretation else None))
    return _KnnResult(out, warnings, None)


async def _semantic_search_direct(
    session: Session, queries: list[dict], k: int,
) -> str:
    """Run semantic search queries concurrently, returning formatted results."""
    ml_state = session.root.ml_state

    # Run all queries concurrently (knn + entity retrieval in one step)
    knn_results = await asyncio.gather(
        *[_run_knn_for_query(ml_state, q, k) for q in queries])

    seen = session.seen_entities
    lines: list[str] = []
    warn_lines: list[str] = []
    retrieved: list[str] = []
    for r in knn_results:
        if r.error:
            warn_lines.append(f"Warning: {r.error}")
        for w in r.warnings:
            warn_lines.append(f"Warning: {w}")
        for f in r.fetched[:k]:
            if f.entity.short_name in seen:
                continue
            expr_str = _trunc_expr(', '.join(f.entity.expression))
            lines.append(f"- {f.entity.short_name}: {expr_str}")
            if f.interpretation:
                lines.append(f"  {f.interpretation}")
            seen.add(f.entity.short_name)
            retrieved.append(f"{f.entity.short_name}: {expr_str}")
    if not lines:
        lines.append("No new relevant entities found." if seen else "No relevant entities found.")
    lines.extend(warn_lines)
    if retrieved:
        query_str = "; ".join(_format_query_header(q) for q in queries)
        session.log_retrieval(query_str, retrieved, quiet=True)
    result = "\n".join(lines)
    session.log_tool_response("mcp__proof__search_isabelle", result)
    return result


class Interaction_RetrieveForSearch(Interaction_Retrieve):
    """Retrieve entities for semantic search filtering. No prove-in-time."""

    async def prompt(self, indent: int, file: MyIO) -> None:
        title = self._entity_title()
        print_indent(indent, file)
        if self.query:
            file.write(f"You are looking for {title} establishing:")
            print_paragraph(indent, file, self.query)
        else:
            file.write(f"You are looking for {title} matching the search criteria.")
        file.write("\n")
        file.write(f"Select all relevant {title} from the following list:\n")
        await self._prompt_candidates(indent, file)
        if self.fork_allowed_tools is None or TOOL_SEARCH in self.fork_allowed_tools:
            file.write("\nYou are encouraged to call the search_isabelle tool "
                       "to find more if none of the above is relevant.\n")
        file.write("Answer with the indices of all relevant entries.\n")


async def _semantic_search_with_filtering(session: Session, queries: list[dict]) -> str:
    """Run semantic search and raise Interaction_RetrieveForSearch for fork-based filtering.

    Creates one interaction per query; all are raised together so forks run concurrently.
    """
    ml_state = session.root.ml_state
    interactions: list[Interaction] = []
    for q in queries:
        try:
            kinds = [EntityKind.from_label(label) for label in q["kinds"]]
        except KeyError as e:
            continue
        interaction = Interaction_RetrieveForSearch(
            state=ml_state, query=q.get("long_description", "") or "", kinds=kinds,
            initial_k=50,
            single_choice=False,
            term_patterns=q.get("term_patterns", []),
            type_patterns=q.get("type_patterns", []),
            theories_include=q.get("theories_include", []),
            name_contains=q.get("name_contains", []),
        )
        interactions.append(interaction)

    if not interactions:
        return "No relevant entities found."

    _empty_msg = ("No relevant entities exist. "
        "Exhaustive search completed — you MUST consider alternative proof strategies."
        if session.interactive_retrieval == InteractiveRetrievalMode.YES_WITH_RECURSIVE_RETRIEVAL
        else "No relevant entities found.")

    seen = session.seen_entities

    async def format_selected(results: list[list[IsabelleEntity]]) -> str:
        if len(results) == 1:
            selected = results[0]
            if not selected:
                return _empty_msg
            new_entities = [e for e in selected if e.short_name not in seen]
            repeated = [e.short_name for e in selected if e.short_name in seen]
            lines: list[str] = []
            for entity in new_entities:
                lines.append(f"- {entity.short_name}: {_trunc_expr(', '.join(entity.expression))}")
                seen.add(entity.short_name)
            if repeated:
                if new_entities:
                    lines.append(f"{', '.join(repeated)} are also relevant")
                else:
                    lines.append(f"{', '.join(repeated)} are relevant. No new entities found.")
            return "\n".join(lines) if lines else _empty_msg

        # Multiple queries — grouped output with cross-query dedup by reference
        return "\n".join(_format_multi_query_grouped(
            queries, results,
            name_of=lambda e: e.short_name,
            format_entity=lambda e: f"  {e.short_name}: {_trunc_expr(', '.join(e.expression))}",
            seen=seen,
            empty_msg=_empty_msg,
        ))

    raise RaiseInteraction(interactions, format_selected)


def _find_active_retrieve_fact(session: Session) -> Interaction_Retrieve | None:
    """Find the active Interaction_Retrieve in the interaction stack, if any."""
    for wi in reversed(session.working_interactions):
        for i, inter in enumerate(wi.interactions):
            if isinstance(inter, Interaction_Retrieve) and wi.result_set[i] is False:
                return inter
    return None


async def _semantic_search_extend_candidates(
    session: Session, queries: list[dict], interaction: Interaction_Retrieve,
) -> str:
    """Run semantic search queries and extend the active interaction's candidate list.
    Output uses the same format as the interaction prompt, with continuing indices."""
    ml_state = session.root.ml_state

    # Run all queries concurrently (knn + entity retrieval in one step)
    knn_results = await asyncio.gather(
        *[_run_knn_for_query(ml_state, q, 10) for q in queries])

    # Collect warnings and errors (appended at end)
    lines: list[str] = []
    warn_lines: list[str] = []
    for r in knn_results:
        if r.error:
            warn_lines.append(f"Warning: {r.error}")
        for w in r.warnings:
            warn_lines.append(f"Warning: {w}")

    # Deduplicate against existing candidates and across queries
    existing = await interaction.candidate_facts()
    existing_names = {f.entity.full_name for f in existing}
    new_facts: list[Interaction_Retrieve.FetchedEntity] = []
    seen_new: set[str] = set()
    for r in knn_results:
        for f in r.fetched:
            name = f.entity.full_name
            if name in existing_names or name in seen_new:
                continue
            seen_new.add(name)
            new_facts.append(f)

    if not new_facts:
        lines.append("No new matching entities found.")
        lines.extend(warn_lines)
        return "\n".join(lines)

    # Extend the interaction's candidate list
    start_idx = len(existing)
    existing.extend(new_facts)

    # Format in the same style as Interaction_Retrieve.prompt()
    for i, fetched in enumerate(new_facts):
        lines.append(f"{start_idx + i}. {fetched.entity.short_name}: {_trunc_expr(', '.join(fetched.entity.expression))}")
        if fetched.interpretation:
            lines.append(f"  {fetched.interpretation}")
    lines.extend(warn_lines)
    return "\n".join(lines)


async def _semantic_search_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call("mcp__proof__search_isabelle", args)
    try:
        queries = args["queries"] if BATCHED_SEMANTIC_SEARCH else [args]
        active = _find_active_retrieve_fact(session)
        if active is not None:
            # Inside a fork with an active Interaction_Retrieve — extend its candidates
            result = await _semantic_search_extend_candidates(session, queries, active)
            return (result, False)
        # Check if interactive retrieval is enabled
        if session.interactive_retrieval != InteractiveRetrievalMode.NO:
            result = await _semantic_search_with_filtering(session, queries)
            return (result, False)
        else:
            # Direct (non-interactive) retrieval — return raw results
            result = await _semantic_search_direct(session, queries, k=25)
            return (result, False)
    except RaiseInteraction as e:
        r = await _handle_raise_interaction(session, e, "mcp__proof__search_isabelle")
        if isinstance(r, _Prompt):
            return (r.text, False)
        return (str(r.value), False)
    except IsabelleError as e:
        error_msg = f"Isabelle error: {'; '.join(e.errors)}"
        session.log_tool_response("mcp__proof__search_isabelle", f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response("mcp__proof__search_isabelle", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)


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
    tool_lock = asyncio.Lock()  # serialize tool calls per session

    # Build tool list: built-in + extras
    tools: list[Tool] = [
        Tool(name="edit",
             description="Edit the proof.yaml file",
             inputSchema=_cc_edit_schema),
        Tool(name="delete",
             description="Delete proof steps",
             inputSchema=_cc_delete_schema),
        Tool(name="answer",
             description="Answer a pending question",
             inputSchema=_cc_answer_schema),
        Tool(name="search_isabelle",
             description="Search for Isabelle entities.",
             inputSchema=_cc_semantic_search_schema),
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

        # Permission check (both modes)
        perm_error = _check_tool_permission(session, name)
        if perm_error:
            return CallToolResult(
                content=[TextContent(type="text", text=perm_error)], isError=True)

        is_error = False
        match name:
            case "edit":
                async with tool_lock:
                    result, is_error = await _edit_tool_logic(session, arguments)
            case "delete":
                async with tool_lock:
                    result, is_error = await _delete_tool_logic(session, arguments)
            case "answer":
                async with tool_lock:
                    result, is_error = await _answer_tool_logic(session, arguments)
            case "search_isabelle":
                result, is_error = await _semantic_search_tool_logic(session, arguments)
            case _:
                handler = extra_handlers.get(name)
                if handler is not None:
                    ret = await handler(arguments)
                    content = ret.get("content", [])
                    return CallToolResult(
                        content=[TextContent(type="text", text=c.get("text", "")) for c in content])
                return CallToolResult(
                    content=[TextContent(type="text", text=f"Unknown tool: {name}")], isError=True)

        return CallToolResult(
            content=[TextContent(type="text", text=result)], isError=is_error)

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

    async def __call__(self, scope, receive, send):
        if scope["type"] not in ("http", "websocket"):
            return

        path: str = scope["path"]
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
        return f"http://127.0.0.1:{self._port}/mcp/{session_id}"

    async def unregister_session(self, session_id: str):
        app = self._router.apps.pop(session_id, None)
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
