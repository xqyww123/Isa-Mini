"""
Semantic retrieval and query-by-name tool logic.

Extracted from mcp_http_server.py — all semantic search / entity retrieval
functionality lives here.
"""

from __future__ import annotations

import asyncio
import os
import re
import sys
from io import StringIO
from time import time
from typing import Callable, NamedTuple, TypeVar

import jsoncomment

from Isabelle_RPC_Host.position import IsabellePosition
from Isabelle_RPC_Host.universal_key import universal_key, universal_key_of, UndefinedEntity
from Isabelle_Semantic_Embedding.semantics import (
    trunc_expr as _trunc_expr_base,
    trunc_expr,
    _get_definition_with_pos,
    Semantic_DB,
)

from .model import (
    Session, Minilang_State, MyIO,
    RaiseInteraction, Interaction, IsabelleError,
    EntityKind, print_indent, print_paragraph,
    Interaction_Retrieve,
    IsabelleEntity, IsabelleFact_Presented, FactByName,
    _THEOREM_KINDS, AGENT_EXPR_LIMIT,
    TOOL_SEARCH, InteractiveRetrievalMode, ForkingMode,
    _Prompt, _handle_raise_interaction,
)


# ============================================================================
# Schema Loading
# ============================================================================

_current_dir = os.path.dirname(os.path.abspath(__file__))
_json = jsoncomment.JsonComment()

def _load_schema(filename: str) -> dict:
    with open(os.path.join(_current_dir, "tools", filename), "r", encoding="utf-8") as f:
        return _json.load(f)


# ============================================================================
# Constants
# ============================================================================

BATCHED_SEMANTIC_SEARCH = True

_cc_semantic_search_schema = _load_schema(
    "cc_semantic_search.jsonc" if BATCHED_SEMANTIC_SEARCH
    else "cc_semantic_search_single.jsonc")

_cc_query_schema = {
    "type": "object",
    "properties": {
        "type": {
            "type": "string",
            "enum": ["constant", "lemma", "type", "typeclass", "locale",
                     "introduction rule", "elimination rule"],
            "description": "The kind of entity to query.",
        },
        "name": {
            "type": "string",
            "description": "The short or full name of the entity to look up.",
        },
    },
    "required": ["type", "name"],
}


# ============================================================================
# Command Header Parser
# ============================================================================

_COMMAND_HEADER_RE = re.compile(
    r"^\s*(?:private\s+|qualified\s+)?"
    r"(fun|primrec|function|definition|abbreviation|"
    r"datatype|codatatype|record|typedef|type_synonym|"
    r"inductive|inductive_set|coinductive|"
    r"locale|class|subclass|sublocale|interpretation|"
    r"lemma|theorem|corollary|proposition|schematic_goal|"
    r"instantiation|instance|overloading|"
    r"consts|axiomatization|nominal_datatype)\s+"
)


_PROOF_COMMAND_RE = re.compile(
    r"^\s*(?:private\s+|qualified\s+)?"
    r"(?:lemma|theorem|corollary|proposition|schematic_goal)\s"
)

def _parse_command_header(source: str) -> str:
    """Extract a concise header like ``fun fib`` from Isabelle command source.

    Handles type parameters: ``datatype ('a,'b) tree = ...`` -> ``datatype tree``.
    Fallback: first several words whose total length just exceeds 24 chars.
    """
    def _first_words(text: str) -> str:
        words = text.split()
        parts: list[str] = []
        total = 0
        for w in words:
            parts.append(w)
            total += len(w)
            if total > 24:
                break
        return ' '.join(parts)

    m = _COMMAND_HEADER_RE.match(source)
    if not m:
        return _first_words(source)
    keyword = m.group(1)
    rest = source[m.end():].lstrip()
    # Skip type parameters like ('a, 'b)
    if rest.startswith("(") and "'" in rest[:10]:
        depth = 0
        for i, ch in enumerate(rest):
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            if depth == 0:
                rest = rest[i + 1:].lstrip()
                break
    # Extract the name (first non-whitespace token, strip trailing colons)
    name_match = re.match(r"(\S+)", rest)
    if name_match:
        name = name_match.group(1).rstrip(":")
        return f"{keyword} {name}"
    return _first_words(source)


# ============================================================================
# Display Helpers
# ============================================================================

def _format_with_definition(
    session: Session,
    source: str,
    cmd_pos: IsabellePosition,
    indent: int,
    out,
) -> None:
    """Write definition source with show-once tracking.

    First time for a given *cmd_pos*: writes full indented source.
    Subsequent times: writes ``associated with `{header}```.
    """
    if cmd_pos in session.seen_commands:
        header = session.seen_commands[cmd_pos]
        print_indent(indent, out)
        out.write(f"associated with `{header}`\n")
    else:
        header = _parse_command_header(source)
        session.seen_commands[cmd_pos] = header
        for line in source.split('\n'):
            print_indent(indent, out)
            out.write(line)
            out.write('\n')

def _trunc_expr(s: str) -> str:
    return _trunc_expr_base(s, AGENT_EXPR_LIMIT)


# ============================================================================
# Multi-Query Formatting
# ============================================================================

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


# ============================================================================
# Warning Collection / Formatting
# ============================================================================

def _collect_query_warnings(
    knn_results: list[_KnnResult],
) -> list[list[str]]:
    """Collect warnings from each knn result into per-query lists."""
    per_query: list[list[str]] = []
    for r in knn_results:
        qwarns: list[str] = []
        if r.error:
            qwarns.append(f"Warning: {r.error}")
        for w in r.warnings:
            qwarns.append(f"Warning: {w}")
        per_query.append(qwarns)
    return per_query


def _format_warn_lines(
    queries: list[dict],
    per_query_warnings: list[list[str]],
) -> list[str]:
    """Format warnings grouped by query (only queries with warnings)."""
    lines: list[str] = []
    queries_with_warnings = [(q, ws) for q, ws in zip(queries, per_query_warnings) if ws]
    if not queries_with_warnings:
        return lines
    if len(queries) <= 1:
        for _, ws in queries_with_warnings:
            lines.extend(ws)
    else:
        for q, ws in queries_with_warnings:
            lines.append(f"Query: {_format_query_header(q)}")
            lines.extend(f"  {w}" for w in ws)
    return lines


# ============================================================================
# KNN Query
# ============================================================================

class _KnnResult(NamedTuple):
    fetched: list[Interaction_Retrieve.FetchedEntity]
    kinds: list[EntityKind]  # parallel to fetched
    warnings: list[str]
    error: str | None


async def _run_knn_for_query(
    ml_state: Minilang_State, q: dict, k: int,
) -> _KnnResult:
    """Run semantic_knn for a single query dict and resolve entities via RPC."""
    import logging as _logging
    _perf_log = _logging.getLogger("perf.run_knn_for_query")
    _t0 = time()
    try:
        kinds = [EntityKind.from_label(label) for label in q["kinds"]]
    except KeyError as e:
        return _KnnResult([], [], [], f"Invalid entity kind: {e}")
    _t_knn = time()
    results, warnings = await ml_state.semantic_knn(
        q.get("long_description") or None, k, kinds,
        term_patterns=q.get("term_patterns", []),
        type_patterns=q.get("type_patterns", []),
        theories_include=q.get("theories_include", []),
        name_contains=q.get("name_contains", []))
    _perf_log.info("_run_knn: semantic_knn %.3fs (%d results)", time() - _t_knn, len(results))
    if not results:
        return _KnnResult([], [], warnings, None)
    entities = [(rec.kind, rec.name) for _, rec in results]
    _t_retrieve = time()
    infos = await ml_state._retrieve_entity(entities)
    _perf_log.info("_run_knn: _retrieve_entity %.3fs (%d entities)", time() - _t_retrieve, len(entities))
    out: list[Interaction_Retrieve.FetchedEntity] = []
    out_kinds: list[EntityKind] = []
    for (score, rec), info in zip(results, infos):
        if info is None:
            short_name, exprs = rec.name, []
        else:
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
        out_kinds.append(rec.kind)
    _perf_log.info("_run_knn: total %.3fs", time() - _t0)
    return _KnnResult(out, out_kinds, warnings, None)


# ============================================================================
# Search Strategies
# ============================================================================

async def _semantic_search_direct(
    session: Session, queries: list[dict], k: int,
) -> str:
    """Run semantic search queries concurrently, returning formatted results."""
    import logging as _logging
    _perf_log = _logging.getLogger("perf.search_direct")
    _t0 = time()
    ml_state = session.root.ml_state
    connection = ml_state.connection

    # Run all queries concurrently (knn + entity retrieval in one step)
    _t_knn = time()
    knn_results = await asyncio.gather(
        *[_run_knn_for_query(ml_state, q, k) for q in queries])
    _perf_log.info("search_direct: all knn queries %.3fs (%d queries)", time() - _t_knn, len(queries))

    seen = session.seen_entities
    per_query_warnings = _collect_query_warnings(knn_results)
    # Collect new entities with their kinds
    new_items: list[tuple[Interaction_Retrieve.FetchedEntity, EntityKind]] = []
    for r in knn_results:
        for f, kind in zip(r.fetched[:k], r.kinds[:k]):
            if f.entity.short_name in seen:
                continue
            new_items.append((f, kind))
            seen.add(f.entity.short_name)

    if not new_items:
        lines: list[str] = ["No new relevant entities found." if seen else "No relevant entities found."]
        lines.extend(_format_warn_lines(queries, per_query_warnings))
        result = "\n".join(lines)
        session.log_tool_response("mcp__proof__search_isabelle", result)
        return result

    # Batch fetch definition sources concurrently (only for non-theorem kinds)
    from Isabelle_RPC_Host.universal_key import universal_key_of

    async def _get_def_for_entity(f, kind):
        if kind in _THEOREM_KINDS:
            return None
        try:
            uk = await universal_key_of(connection, kind, f.entity.full_name)
            return await _get_definition_with_pos(connection, kind, uk)
        except Exception:
            return None

    _t_defs = time()
    def_infos = await asyncio.gather(*[_get_def_for_entity(f, kind) for f, kind in new_items])
    _perf_log.info("search_direct: fetch_definitions %.3fs (%d entities)", time() - _t_defs, len(new_items))
    _perf_log.info("search_direct: total %.3fs", time() - _t0)

    # Format with definitions
    buf = StringIO()
    retrieved: list[str] = []
    for (f, _kind), def_info in zip(new_items, def_infos):
        expr_str = _trunc_expr(', '.join(f.entity.expression))
        if expr_str:
            buf.write(f"- {f.entity.short_name}:")
            print_paragraph(1, buf, expr_str)
        else:
            buf.write(f"- {f.entity.short_name}\n")
        if f.interpretation and (_kind != EntityKind.THEOREM or expr_str.endswith("…")):
            buf.write(f"  {f.interpretation}\n")
        if def_info is not None:
            source, cmd_pos = def_info
            _format_with_definition(session, source, cmd_pos, indent=1, out=buf)
        retrieved.append(f"{f.entity.short_name}: {expr_str}")
    for w in _format_warn_lines(queries, per_query_warnings):
        buf.write(w)
        buf.write('\n')
    if retrieved:
        query_str = "; ".join(_format_query_header(q) for q in queries)
        session.log_retrieval(query_str, retrieved, quiet=True)
    result = buf.getvalue().rstrip('\n')
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

    lines: list[str] = []
    per_query_warnings = _collect_query_warnings(knn_results)

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
        lines.extend(_format_warn_lines(queries, per_query_warnings))
        return "\n".join(lines)

    # Extend the interaction's candidate list
    start_idx = len(existing)
    existing.extend(new_facts)

    # Format in the same style as Interaction_Retrieve.prompt()
    for i, fetched in enumerate(new_facts):
        expr_str = _trunc_expr(', '.join(fetched.entity.expression))
        if expr_str:
            lines.append(f"{start_idx + i}. {fetched.entity.short_name}: {expr_str}")
        else:
            lines.append(f"{start_idx + i}. {fetched.entity.short_name}")
        if fetched.interpretation:
            lines.append(f"  {fetched.interpretation}")
    lines.extend(_format_warn_lines(queries, per_query_warnings))
    return "\n".join(lines)


# ============================================================================
# Tool Entry Points
# ============================================================================

async def _query_entity_core(connection, tag: EntityKind, name: str
    ) -> tuple[str, bool, 'universal_key | None']:
    """Core query logic: resolve name, look up semantic record, format.
    Returns (formatted_text, is_error, uk_or_None). Needs only a connection, no Session.
    uk is returned for callers that need to fetch definition sources."""
    try:
        uk = await universal_key_of(connection, tag, name)
        prefix = ""
    except UndefinedEntity:
        if "." in name:
            short = name.rsplit(".", 1)[1]
            try:
                uk = await universal_key_of(connection, tag, short)
                prefix = f"The {name} is undefined, but we find:\n"
            except Exception:
                return (f'Undefined: "{name}". Try search_isabelle.', True, None)
        else:
            return (f'Undefined: "{name}". Try search_isabelle.', True, None)
    except IsabelleError as e:
        return (str(e), True, None)

    rec = Semantic_DB[uk]
    buf = StringIO()
    buf.write(prefix)
    if rec is not None:
        buf.write(f"{rec.kind.label} {rec.name}:")
        print_paragraph(2, buf, trunc_expr(rec.expr) if rec.expr else "")
        if rec.interpretation:
            buf.write(rec.interpretation)
            buf.write('\n')
    else:
        buf.write(f"{tag.label} {name}\n")

    return (buf.getvalue().rstrip('\n'), False, uk)


async def _query_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    """Query entity by name with show-once definition source tracking."""
    _TOOL = "mcp__proof__query"
    session.log_tool_call(_TOOL, args)

    def _ret(msg: str, is_error: bool) -> tuple[str, bool]:
        session.log_tool_response(_TOOL, ("ERROR: " if is_error else "") + msg)
        return (msg, is_error)

    connection = session.root.ml_state.connection
    t = args.get("type", "")
    name = args.get("name", "")

    if not isinstance(t, str) or not isinstance(name, str):
        return _ret("Invalid arguments.", True)
    try:
        tag = EntityKind.from_label(t)
    except KeyError:
        return _ret(f"Invalid type: {t!r}.", True)
    if not name:
        return _ret("Empty name.", True)

    text, is_error, uk = await _query_entity_core(connection, tag, name)
    if is_error or uk is None:
        return _ret(text, is_error)

    buf = StringIO()
    buf.write(text)

    # Session-specific: fetch definition source with position-based caching
    # Skip proof commands (lemma/theorem/…) whose source is the full proof
    def_info = await _get_definition_with_pos(connection, tag, uk)
    if def_info is not None:
        source, cmd_pos = def_info
        if not _PROOF_COMMAND_RE.match(source):
            buf.write('\n')
            _format_with_definition(session, source, cmd_pos, 0, buf)

    # Session-specific: fetch candidate definitions for constants
    if tag == EntityKind.CONSTANT:
        try:
            candidates = await session.root.ml_state.potential_defs_of([name])
            if candidates:
                seen = session.seen_entities
                buf.write('\nRelevant definitions:\n')
                for cand in candidates:
                    if cand.short_name in seen:
                        buf.write(f'- {cand.short_name} (seen)\n')
                    else:
                        expr_str = _trunc_expr(', '.join(cand.expression))
                        buf.write(f'- {cand.short_name}:')
                        print_paragraph(1, buf, expr_str)
                        seen.add(cand.short_name)
        except Exception:
            pass

    return _ret(buf.getvalue().rstrip('\n'), False)


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
        error_msg = '; '.join(e.errors)
        session.log_tool_response("mcp__proof__search_isabelle", f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response("mcp__proof__search_isabelle", f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)
