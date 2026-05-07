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
from typing import Any

import json
import jsoncomment

from Isabelle_RPC_Host import pretty_unicode
from Isabelle_RPC_Host.position import IsabellePosition
from Isabelle_RPC_Host.universal_key import universal_key, universal_key_of, UndefinedEntity
from Isabelle_Semantic_Embedding.semantics import (
    trunc_expr as _trunc_expr_base,
    trunc_expr,
    _get_definition_with_pos,
    Semantic_DB,
)

from .model import (
    Session, Minilang_State, MyIO, short_name,
    Interaction, IsabelleError, ArgumentError,
    EntityKind, print_indent, print_paragraph, print_expression_list,
    Interaction_Retrieve, RetrievedEntity, IsabelleEntity,
    _THEOREM_KINDS, AGENT_EXPR_LIMIT,
    TOOL_SEARCH, InteractiveRetrievalMode,
    InternalError_UnparsedTerm,
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

DEFAULT_QUERY_K = 15
MAX_QUERY_K = 50

_cc_query_schema = _load_schema(
    "cc_semantic_search.jsonc" if BATCHED_SEMANTIC_SEARCH
    else "cc_semantic_search_single.jsonc")


def _query_k(q: dict) -> int:
    k = q.get("number", DEFAULT_QUERY_K)
    if not isinstance(k, int) or k < 1:
        return DEFAULT_QUERY_K
    return min(k, MAX_QUERY_K)


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
    r"(?:lemma|lemmas|theorem|corollary|proposition|schematic_goal|by|apply|done)\s"
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

def _trunc_expr(s) -> str:
    from .model import IsaTerm
    return _trunc_expr_base(s.unicode if isinstance(s, IsaTerm) else s, AGENT_EXPR_LIMIT)


async def _format_fetched_entity(
    f: RetrievedEntity,
    buf,
    *,
    prefix: str = "- ",
    indent: int = 0,
    session: Session | None = None,
    def_info: tuple[str, IsabellePosition] | bool | None = None,
    potential_defs: bool = False,
    abbreviation_defs: dict[str, tuple[str, str]] = {},
) -> None:
    """Render a single retrieved entity in unified format.

    ``prefix``: line prefix, e.g. ``"- "`` for final output, ``"{i}. "`` for numbered lists.
    ``indent``: base indentation level.
    ``def_info``: ``True`` to fetch definition via RPC, a pre-fetched tuple to use directly,
    or ``None``/``False`` to skip.  Requires ``session`` for both fetching and show-once tracking.
    ``potential_defs``: if True and entity is a constant, append relevant definitions.
    ``abbreviation_defs``: map from abbreviation full name to (lhs, rhs) pretty-printed strings.
    """
    exprs = f.entity.expression
    roles = getattr(f.entity, 'roles', [])
    tag = "" if (roles or f.entity.kind not in _THEOREM_KINDS) else " [opaque]"
    print_indent(indent, buf)
    if exprs:
        buf.write(f"{prefix}{f.entity.short_name.unicode}{tag}:")
        truncated = print_expression_list(indent + 1, buf, exprs)
    else:
        buf.write(f"{prefix}{f.entity.short_name.unicode}{tag}\n")
        truncated = False
    if f.interpretation and (f.entity.kind not in _THEOREM_KINDS or truncated):
        print_indent(indent + 1, buf)
        buf.write(f"{f.interpretation}\n")
    if def_info is True and session is not None:
        def_info = await _get_def_for_fetched(
            session.retrieval_state().connection, f, ctxt=session.retrieval_state().name)
    if isinstance(def_info, tuple) and session is not None:
        source, cmd_pos = def_info
        if not _PROOF_COMMAND_RE.match(source):
            _format_with_definition(session, source, cmd_pos, indent=indent + 1, out=buf)
    if abbreviation_defs and session is not None:
        abbrev_names = f.entity.abbreviation_names
        for aname in abbrev_names:
            if aname in abbreviation_defs and aname not in session.seen_abbreviations:
                session.seen_abbreviations.add(aname)
                lhs, rhs = abbreviation_defs[aname]
                print_indent(indent + 1, buf)
                buf.write(f"where `{_trunc_expr(lhs)}` abbreviates `{_trunc_expr(rhs)}`\n")
    if potential_defs and session is not None and f.entity.kind == EntityKind.CONSTANT:
        try:
            candidates = await session.retrieval_state().potential_defs_of([f.entity.short_name])
            if candidates:
                seen = session.seen_entities
                print_indent(indent + 1, buf)
                buf.write('Relevant definitions:\n')
                for cand in candidates:
                    if cand.short_name in seen:
                        print_indent(indent + 1, buf)
                        buf.write(f'- {cand.short_name.unicode} (seen)\n')
                    else:
                        cand_expr = _trunc_expr(', '.join(e.unicode for e in cand.expression))
                        print_indent(indent + 1, buf)
                        buf.write(f'- {cand.short_name.unicode}:')
                        print_paragraph(indent + 2, buf, cand_expr)
                        seen.add(cand.short_name)
        except Exception:
            pass


def _format_repeated(
    new_names: 'list[short_name]',
    repeated_names: 'list[short_name]',
    buf,
    *,
    indent: int = 0,
) -> None:
    """Append a note about repeated (already-seen) entity names."""
    if repeated_names:
        print_indent(indent, buf)
        if new_names:
            buf.write(f"{', '.join(n.unicode for n in repeated_names)} are also relevant\n")
        else:
            buf.write(f"{', '.join(n.unicode for n in repeated_names)} are relevant. No new entities found.\n")


# ============================================================================
# Multi-Query Formatting
# ============================================================================

def _format_query_header(q: dict) -> str:
    """Pretty-print a query dict into a header line."""
    parts: list[str] = []
    exact_term = q.get("exact_term", "")
    if exact_term:
        parts.append(f"exact term: {exact_term}")
    exact = q.get("exact_name", "")
    if exact:
        parts.append(f"exact name: {exact}")
    desc = q.get("long_description", "")
    if desc:
        parts.append(desc)
    target_type = q.get("target_type", "")
    if target_type:
        parts.append(f"target type: {target_type}")
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


# ============================================================================
# Warning Collection / Formatting
# ============================================================================

_KnnQueryResult = tuple[list[RetrievedEntity], list[str], str | None]
# (fetched, warnings, error)

def _collect_query_warnings(
    knn_results: list[_KnnQueryResult],
) -> list[list[str]]:
    """Collect warnings from each knn result into per-query lists."""
    per_query: list[list[str]] = []
    for _fetched, warnings, error in knn_results:
        qwarns: list[str] = []
        if error:
            qwarns.append(f"Warning: {error}")
        for w in warnings:
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

async def _run_knn_for_query(
    ml_state: Minilang_State, q: dict,
) -> _KnnQueryResult:
    """Parse a query dict and run semantic_knn. Reads ``k`` from the query dict."""
    try:
        kinds = [EntityKind.from_label(label) for label in q.get("kinds", ["constant"])]
    except KeyError as e:
        return ([], [], f"Invalid entity kind: {e}")
    exact_name = q.get("exact_name") or None
    fetched, warnings = await ml_state.semantic_knn(
        q.get("long_description") or None, _query_k(q), kinds,
        term_patterns=q.get("term_patterns", []),
        type_patterns=q.get("type_patterns", []),
        theories_include=q.get("theories_include", []),
        name_contains=q.get("name_contains", []),
        exact_name=exact_name,
        target_type=q.get("target_type", "") or "")
    return (fetched, warnings, None)


async def _get_def_for_fetched(
    connection, f: RetrievedEntity, ctxt: Any = None,
) -> tuple[str, IsabellePosition] | None:
    """Fetch definition source for an entity. Returns None on failure."""
    try:
        uk = await universal_key_of(connection, f.entity.kind, f.entity.full_name, ctxt=ctxt)
        return await _get_definition_with_pos(connection, f.entity.kind, uk, ctxt=ctxt)
    except Exception:
        return None


# ============================================================================
# Search Strategies
# ============================================================================


async def _semantic_search_direct(
    session: Session, queries: list[dict],
) -> str:
    """Run semantic search queries concurrently, returning formatted results.
    Each query carries its own ``k`` (see ``_query_k``)."""
    ml_state = session.retrieval_state()

    # Run all queries concurrently (knn + entity retrieval in one step)
    knn_results = await asyncio.gather(
        *[_run_knn_for_query(ml_state, q) for q in queries])

    seen = session.seen_entities
    per_query_warnings = _collect_query_warnings(knn_results)
    # Collect new entities
    new_items: list[RetrievedEntity] = []
    for q, (fetched, _warnings, _error) in zip(queries, knn_results):
        for f in fetched[:_query_k(q)]:
            if f.entity.short_name in seen:
                continue
            new_items.append(f)
            seen.add(f.entity.short_name)

    if not new_items:
        lines: list[str] = ["No new relevant entities found." if seen else "No relevant entities found."]
        lines.extend(_format_warn_lines(queries, per_query_warnings))
        result = "\n".join(lines)
        session.log_tool_response(session.tool_name(TOOL_SEARCH), result)
        return result

    # Batch-fetch abbreviation definitions for unseen abbreviations
    unseen_abbrevs: list[str] = []
    for f in new_items:
        for name in f.entity.abbreviation_names:
            if name not in session.seen_abbreviations and name not in unseen_abbrevs:
                unseen_abbrevs.append(name)
    abbrev_defs: dict = {}
    if unseen_abbrevs:
        defs = await ml_state.abbreviation_defs(unseen_abbrevs)
        for name, defn in zip(unseen_abbrevs, defs):
            if defn is not None:
                abbrev_defs[name] = defn

    # Format with unified renderer
    buf = StringIO()
    retrieved: list[str] = []
    for f in new_items:
        await _format_fetched_entity(f, buf, session=session, def_info=True,
                                     potential_defs=(f.score == 1.0),
                                     abbreviation_defs=abbrev_defs)
        expr_str = _trunc_expr(', '.join(e.unicode for e in f.entity.expression))
        retrieved.append(f"{f.entity.short_name.unicode}: {expr_str}")
    for w in _format_warn_lines(queries, per_query_warnings):
        buf.write(w)
        buf.write('\n')
    if not session.seen_opaque_note and any(
            f.entity.kind in _THEOREM_KINDS and not getattr(f.entity, 'roles', [])
            for f in new_items):
        buf.write("\n[opaque] — will not be used automatically unless supplied explicitly.\n")
        session.seen_opaque_note = True
    if retrieved:
        query_str = "; ".join(_format_query_header(q) for q in queries)
        session.log_retrieval(query_str, retrieved, quiet=True)
    result = buf.getvalue().rstrip('\n')
    session.log_tool_response(session.tool_name(TOOL_SEARCH), result)
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
            file.write("\nYou are encouraged to call the query tool "
                       "to find more if none of the above is relevant.\n")
        file.write("Answer with the indices of all relevant entries.\n")


async def _semantic_search_with_filtering(session: Session, queries: list[dict]) -> str:
    """Run semantic search and spawn one sub-agent per query to filter candidates.

    Sub-agents run concurrently via ``asyncio.gather``. Each sub-agent returns
    the list of entities it selected; the parent formats them into the final
    search result string.
    """
    ml_state = session.retrieval_state()
    interactions: list[Interaction] = []
    for q in queries:
        try:
            kinds = [EntityKind.from_label(label) for label in q.get("kinds", ["constant"])]
        except KeyError:
            continue
        interaction = Interaction_RetrieveForSearch(
            state=ml_state, query=q.get("long_description", "") or "", kinds=kinds,
            initial_k=50,
            single_choice=False,
            term_patterns=q.get("term_patterns", []),
            type_patterns=q.get("type_patterns", []),
            theories_include=q.get("theories_include", []),
            name_contains=q.get("name_contains", []),
            target_type=q.get("target_type", "") or "",
        )
        interactions.append(interaction)

    if not interactions:
        return "No relevant entities found."

    _empty_msg = ("No relevant entities exist. "
        "Exhaustive search completed — you MUST consider alternative proof strategies."
        if session.interactive_retrieval == InteractiveRetrievalMode.YES_WITH_RECURSIVE_RETRIEVAL
        else "No relevant entities found.")

    seen = session.seen_entities

    results: list[list[IsabelleEntity]] = await asyncio.gather(
        *[session.fork_interaction(i) for i in interactions])

    # Build lookup from full_name → RetrievedEntity for each interaction
    fetched_maps: list[dict[str, RetrievedEntity]] = []
    for inter in interactions:
        if isinstance(inter, Interaction_Retrieve):
            candidates = await inter.candidate_facts()
            fetched_maps.append({f.entity.full_name: f for f in candidates})
        else:
            fetched_maps.append({})

    buf = StringIO()
    multi = len(results) > 1

    for q_idx, (selected, fmap) in enumerate(zip(results, fetched_maps)):
        if multi:
            buf.write(f"Query: {_format_query_header(queries[q_idx])}\n")
        indent = 1 if multi else 0

        new_fetched: list[RetrievedEntity] = []
        repeated_names: 'list[short_name]' = []
        for entity in selected:
            if entity.short_name in seen:
                repeated_names.append(entity.short_name)
            else:
                f = fmap.get(entity.full_name)
                if f is not None:
                    new_fetched.append(f)
                seen.add(entity.short_name)

        if not new_fetched and not repeated_names:
            print_indent(indent, buf)
            buf.write(f"{_empty_msg}\n")
        else:
            # Batch-fetch abbreviation definitions for unseen abbreviations
            unseen_abbrevs: list[str] = []
            for f in new_fetched:
                for name in f.entity.abbreviation_names:
                    if name not in session.seen_abbreviations and name not in unseen_abbrevs:
                        unseen_abbrevs.append(name)
            abbrev_defs: dict = {}
            if unseen_abbrevs:
                defs = await ml_state.abbreviation_defs(unseen_abbrevs)
                for name, defn in zip(unseen_abbrevs, defs):
                    if defn is not None:
                        abbrev_defs[name] = defn

            for f in new_fetched:
                await _format_fetched_entity(f, buf, indent=indent,
                                             session=session, def_info=True,
                                             potential_defs=(f.score == 1.0),
                                             abbreviation_defs=abbrev_defs)

        _format_repeated(
            [f.entity.short_name for f in new_fetched],
            repeated_names, buf, indent=indent)
        if multi:
            buf.write("\n")

    return buf.getvalue().rstrip('\n') or _empty_msg


async def _semantic_search_extend_candidates(
    session: Session, queries: list[dict], interaction: Interaction_Retrieve,
) -> str:
    """Run semantic search queries and extend the active interaction's candidate list.
    Output uses the same format as the interaction prompt, with continuing indices."""
    ml_state = session.retrieval_state()

    # Run all queries concurrently (knn + entity retrieval in one step)
    knn_results = await asyncio.gather(
        *[_run_knn_for_query(ml_state, q) for q in queries])

    per_query_warnings = _collect_query_warnings(knn_results)

    # Deduplicate against existing candidates and across queries
    existing = await interaction.candidate_facts()
    existing_names = {f.entity.full_name for f in existing}
    new_facts: list[RetrievedEntity] = []
    seen_new: set[str] = set()
    for fetched_list, _warnings, _error in knn_results:
        for f in fetched_list:
            name = f.entity.full_name
            if name in existing_names or name in seen_new:
                continue
            seen_new.add(name)
            new_facts.append(f)

    if not new_facts:
        lines: list[str] = ["No new matching entities found."]
        lines.extend(_format_warn_lines(queries, per_query_warnings))
        return "\n".join(lines)

    # Extend the interaction's candidate list
    start_idx = len(existing)
    existing.extend(new_facts)

    # Format with unified renderer (numbered for fork prompt)
    buf = StringIO()
    for i, fetched in enumerate(new_facts):
        await _format_fetched_entity(fetched, buf, prefix=f"{start_idx + i}. ")
    for w in _format_warn_lines(queries, per_query_warnings):
        buf.write(w)
        buf.write('\n')
    return buf.getvalue().rstrip('\n')


# ============================================================================
# Tool Entry Points
# ============================================================================

async def _query_entity_core(connection, tag: EntityKind, name: str,
    ctxt: Any = None,
    ) -> tuple[str, bool, 'universal_key | None']:
    """Core query logic: resolve name, look up semantic record, format.
    Returns (formatted_text, is_error, uk_or_None). Needs only a connection, no Session.
    uk is returned for callers that need to fetch definition sources."""
    try:
        uk = await universal_key_of(connection, tag, name, ctxt=ctxt)
        prefix = ""
    except UndefinedEntity:
        if "." in name:
            short = name.rsplit(".", 1)[1]
            try:
                uk = await universal_key_of(connection, tag, short, ctxt=ctxt)
                prefix = f"The {name} is undefined, but we find:\n"
            except Exception:
                return (f'Undefined: "{name}". Try query.', True, None)
        else:
            return (f'Undefined: "{name}". Try query.', True, None)
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


async def _handle_exact_term_query(session: Session, term_str: str) -> str:
    """Handle an exact_term query: parse, show unfolded form, get head semantics."""
    ml_state = session.retrieval_state()
    try:
        head_name, raw_display, normal_display = await ml_state.unfold_syntax(term_str)
    except InternalError_UnparsedTerm as e:
        return f"Failed to parse term: {pretty_unicode(e.reason)}"
    except IsabelleError as e:
        return f"Error: {'; '.join(pretty_unicode(err) for err in e.errors)}"

    buf = StringIO()
    buf.write(f"{normal_display} ≡ {raw_display}\n")

    if head_name:
        text, is_error, _uk = await _query_entity_core(
            ml_state.connection, EntityKind.CONSTANT, head_name, ctxt=ml_state.name)
        if not is_error:
            buf.write(f"Head {text}\n")
        else:
            buf.write(f"Head {head_name}\n")

    result = buf.getvalue().rstrip('\n')
    session.log_tool_response(session.tool_name(TOOL_SEARCH), result)
    return result


def _normalize_array_field(args: dict, field: str) -> dict:
    """Normalize a field that should be a list of dicts, handling common LLM malformations.

    Handles: JSON-encoded strings, single dict not wrapped in a list,
    and individual list items that are JSON strings instead of dicts.
    Raises ArgumentError on unrecoverable malformation.
    Returns a shallow copy of args with the field normalized.
    """
    value = args.get(field)
    if value is None:
        raise ArgumentError(args, f"Missing required field: {field}")

    if isinstance(value, str):
        try:
            value = json.loads(value)
        except (json.JSONDecodeError, ValueError):
            raise ArgumentError(args, f"'{field}' must be a JSON array, got an unparseable string")

    if isinstance(value, dict):
        value = [value]

    if not isinstance(value, list):
        raise ArgumentError(args, f"'{field}' must be an array, got {type(value).__name__}")

    normalized: list[dict] = []
    for i, item in enumerate(value):
        if isinstance(item, str):
            try:
                item = json.loads(item)
            except (json.JSONDecodeError, ValueError):
                raise ArgumentError(args, f"'{field}[{i}]' must be an object, got an unparseable string")
        if not isinstance(item, dict):
            raise ArgumentError(args, f"'{field}[{i}]' must be an object, got {type(item).__name__}")
        normalized.append(item)

    if not normalized:
        raise ArgumentError(args, f"'{field}' must be a non-empty array")

    return {**args, field: normalized}


async def _query_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call(session.tool_name(TOOL_SEARCH), args)
    try:
        if BATCHED_SEMANTIC_SEARCH:
            args = _normalize_array_field(args, "queries")
            queries = args["queries"]
        else:
            queries = [args]

        # Separate exact_term queries from regular queries
        exact_term_queries = [q for q in queries if q.get("exact_term")]
        regular_queries = [q for q in queries if not q.get("exact_term")]

        results: list[str] = []

        # Handle exact_term queries
        for q in exact_term_queries:
            results.append(await _handle_exact_term_query(session, q["exact_term"]))

        # Handle regular queries
        if regular_queries:
            pending = session.fork_pending
            if (pending is not None and not pending.answer.done()
                    and isinstance(pending.interaction, Interaction_Retrieve)):
                # Fork session extending its own candidate list
                results.append(await _semantic_search_extend_candidates(
                    session, regular_queries, pending.interaction))
            elif session.interactive_retrieval == InteractiveRetrievalMode.NO:
                results.append(await _semantic_search_direct(session, regular_queries))
            else:
                results.append(await _semantic_search_with_filtering(session, regular_queries))

        return ("\n\n".join(results), False)
    except ArgumentError as e:
        error_msg = str(e)
        session.log_tool_response(session.tool_name(TOOL_SEARCH), f"ERROR: {error_msg}")
        return (error_msg, True)
    except IsabelleError as e:
        error_msg = '; '.join(pretty_unicode(err) for err in e.errors)
        session.log_tool_response(session.tool_name(TOOL_SEARCH), f"ERROR: {error_msg}")
        return (error_msg, True)
    except Exception as e:
        session.log_tool_response(session.tool_name(TOOL_SEARCH), f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)
