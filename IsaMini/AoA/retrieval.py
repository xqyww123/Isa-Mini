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
    InternalError_UnparsedTerm, tn,
)


# Note appended (once per session) whenever a [manual] lemma is shown — both in
# `query` results (`_semantic_search_direct`) and the worker's "Useful lemmas"
# initial-prompt block (`Session._render_useful_lemmas`). A [manual] lemma is a
# real, in-scope theorem that carries no simp/intro/elim role, so automation
# won't apply it on its own.
MANUAL_LEMMA_NOTE = (
    "Lemmas marked with [manual] must be specified manually "
    "for Rewrite/Obvious to use them."
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
    tag = "" if (roles or f.entity.kind not in _THEOREM_KINDS) else " [manual]"
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

_KnnQueryResult = tuple[list[RetrievedEntity], list[str], str | None, int]
# (fetched, warnings, error, total) — total = entities matching the filters

def _collect_query_warnings(
    knn_results: list[_KnnQueryResult],
) -> list[list[str]]:
    """Collect warnings from each knn result into per-query lists."""
    per_query: list[list[str]] = []
    for _fetched, warnings, error, _total in knn_results:
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


def _has_structural_filter(q: dict) -> bool:
    """Whether a query carries a structural filter that makes the total match
    count (XX) meaningful. A bare semantic query (no filters) matches the whole
    corpus, so its XX is noise and omitted."""
    return bool(q.get("term_patterns") or q.get("type_patterns")
                or q.get("theories_include") or q.get("name_contains")
                or q.get("target_type"))


def _format_search_summary(q: dict, total: int, shown: int, before: int,
                           verbose: bool) -> str:
    """One-line per-query count summary: how many entities match the filters
    (XX, only when the query is filtered), how many are shown this call (YY),
    and how many were already shown in earlier calls (ZZ). The first few lines
    per session use a self-explanatory phrasing; the rest a terse one."""
    show_xx = _has_structural_filter(q)
    if verbose:
        tail = f"{shown} shown ({before} already shown earlier)."
        return f"{total} entities match the filters — {tail}" if show_xx else tail
    tail = f"{shown} shown ({before} before)."
    return f"{total} match — {tail}" if show_xx else tail


def _format_search_report(
    queries: list[dict],
    summaries: list[str],
    per_query_warnings: list[list[str]],
) -> list[str]:
    """Per-query summary line followed by that query's warnings, grouped under a
    'Query:' header when there is more than one query (mirrors
    _format_warn_lines)."""
    lines: list[str] = []
    multi = len(queries) > 1
    for q, summ, ws in zip(queries, summaries, per_query_warnings):
        if multi:
            lines.append(f"Query: {_format_query_header(q)}")
            if summ:
                lines.append(f"  {summ}")
            lines.extend(f"  {w}" for w in ws)
        else:
            if summ:
                lines.append(summ)
            lines.extend(ws)
    return lines


# ============================================================================
# KNN Query
# ============================================================================

async def _run_knn_for_query(
    ml_state: Minilang_State, q: dict,
) -> _KnnQueryResult:
    """Parse a query dict and run semantic_knn. Reads ``k`` from the query dict."""
    exact_name = q.get("exact_name") or None
    # An exact_name lookup resolves the name in one namespace chosen by `kinds`,
    # with no cross-kind fallback. When the agent omits `kinds` it would default
    # to `constant` only, so a real theorem (e.g. `card_Un_le`) is reported
    # "Undefined". Default an exact_name lookup to constant+theorem instead;
    # other kinds (type/typeclass/locale) still require an explicit `kinds`. A
    # semantic query keeps the `constant` default (consistent with the filter
    # path in `_semantic_search_with_filtering`).
    default_kinds = ["constant", "theorem"] if exact_name else ["constant"]
    try:
        kinds = [EntityKind.from_label(label) for label in (q.get("kinds") or default_kinds)]
    except KeyError as e:
        return ([], [], f"Invalid entity kind: {e}", 0)
    fetched, warnings, total = await ml_state.semantic_knn_counted(
        q.get("long_description") or None, _query_k(q), kinds,
        term_patterns=q.get("term_patterns") or [],
        type_patterns=q.get("type_patterns") or [],
        theories_include=q.get("theories_include") or [],
        name_contains=q.get("name_contains") or [],
        exact_name=exact_name,
        target_type=q.get("target_type") or "")
    return (fetched, warnings, None, total)


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


async def _render_fetched_entities(
    session: Session,
    ml_state: Minilang_State,
    entities: list[RetrievedEntity],
    buf,
    *,
    indent: int = 0,
) -> list[str]:
    """Batch-fetch abbreviation definitions for ``entities`` and render each via
    the unified ``_format_fetched_entity`` renderer (statement, ``[manual]`` tag,
    declaring definition, abbreviation expansions) into ``buf``.

    Returns the compact ``name: expr`` summary lines (used for retrieval
    logging). Shared by the ``query`` tool (``_semantic_search_direct``) and the
    worker's "Useful lemmas" prompt block (``Session._render_useful_lemmas``) so
    both print looked-up theorems identically. The caller owns any surrounding
    warnings / ``[manual]`` footer / logging."""
    # Batch-fetch abbreviation definitions for unseen abbreviations
    unseen_abbrevs: list[str] = []
    for f in entities:
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
    retrieved: list[str] = []
    for f in entities:
        await _format_fetched_entity(f, buf, indent=indent, session=session,
                                     def_info=True,
                                     potential_defs=(f.score == 1.0),
                                     abbreviation_defs=abbrev_defs)
        expr_str = _trunc_expr(', '.join(e.unicode for e in f.entity.expression))
        retrieved.append(f"{f.entity.short_name.unicode}: {expr_str}")
    return retrieved


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
    # Collect new entities, tracking per-query (total / shown / shown-before)
    # counts for the summary lines.
    new_items: list[RetrievedEntity] = []
    total_found = 0
    encountered: set[short_name] = set()
    summary_lines: list[str] = []
    for q, (fetched, _warnings, _error, total) in zip(queries, knn_results):
        k = _query_k(q)
        shown = 0   # YY: newly shown by this query
        before = 0  # ZZ: this query's top-k already shown in earlier calls
        for f in fetched[:k]:
            sn = f.entity.short_name
            if sn in encountered:
                continue
            encountered.add(sn)
            total_found += 1
            if sn in seen:
                before += 1
                continue
            new_items.append(f)
            seen.add(sn)
            shown += 1
        verbose = (session.search_summary_count + len(summary_lines)) < 5
        summary_lines.append(_format_search_summary(q, total, shown, before, verbose))

    if not new_items:
        totals = [r[3] for r in knn_results]
        if total_found == 0 and not any(totals):
            no_new_lines: list[str] = ["No relevant entities found."]
            no_new_lines.extend(_format_warn_lines(queries, per_query_warnings))
        else:
            no_new_lines = _format_search_report(queries, summary_lines, per_query_warnings)
            session.search_summary_count += len(summary_lines)
        result = "\n".join(no_new_lines)
        session.log_tool_response(session.tool_name(TOOL_SEARCH), result)
        return result

    # Format with unified renderer
    buf = StringIO()
    retrieved = await _render_fetched_entities(session, ml_state, new_items, buf)
    for line in _format_search_report(queries, summary_lines, per_query_warnings):
        buf.write(line)
        buf.write('\n')
    session.search_summary_count += len(summary_lines)
    if not session.seen_manual_note and any(
            f.entity.kind in _THEOREM_KINDS and not getattr(f.entity, 'roles', [])
            for f in new_items):
        buf.write("\n" + MANUAL_LEMMA_NOTE + "\n")
        session.seen_manual_note = True
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
            file.write(f"\nYou are encouraged to call the `{tn(TOOL_SEARCH)}` tool "
                       "to find more if none of the above is relevant.\n")
        file.write("Answer with the indices of all relevant entries.\n")


async def _semantic_search_with_filtering(session: Session, queries: list[dict]) -> str:
    """Run semantic search and spawn one sub-agent per query to filter candidates.

    Sub-agents run concurrently via ``asyncio.gather``. Each sub-agent returns
    the list of entities it selected; the parent formats them into the final
    search result string.

    ``exact_name`` queries are NOT fork-filtered (there is nothing to choose once
    the name is known): they are routed through the direct path
    (``_semantic_search_direct``, as in NO mode), which honours ``exact_name`` and
    surfaces its warnings (e.g. ``Undefined: "<name>"``). Only the remaining
    queries get the fork-filtering treatment.
    """
    ml_state = session.retrieval_state()
    exact_queries = [q for q in queries if q.get("exact_name")]
    filter_queries = [q for q in queries if not q.get("exact_name")]
    exact_result = (await _semantic_search_direct(session, exact_queries)
                    if exact_queries else None)

    interactions: list[Interaction] = []
    for q in filter_queries:
        try:
            kinds = [EntityKind.from_label(label) for label in (q.get("kinds") or ["constant"])]
        except KeyError:
            continue
        interaction = Interaction_RetrieveForSearch(
            state=ml_state, query=q.get("long_description", "") or "", kinds=kinds,
            initial_k=50,
            single_choice=False,
            term_patterns=q.get("term_patterns") or [],
            type_patterns=q.get("type_patterns") or [],
            theories_include=q.get("theories_include") or [],
            name_contains=q.get("name_contains") or [],
            target_type=q.get("target_type") or "",
        )
        interactions.append(interaction)

    if not interactions:
        return exact_result if exact_result is not None else "No relevant entities found."

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

    filter_result = buf.getvalue().rstrip('\n') or _empty_msg
    return (f"{exact_result}\n\n{filter_result}"
            if exact_result is not None else filter_result)


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
    for fetched_list, _warnings, _error, _total in knn_results:
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


# Per-query fields that the tool schema declares as arrays of strings. The ML
# entity-enumeration callbacks unpack these with `unpackList unpackString`
# (contrib/Isabelle_RPC/Tools/context.ML), so a scalar value sent by the LLM
# (e.g. name_contains="iff" instead of ["iff"]) makes the msgpack arg fail to
# unpack -> "Failed to unpack callback argument". Normalize before dispatch.
_QUERY_STRING_LIST_FIELDS = (
    "kinds", "term_patterns", "type_patterns", "theories_include", "name_contains",
)


def _normalize_query_string_list_fields(q: dict) -> dict:
    """Coerce the array-of-string query fields into actual lists of strings.

    Tolerates the common LLM malformation of passing a bare scalar (or a
    JSON-encoded array string) where the schema requires an array — mirroring
    ``_normalize_array_field``'s single-value-to-list handling. ``None`` /
    missing are left untouched (callers already default them via ``or []``).
    Returns a shallow copy with the affected fields normalized."""
    out = dict(q)
    for field in _QUERY_STRING_LIST_FIELDS:
        if field not in out:
            continue
        value = out[field]
        if value is None or isinstance(value, list):
            continue
        if isinstance(value, str):
            try:
                parsed = json.loads(value)
            except (json.JSONDecodeError, ValueError):
                parsed = None
            out[field] = parsed if isinstance(parsed, list) else [value]
        else:
            # Any other scalar (int/bool/…): wrap so packing as a list succeeds.
            out[field] = [value]
    return out


def _parenthesize_query_term_strings(q: dict) -> dict:
    """Wrap the query's *term*-valued fields in parentheses so a bare operator
    parses.

    A pattern like ``≤`` / ``<`` / ``*`` is not a parseable term on its own,
    but Isabelle reads the parenthesized operator section ``(≤)`` as the
    underlying constant (which then matches the operator wherever it occurs in a
    proposition, even partially applied). For any already-valid term ``t``,
    ``(t)`` parses to the identical term — outer parens are pure grouping —
    so wrapping is a no-op for normal patterns and only rescues bare operators.

    Only the two term-valued query fields are touched: ``term_patterns`` (list)
    and ``exact_term`` (scalar). ``type_patterns`` / ``target_type`` are *types*,
    and the name/description/theory fields are never parsed as terms, so they are
    left untouched. Must run after ``_normalize_query_string_list_fields`` so
    ``term_patterns`` is already coerced to a list. Empty/blank entries are
    dropped (``()`` would not parse)."""
    out = dict(q)
    tps = out.get("term_patterns")
    if isinstance(tps, list):
        out["term_patterns"] = [
            f"({p.strip()})" for p in tps if isinstance(p, str) and p.strip()]
    et = out.get("exact_term")
    if isinstance(et, str) and et.strip():
        out["exact_term"] = f"({et.strip()})"
    return out


async def _query_tool_logic(session: Session, args: dict) -> tuple[str, bool]:
    session.log_tool_call(session.tool_name(TOOL_SEARCH), args)
    try:
        if BATCHED_SEMANTIC_SEARCH:
            args = _normalize_array_field(args, "queries")
            queries = args["queries"]
        else:
            queries = [args]

        # Coerce array-of-string fields the LLM may have sent as scalars, so
        # they survive the ML callbacks' `unpackList unpackString` arg schema.
        queries = [_normalize_query_string_list_fields(q) for q in queries]
        # Parenthesize the term-valued fields (term_patterns, exact_term) so bare
        # operators like `≤` / `<` / `*` parse: Isabelle reads `(≤)` as the
        # operator constant, and `(t)` == `t` for any already-valid term, so this
        # is a no-op for normal patterns.
        queries = [_parenthesize_query_term_strings(q) for q in queries]

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
    except (ConnectionError, EOFError):
        raise asyncio.CancelledError("connection lost")
    except Exception as e:
        session.log_tool_response(session.tool_name(TOOL_SEARCH), f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
        sys.exit(1)
