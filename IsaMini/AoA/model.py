import asyncio
import contextlib
import re
from time import time
from datetime import datetime
from io import StringIO
from pathlib import Path
from .helper import split_id_into_segs, cat_segs_into_id, incr_id_major, incr_id_minor, local_step_between, MyIO
from .linked_list import Cons, LinkedList, from_iterable, iterate, concat
from . import config
import types as _types
from typing import Any, Awaitable, ClassVar, Iterable, Mapping, NamedTuple, Protocol, Sequence, TypedDict, Callable, cast, Type, Literal, NotRequired, TypeAliasType, Union, get_type_hints, get_origin, get_args, is_typeddict, TYPE_CHECKING
from Isabelle_RPC_Host import Connection, IsabelleError, pretty_unicode, ascii_of_unicode
from Isabelle_RPC_Host.position import IsabellePosition
from Isabelle_RPC_Host.universal_key import (
    EntityKind, universal_key, universal_key_of, universal_key_and_name_of,
    key_of_theorems, UndefinedEntity,
)
from Isabelle_Semantic_Embedding.semantics import Semantic_Vector_Store, SemanticRecord, trunc_expr as _trunc_expr_base

# Max number of members shown when an exact_name lookup hits a multi-theorem
# fact (a bundle); any beyond this are summarised with a "use foo(k)…" note.
EXACT_NAME_BUNDLE_LIMIT = 20

if TYPE_CHECKING:
    # `LMDriver` (the session/driver base) lives in `language_model_driver`, which
    # imports `Session` from this module — so a runtime import would be circular.
    # The annotations that reference it are string forward-refs; this guarded
    # import only feeds the type checker and runs no code at import time.
    from .language_model_driver import LMDriver

AGENT_EXPR_LIMIT = 200
AGENT_GOAL_CHAR_LIMIT = 400

LONG_GOAL_HINT = (
    "note: the resulting goal is unusually long, "
    "which is often a sign of a wrong direction.\n"
)

def _clean_warning(w: str) -> str:
    s = pretty_unicode(w)
    if s.startswith("Ambiguous input"):
        first = s.split('\n', 1)[0]
        first = re.sub(r'\s*\(\d+ displayed\)', '', first)
        return first.rstrip(':')
    return s

def trunc_expr(s: 'str | IsaTerm') -> str:
    return _trunc_expr_base(s.unicode if isinstance(s, IsaTerm) else s, AGENT_EXPR_LIMIT)
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum, auto
import json
import logging
import os
import sqlite3
import sys
import yaml
import platformdirs
from io import StringIO

class IsaTerm:
    """Dual-representation Isabelle string: Unicode (for LLM display) + ASCII (for Isabelle RPC).

    Constructed at two boundaries:
    - ``IsaTerm.from_isabelle(ascii_str)`` — when data arrives from Isabelle RPC
    - ``IsaTerm.from_agent(unicode_str)`` — when the LLM provides a term via tool calls
    """
    __slots__ = ('unicode', 'ascii')

    def __init__(self, unicode: str, ascii: str):
        self.unicode = unicode
        self.ascii = ascii

    @classmethod
    def from_isabelle(cls, ascii_str: str) -> 'IsaTerm':
        """Create from Isabelle RPC output (ASCII notation)."""
        return cls(pretty_unicode(ascii_str), ascii_str)

    @classmethod
    def from_agent(cls, unicode_str: str) -> 'IsaTerm':
        """Create from LLM/agent input (Unicode)."""
        return cls(unicode_str, ascii_of_unicode(unicode_str))

    def __str__(self) -> str:
        raise TypeError(
            "str() on IsaTerm is ambiguous — use .unicode (for display) or .ascii (for Isabelle RPC) explicitly")
    def __repr__(self) -> str: return f'IsaTerm({self.unicode!r})'

    @staticmethod
    def to_unicode(x: Any) -> str:
        """Display (Unicode) string of *any* value, resolving an ``IsaTerm``
        via ``.unicode``.

        The sanctioned way to stringify a value of statically-unknown type at
        a generic display / logging sink (e.g. an ``Interaction.answer()``
        result, which is one of several payload types and is occasionally a
        bare ``IsaTerm``).  A plain ``str(x)`` / f-string there would trip the
        deliberately-forbidden ``IsaTerm.__str__``; this routes an ``IsaTerm``
        to ``.unicode`` instead.  ``None`` renders as the empty string; every
        other non-``IsaTerm`` value falls back to ``str(x)`` (containers are
        safe — they format their elements via ``repr``, and
        ``IsaTerm.__repr__`` is safe)."""
        if x is None:
            return ""
        if isinstance(x, IsaTerm):
            return x.unicode
        return str(x)

    @staticmethod
    def to_ascii(x: Any) -> str:
        """ASCII (Isabelle-RPC) string of *any* value, resolving an ``IsaTerm``
        via ``.ascii`` — the wire-boundary counterpart of ``to_unicode``.

        A non-``IsaTerm`` value is assumed to be a Unicode string and is
        converted with ``ascii_of_unicode`` (a no-op on already-ASCII text);
        ``None`` renders as the empty string."""
        if x is None:
            return ""
        if isinstance(x, IsaTerm):
            return x.ascii
        return ascii_of_unicode(x if isinstance(x, str) else str(x))

    def __hash__(self) -> int: return hash(self.ascii)
    def __eq__(self, other) -> bool:
        if isinstance(other, IsaTerm): return self.ascii == other.ascii
        if isinstance(other, str): return self.ascii == other
        return NotImplemented
    def __len__(self) -> int: return len(self.unicode)
    def __lt__(self, other) -> bool:
        if isinstance(other, IsaTerm): return self.ascii < other.ascii
        if isinstance(other, str): return self.ascii < other
        return NotImplemented

# Internal dual-representation types (carry both Unicode and ASCII)
type varname = IsaTerm
type varname_spec = varname | None # underscore '_' is represented as None
type typ = IsaTerm
type term = IsaTerm

# External types (raw Unicode strings from LLM tool calls, before wrapping)
type xterm = str
type xtyp = str
type xvarname = str
type xname = str

type full_name = str   # Isabelle internal name, always ASCII
type name = IsaTerm    # Isabelle name (short or full), dual-representation
type short_name = IsaTerm  # Display name, dual-representation

type lambda_term = Any
type step = str
type local_step = str
type case_name = local_step
type Var = tuple[varname, typ]
type Hyp = tuple[varname, term]
type Vars = dict[varname, typ]
type Hyps = dict[varname, term]
type TVars = dict[varname, typ]
# `ToolCall_arg` — the generic shape of any ToolCall argument dict sent by
# the agent.  `Mapping[str, Any]` rather than `dict[str, Any]` so TypedDict
# subclasses are assignable (TypedDicts are NOT pyright-subtypes of `dict`
# but ARE of `Mapping[str, object]` / `Mapping[str, Any]`).
type ToolCall_arg = Mapping[str, Any]
# `raw_op` (type alias): a single raw proof-operation dict as received from
# the agent — same shape as `ToolCall_arg`, named distinctly to signal "one
# raw proof op" in the parsing pipeline.
type raw_op = ToolCall_arg
# `raw_proof` (type alias): an ordered list of raw operation dicts as
# received from the agent, BEFORE parsing via `Parse_Nodes`.  Used only in
# `*_ToolArg` field types (schema-level shape); node instance fields never
# hold `raw_proof` — they hold the parsed `proof` (list of `Parsed_Opr`)
# instead.  Optionality (absence of a proof body) is expressed by
# `NotRequired[raw_proof | None]` at the ToolArg level and by
# `proof | None` on instance fields.
type raw_proof = list[raw_op]


class Explicit_Var(TypedDict):
    name: xvarname
    type: NotRequired[xtyp | None]

class FactByProposition(TypedDict):
    proposition: xterm

class FactByDescription(TypedDict):
    english: str

class Instantiation(TypedDict):
    name: str
    value: xterm

class FactByName(TypedDict):
    name: xname
    instantiations: NotRequired[list[Instantiation]]
    discharge: NotRequired[list['FactByName | None']]
    flip: NotRequired[bool]

type Fact = FactByName | FactByProposition | FactByDescription

def fact_kind(fact: Fact) -> Literal["name", "proposition", "description"]:
    if "name" in fact:
        return "name"
    if "proposition" in fact:
        return "proposition"
    return "description"

# The clauses below return the *bracket-less* attribute text; `_fact_suffix`
# assembles the non-empty ones into a SINGLE comma-separated `[...]` group.
# Display uses `where`/`OF`/`symmetric`; `for_pack=True` emits `xwhere`/`xOF`/
# `xsymmetric` for `read_fact`'s `Parse.thm`, which accepts only one attribute
# bracket group (`Scan.optional attribs`, no `Scan.repeat`) — merging into a
# single `[...]` preserves the where→OF→symmetric order.
def _where_clause(fact: Fact, *, for_pack: bool = False) -> str:
    if "name" not in fact:
        return ""
    insts = cast(FactByName, fact).get("instantiations", [])
    if not insts:
        return ""
    where_parts = " and ".join(
        f"{i['name']} = \N{SINGLE LEFT-POINTING ANGLE QUOTATION MARK}{i['value']}\N{SINGLE RIGHT-POINTING ANGLE QUOTATION MARK}"
        for i in insts)
    keyword = "xwhere" if for_pack else "where"
    return f"{keyword} {where_parts}"

def _of_clause(fact: Fact, *, for_pack: bool = False) -> str:
    if "name" not in fact:
        return ""
    discharge = cast(FactByName, fact).get("discharge", [])
    if not discharge:
        return ""
    while discharge and discharge[-1] is None:
        discharge = discharge[:-1]
    if not discharge:
        return ""
    of_parts = []
    for item in discharge:
        if item is None:
            of_parts.append("_")
        else:
            of_parts.append(item["name"] + _fact_suffix(item, for_pack=for_pack))
    keyword = "xOF" if for_pack else "OF"
    return keyword + " " + " ".join(of_parts)

def _symmetric_clause(fact: Fact, *, for_pack: bool = False) -> str:
    if "name" not in fact:
        return ""
    if cast(FactByName, fact).get("flip", False):
        return "xsymmetric" if for_pack else "symmetric"
    return ""

def _fact_suffix(fact: Fact, *, for_pack: bool = False) -> str:
    clauses = [c for c in (_where_clause(fact, for_pack=for_pack),
                           _of_clause(fact, for_pack=for_pack),
                           _symmetric_clause(fact, for_pack=for_pack)) if c]
    return f"[{', '.join(clauses)}]" if clauses else ""

class FailureReason(NamedTuple):
    """A human-readable failure reason, used in Interaction.answer() returns
    and Leaf.the_operation() returns."""
    reason: str


class IsabelleEntity:
    """A resolved Isabelle entity (constant, type, class, locale, etc.) with display info."""
    __slots__ = ('full_name', 'short_name', 'expression', 'kind', 'roles', 'abbreviation_names')
    full_name: 'full_name'
    short_name: 'short_name'
    expression: list[term]
    kind: EntityKind
    roles: list[str]
    abbreviation_names: 'list[full_name]'
    def __init__(self, full_name: 'full_name', short_name: 'short_name', expression: list[term],
                 kind: EntityKind, roles: list[str] = [],
                 abbreviation_names: 'list[full_name]' = []):
        self.full_name = full_name
        self.short_name = short_name
        self.expression = expression
        self.kind = kind
        self.roles = roles
        self.abbreviation_names = abbreviation_names

class RetrievedEntity(NamedTuple):
    """Result of semantic search: an entity with its similarity score and interpretation."""
    entity: IsabelleEntity
    score: float              # semantic similarity score
    interpretation: str | None  # human-readable description from SemanticRecord
    # Heading line printed above the interpretation, for abbreviation constants
    # hit by exact_name lookups ("Abbreviation constant ..." / "Raw constant ...").
    # None everywhere else (KNN / pattern paths never set it).
    semantics_heading: str | None = None
    # True for a member surfaced by expanding a multi-theorem fact (bundle) via
    # exact_name: the renderer skips the per-member declaring-definition fetch
    # (they share one `lemmas`/`fun` declaration — fetching it per member is
    # wasteful and, for fun/.simps bundles, repeats the same source N times).
    suppress_def: bool = False

class IsabelleFact(ABC):
    """A fact referenced in proof operations.

    Instances are immutable by convention (not runtime-enforced):
    "updating" a fact means constructing a new instance, e.g. via
    Minilang_State.refresh_facts.
    """
    @abstractmethod
    def name(self) -> 'short_name | term': ...
    @abstractmethod
    def print(self, indent: int, file: MyIO) -> None: ...
    @abstractmethod
    def pack(self) -> Any:
        """Pack for RPC. Returns the packed form, or FailureReason on error."""
        ...
    def __repr__(self) -> str:
        return self.name().unicode

class IsabelleFact_Presented(IsabelleFact, IsabelleEntity):
    """A resolved fact with full information from Isabelle. `kind` must be
    theorem-like (see _THEOREM_KINDS). `is_local` is True iff the fact
    lives only in the current proof context (assms, IH, named `have`),
    not in the global theory namespace — used by the Induction tool's
    `facts_to_generalize` filter."""
    __slots__ = ('fact', 'is_local', 'is_conditional')
    def __init__(self, full_name: 'full_name', short_name: 'short_name', fact: Fact, expression: list[term],
                 kind: EntityKind = EntityKind.THEOREM, roles: list[str] = [],
                 abbreviation_names: 'list[full_name]' = [],
                 is_local: bool = False, is_conditional: bool = False):
        assert kind in _THEOREM_KINDS, \
            f"IsabelleFact_Presented requires a theorem-like kind, got {kind}"
        self.full_name = full_name
        self.short_name = short_name
        self.fact = fact
        self.expression = expression
        self.kind = kind
        self.roles = roles
        self.abbreviation_names = abbreviation_names
        self.is_local = is_local
        # True iff the fact carries a premise (Pure ⟹ or leading object ⟶), so an
        # Unfold using it may silently no-op. Sourced from the potential_defs_of
        # callback's flag; preserved across refresh_facts and re-resolution.
        self.is_conditional = is_conditional
    def name(self) -> 'short_name':
        suffix = _fact_suffix(self.fact)
        if suffix:
            return IsaTerm.from_agent(self.short_name.unicode + suffix)
        return self.short_name
    def print(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        display_name = self.short_name.unicode + _fact_suffix(self.fact)
        if len(self.expression) == 1:
            file.write(f"- {display_name}: {self.expression[0].unicode}\n")
        elif len(self.expression) > 1:
            file.write(f"- {display_name}:\n")
            for expr in self.expression[:MAX_EXPR_ITEMS]:
                print_indent(indent + 1, file)
                file.write(f"  {expr.unicode}\n")
            if len(self.expression) > MAX_EXPR_ITEMS:
                print_indent(indent + 1, file)
                file.write(f"  ... ({len(self.expression)} facts total)\n")
        else:
            file.write(f"- {display_name}\n")
    def pack(self) -> tuple[str, str | None]:
        suffix = _fact_suffix(self.fact, for_pack=True)
        if suffix:
            suffix = ascii_of_unicode(suffix)
        return (self.full_name + suffix, None)

class IsabelleFact_ProveInTime(IsabelleFact):
    """A fact to be proven just-in-time by Isabelle."""
    __slots__ = ('statement', 'assigned_name')
    def __init__(self, statement: term, assigned_name: str):
        self.statement = statement
        self.assigned_name = assigned_name
    def name(self) -> 'term':
        return self.statement
    def print(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        file.write(f"- {self.statement.unicode}\n")
    def pack(self) -> tuple[str, str | None]:
        return (self.assigned_name, self.statement.ascii)

class IsabelleFact_Unfound(IsabelleFact):
    """A fact that could not be found in the Isabelle context."""
    __slots__ = ('fact',)
    def __init__(self, fact: Fact):
        self.fact = fact
    def name(self) -> 'short_name | term':
        match fact_kind(self.fact):
            case "name": return IsaTerm.from_agent(cast(FactByName, self.fact)["name"] + _fact_suffix(self.fact))
            case "proposition": return IsaTerm.from_agent(cast(FactByProposition, self.fact)["proposition"])
            case "description": return IsaTerm.from_agent(cast(FactByDescription, self.fact)["english"])
    def print(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        file.write(f"- Error: fact \"{self.name().unicode}\" not found\n")
    def pack(self) -> Any:
        raise InternalError(f"Attempting to pack an unfound fact \"{self.name().unicode}\". "
                            "Unfound facts should be filtered out before packing.")


class Context(NamedTuple):
    vars: Vars
    tvars: TVars
    hyps: Hyps

    @classmethod
    def unpack(cls, data) -> 'Context':
        (vars, tvars, hyps) = data
        vars = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in vars.items()}
        tvars = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in tvars.items()}
        hyps = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in hyps.items()}
        return cls(vars, tvars, hyps)
    def __str__(self) -> str:
        vs = ", ".join(f"{k.unicode}: {v.unicode}" for k, v in self.vars.items())
        ts = ", ".join(f"{k.unicode}: {v.unicode}" for k, v in self.tvars.items())
        hs = ", ".join(f"{k.unicode}: {v.unicode}" for k, v in self.hyps.items())
        return f"{{{vs}}}, tvars={{{ts}}}, {{{hs}}}"

class Goal(NamedTuple):
    context: Context
    conclusion: term

    @classmethod
    def unpack(cls, data) -> 'Goal':
        (context, conclusion) = data
        conclusion = IsaTerm.from_isabelle(conclusion)
        return cls(Context.unpack(context), conclusion)
    def visible(self, suppressed: Context) -> 'Goal':
        """Return a Goal with suppressed vars/hyps/tvars removed."""
        return Goal(
            Context(
                {k: v for k, v in self.context.vars.items() if k not in suppressed.vars},
                {k: v for k, v in self.context.tvars.items() if k not in suppressed.tvars},
                {k: v for k, v in self.context.hyps.items() if k not in suppressed.hyps},
            ),
            self.conclusion
        )
    def __str__(self) -> str:
        return f"{self.context} ⊢ {self.conclusion.unicode}"
    def __repr__(self) -> str:
        return self.__str__()

class Goals(NamedTuple):
    context: Context
    goals: list[Goal]

    @classmethod
    def unpack(cls, data) -> 'Goals':
        (context, goals) = data
        return cls(Context.unpack(context), [Goal.unpack(goal) for goal in goals])
    def __str__(self) -> str:
        goals_str = ", ".join(g.conclusion.unicode for g in self.goals)
        return f"{self.context} ⊢ [{goals_str}]"

def print_indent(indent: int, file):
    for _ in range(indent):
        file.write("  ")

def print_paragraph(indent: int, file: MyIO | StringIO, para: str):
    lines = para.strip().split("\n")
    match lines:
        case [line]:
            file.write(" ")
            file.write(line)
            file.write("\n")
        case lines:
            file.write(" |\n")
            for line in lines:
                print_indent(indent+1, file)
                file.write(line)
                file.write("\n")

MAX_EXPR_ITEMS = 8

def print_expression_list(indent: int, file: MyIO | StringIO,
                          expressions: list[term]) -> bool:
    """Render the expression(s) that follow a trailing ``:`` on the
    previous line, individually length-truncated.

    - 1 expression: inline via ``print_paragraph`` on the same line.
    - >1 expressions: bulleted list, one per line, with ``...`` after
      ``MAX_EXPR_ITEMS`` items.

    Returns True if any content was truncated (by length or item count)."""
    if len(expressions) == 1:
        truncated = trunc_expr(expressions[0])
        print_paragraph(indent, file, truncated)
        return truncated.endswith("…")
    any_truncated = False
    file.write("\n")
    for expr in expressions[:MAX_EXPR_ITEMS]:
        line = trunc_expr(expr)
        if line.endswith("…"):
            any_truncated = True
        print_indent(indent, file)
        file.write("- ")
        file.write(line)
        file.write("\n")
    if len(expressions) > MAX_EXPR_ITEMS:
        print_indent(indent, file)
        file.write("...\n")
        any_truncated = True
    return any_truncated

def print_vars(vars: Iterable[tuple[varname, typ]], indent: int, file, suppressed: Vars, banner='variables'):
    printed_banner = False
    for name, type in vars:
        if name in suppressed:
            continue
        if not printed_banner:
            print_indent(indent, file)
            file.write(banner)
            file.write(":\n")
            printed_banner = True
        print_indent(indent+1, file)
        file.write(f"- {name.unicode}: {type.unicode}\n")

def print_type_vars(tvars: Iterable[tuple[varname, typ]], indent: int, file, suppressed: TVars, banner='type variables'):
    printed_banner = False
    for name, sort in tvars:
        if name in suppressed:
            continue
        if not printed_banner:
            print_indent(indent, file)
            file.write(banner)
            file.write(":\n")
            printed_banner = True
        print_indent(indent+1, file)
        file.write(f"- {name.unicode}: {sort.unicode}\n")

def print_hyps(hyps: Iterable[tuple[varname, term]], indent: int, file, suppressed: Hyps, banner='premises'):
    printed_banner = False
    for name, term in hyps:
        if name in suppressed:
            continue
        if not printed_banner:
            print_indent(indent, file)
            file.write(banner)
            file.write(":\n")
            printed_banner = True
        print_indent(indent+1, file)
        file.write(f"- {name.unicode}: {term.unicode}\n")

def print_goal(goal: Goal, indent: int, show_header: bool, file, suppressed: Context,
               truncate: bool = False):
    print_vars(goal.context.vars.items(), indent, file, suppressed.vars)
    print_type_vars(goal.context.tvars.items(), indent, file, suppressed.tvars)
    print_hyps(goal.context.hyps.items(), indent, file, suppressed.hyps)
    print_indent(indent, file)

    conclusion_str = goal.conclusion.unicode
    was_truncated = False
    if truncate and len(conclusion_str) > AGENT_GOAL_CHAR_LIMIT:
        conclusion_str = _trunc_expr_base(conclusion_str, AGENT_GOAL_CHAR_LIMIT)
        was_truncated = True

    if any(name not in suppressed.vars for name in goal.context.vars) or\
        any(name not in suppressed.tvars for name in goal.context.tvars) or\
        any(name not in suppressed.hyps for name in goal.context.hyps):
        file.write(f"goal: {conclusion_str}\n")
    else:
        if show_header:
            file.write("goal: ")
        file.write(conclusion_str)
        file.write("\n")

    if was_truncated:
        print_indent(indent, file)
        file.write(LONG_GOAL_HINT)

def print_pending_goal(goal: Goal, step: step, indent: int, file : MyIO, suppressed: Context,
                       show_goal: bool = True, replace_existing: bool = False) -> int:
    line = file.current_line()
    print_indent(indent, file)
    shown_step = the_session()._display_id(step)
    if replace_existing:
        file.write(f"Unfinished Proof! Call command `edit` with action `fill` and target step `{shown_step}`"
            " to replace it with a proof.\n")
    elif show_goal:
        file.write(f"Unfinished Proof! Call command `edit` with action `fill` and target step `{shown_step}`"
            " to provide the proof for the following goal.\n")
    else:
        file.write(f"Unfinished Proof! Call command `edit` with action `fill` and target step `{shown_step}`"
            " to provide the proof.\n")
    if show_goal:
        print_indent(indent, file)
        file.write("pending proof goal:\n")
        print_goal(goal, indent+1, False, file, suppressed)
    return line

def string_of_and_list(l: list[Any]) -> str:
    def _s(x):
        return x.unicode if isinstance(x, IsaTerm) else str(x)
    match l:
        case []:
            return ""
        case [a]:
            return _s(a)
        case [a, b]:
            return f"{_s(a)} and {_s(b)}"
        case [*rest, last]:
            return ", ".join(_s(x) for x in rest) + f", and {_s(last)}"
        case _:
            raise ValueError(f"Impossible")
def titled_string_of_and_list(l: list[Any], singular: str, plural: str) -> str:
    if len(l) == 1:
        return f"{singular} {string_of_and_list(l)}"
    else:
        return f"{plural} {string_of_and_list(l)}"


## Errors
type timedelta = float # in seconds

class AoA_Error(Exception):
    pass


# --- Quit reasons (per-session ADT) ----------------------------------------
# Why a session's agent loop stopped without finishing the proof. Stored on
# ``Session.quit_info`` — each session owns its own; never shared via ``Root``.
# The major/planner session's value is what ``toplevel`` reports to ML; a
# fork's value dies with the fork. ``reason`` strings are the ML-facing codes.
@dataclass
class ResourceExhausted:
    reason: ClassVar[str] = "resource_exhausted"
    is_terminal: ClassVar[bool] = True
    detail: str | None = None

@dataclass
class ResourceUnavailable:
    # The LM backend itself could not be reached/used (infrastructure failure,
    # e.g. the openai-oauth proxy is down or its ChatGPT credentials expired) —
    # distinct from ResourceExhausted (budget/token/retry limits used up). Set by
    # the driver/executor when ``LMUnreachable`` is caught (see driver_api).
    reason: ClassVar[str] = "resource_unavailable"
    is_terminal: ClassVar[bool] = True
    detail: str | None = None

@dataclass
class Surrender:
    reason: ClassVar[str] = "surrender"
    is_terminal: ClassVar[bool] = True
    detail: str | None = None

@dataclass
class Refute:
    reason: ClassVar[str] = "refute"
    is_terminal: ClassVar[bool] = True
    detail: str | None = None

@dataclass
class Restart:
    reason: ClassVar[str] = "restart"
    is_terminal: ClassVar[bool] = False
    detail: str | None = None

@dataclass
class Refresh:
    reason: ClassVar[str] = "refresh"
    is_terminal: ClassVar[bool] = False
    briefing: str = ""
    detail: str | None = None

QuitInfo = ResourceExhausted | ResourceUnavailable | Surrender | Refute | Restart | Refresh


class DriverArgumentError(AoA_Error):
    pass


class OprError(AoA_Error):
    pass


class LMUnreachable(AoA_Error):
    """The LM backend could not be reached/used (e.g. the openai-oauth proxy is
    down, or its ChatGPT subscription credentials expired). Raised in-band by a
    Provider's ``chat`` (a Provider cannot set ``quit_info`` itself); the driver
    (``_api_loop``) and the tool executor (``ToolExecutor.execute``) catch it and
    convert it to ``quit_info = ResourceUnavailable`` so the proof gives up
    cleanly instead of an exception escaping (a fork's would hit
    ``execute``'s ``sys.exit(1)`` and kill the host)."""
    pass

class EditOperation(Enum):
    """Top-level edit actions exposed to the agent."""
    FILL = "fill"
    INSERT = "insert_before"
    AMEND = "amend"


class EditFailureBehavior(Enum):
    """What `_on_edit_failure` tells the edit method to do after a
    committed node resolves to FAILURE on refresh."""
    CONTINUE = "continue"                  # batch continues, node stays in tree
    TERMINATE = "terminate"                # batch stops, node stays in tree
    TERMINATE_AND_REVERT = "terminate_and_revert"  # batch stops, node deleted from tree


class CannotEdit(AoA_Error):
    """Unified failure carrier for fill/insert_before/amend.

    Subclasses supply ONLY their specific cause via `_reason()`; the base
    `__str__` owns the full-vs-partial framing:
      - full failure (`is_error`, nothing committed): the action could not be
        performed at all → "Cannot fill a node with id X\n<reason>".
      - partial apply (`not is_error`, some ops committed): the batch advanced
        but stopped at one operation → "While filling step X, could not apply
        operation #N (Kind); it and K later operations were left unapplied:
        <reason>".
    """
    # Present-participle of each action, for the partial-apply framing.
    _VERB_ING = {
        EditOperation.FILL: "filling",
        EditOperation.INSERT: "inserting before",
        EditOperation.AMEND: "amending",
    }

    def __init__(self,
                 target_step: step,
                 operation: 'EditOperation | None' = None,
                 unapplied_oprs: 'list[Parsed_Opr] | None' = None,
                 is_error: bool = True,
                 failed_opr: 'Parsed_Opr | None' = None,
                 failed_index: 'int | None' = None):
        # `operation` is None when raised from a node factory (only site:
        # Obvious → GoalIsNontrivial); the enclosing edit method fills it
        # in at catch time.
        # `is_error` is the tool-call error flag surfaced to the agent. Callers
        # set it `len(outcome.committed) == 0`: True when nothing committed (the
        # whole edit failed → full framing); False on a partial apply (some ops
        # committed, the rest left in `unapplied_oprs` → partial framing).
        # `failed_opr` / `failed_index` identify the operation the batch could
        # not apply (== `unapplied_oprs[0]`, the 0-based `failed_index`-th item
        # of the original request). Read only by the partial framing.
        self.target_step = target_step
        self.operation = operation
        self.unapplied_oprs = list(unapplied_oprs) if unapplied_oprs else []
        self.is_error = is_error
        self.failed_opr = failed_opr
        self.failed_index = failed_index

    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        """The specific cause of this failure, one self-contained sentence.
        Implemented by every subclass; framed (full vs partial) by `render`.

        Subclasses store node ids ABSOLUTE (the tree's namespace) and project
        them to the caller's namespace here, using `display_id` for a bare id
        field (e.g. `closed_by`) and `relativize_text` for free text that may
        embed `step …`/`goal …` references (e.g. an evaluation failure blob).
        Both are the identity for a non-worker session."""
        raise NotImplementedError(
            f"{type(self).__name__} must implement `_reason`")

    def _action_phrase(self, shown: 'step') -> str:
        """Full-failure lead: the action could not be performed at all. `shown`
        is `target_step` already projected into the caller's namespace."""
        match self.operation:
            case EditOperation.FILL:
                return (f"Cannot fill a node with id {shown}"
                        if shown else "Cannot fill this step")
            case EditOperation.INSERT:
                return (f"Cannot insert before the node {shown}"
                        if shown else "Cannot insert before this step")
            case EditOperation.AMEND:
                return (f"Cannot amend the node {shown}"
                        if shown else "Cannot amend this step")
            case _:
                raise InternalError(
                    f"CannotEdit._action_phrase: unknown operation {self.operation!r}")

    def _partial_phrase(self, shown: 'step') -> str:
        """Partial-apply lead: the batch committed some ops, then stopped at
        `failed_opr`; name it, its 1-based position, and how many ops dropped.
        `shown` is `target_step` already projected into the caller's namespace."""
        op = self.operation
        verb = self._VERB_ING.get(op, "editing") if op is not None else "editing"
        op_name = (OPERATION_REGISTRY_BY_CLS.get(
                       self.failed_opr.cls, self.failed_opr.cls.__name__)
                   if self.failed_opr is not None else "?")
        pos = f"#{self.failed_index + 1} " if self.failed_index is not None else ""
        later = len(self.unapplied_oprs) - 1
        tail = (f"; it and {later} later operation{'s' if later != 1 else ''} "
                f"were left unapplied") if later > 0 else ""
        return (f"While {verb} step {shown}, could not apply "
                f"operation {pos}({op_name}){tail}")

    def render(self, display_id: 'Callable[[str], str]',
               relativize_text: 'Callable[[str], str]') -> str:
        """Render for an agent. Every node id this message exposes is projected
        from the absolute tree namespace into the caller's namespace via the two
        mappers (`Session._display_id` / `Session._postprocess_outbound_text`): a worker
        sees ids relative to its scope, everyone else sees them unchanged. This
        is the single id-translation boundary for an edit failure — the stored
        fields stay absolute (see model.py's worker-scoped-id design note)."""
        shown = display_id(self.target_step) if self.target_step else self.target_step
        reason = self._reason(display_id, relativize_text)
        if self.is_error:
            return f"{self._action_phrase(shown)}\n{reason}"
        return f"{self._partial_phrase(shown)}: {reason}"

    def __str__(self) -> str:
        """Absolute view for logs / tracebacks (ids in the tree's namespace).
        Agent-facing rendering goes through `render` with the session's
        projection mappers."""
        return self.render(lambda s: s, lambda t: t)


class CannotEdit_BlockClosed(CannotEdit):
    """A block-closed proof line can take no more appends."""
    def __init__(self, closed_by: 'step | None', *args, **kw):
        super().__init__(*args, **kw)
        self.closed_by = closed_by
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        if self.closed_by is None:
            return "The proof block is closed."
        return (f"The proof block is closed. "
                f"You should edit node {display_id(self.closed_by)} instead.")


class CannotEdit_NodeNotFound(CannotEdit):
    """Locate failed: the target step id does not exist."""
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        return "The node is not found."


class CannotEdit_BadNode(CannotEdit):
    """`fill` target has a SUCCESS step at or below it."""
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        return ("The target already exists. "
                "Fill does not overwrite existing successful steps.")


class CannotEdit_Root(CannotEdit):
    """`amend` was called on the root node."""
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        return "It is the root node."


class CannotEdit_EvaluationFailed(CannotEdit):
    """Set by an `_on_edit_failure` hook that terminated the edit. `reason`
    is stored ABSOLUTE (it may embed `step …` references from the evaluation
    blob); it is projected into the caller's namespace at render time."""
    def __init__(self, reason: 'FailureReason', *args, **kw):
        super().__init__(*args, **kw)
        self.reason = reason
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        return relativize_text(self.reason.reason)


class GoalIsNontrivial(CannotEdit):
    """Raised by `Obvious.__init__` when the parent goal is non-trivial."""
    _message = ("You cannot claim the goal is obvious again. "
                "You must provide step-by-step proofs.")
    def __init__(self, parent: 'Node', **kw):
        super().__init__(target_step=parent.id, **kw)
        self.parent = parent
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        return self._message


class ProofTreeTooDeep(CannotEdit):
    """Raised in Node.__init__ when the proof tree depth exceeds the session limit."""
    def __init__(self, depth: int, limit: int, parent: 'Node | None'):
        super().__init__(target_step=parent.id if parent else "")
        self.depth = depth
        self.limit = limit
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        return f"Proof tree depth {self.depth} exceeds the limit of {self.limit}."

class CannotEdit_NonDeclarative(CannotEdit):
    """A non-declarative proof operation was inserted into a declaration-only
    block (e.g. GlobalEnv)."""
    def __init__(self, operation_name: str, target_step: str = ""):
        super().__init__(target_step=target_step)
        self.operation_name = operation_name
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        return (f"Operation {self.operation_name} is a proof operation and "
                f"cannot be used as a global declaration. "
                f"Use it inside a proof step instead.")

class CannotEdit_SubgoalSibling(CannotEdit):
    """`insert_before` or `amend` targeted a direct child of a subgoal container
    (Branch / CaseSplit / Induction / SplitConjs / InferenceRule / Define).
    Those children are STRUCTURAL goals (the exhaustiveness obligation + case
    nodes), created internally — not editable steps — so nothing can be inserted
    before them, nor can one be amended."""
    def _reason(self, display_id: 'Callable[[str], str]',
                relativize_text: 'Callable[[str], str]') -> str:
        if self.operation == EditOperation.AMEND:
            return "You can only amend a proof step but not a subgoal."
        return "Cannot insert before a subgoal."


class InternalError(OprError):
    pass
class InternalError_UnparsedTerm(InternalError):
    def __init__(self, term: str, reason: str):
        self.term = term
        self.reason = reason
    def __str__(self) -> str:
        return f"Syntax error in term `{self.term}`\n{self.reason}"

class NodeNotFound(OprError):
    def __init__(self, id: step):
        self.id = id
    def __str__(self) -> str:
        sess = _session_var.get(None)
        shown = sess._display_id(self.id) if sess is not None else self.id
        return f"Step with id {shown} is not found"

class InvalidAnswer(OprError):
    """Raised when user provides an invalid answer to an interaction."""
    def __init__(self, reason: str):
        self.reason = reason
    def __str__(self) -> str:
        return f"Invalid answer: {self.reason}"

class CannotRename(OprError):
    pass
class CannotRename_NotFound(CannotRename):
    def __init__(self, old_name: 'str | varname', new_name: 'str | varname'):
        self.old_name = old_name
        self.new_name = new_name
class CannotRename_VariableNotFound(CannotRename_NotFound):
    old_name: varname
    new_name: varname
    def __str__(self) -> str:
        return f"Cannot rename. The variable {self.old_name.unicode} is not found"
class CannotRename_FactNotFound(CannotRename_NotFound):
    old_name: str
    new_name: str
    def __str__(self) -> str:
        return f"Cannot rename. The fact {self.old_name} is not found"

class CannotDelete(OprError):
    pass
class CannotDelete_NodeNotFound(CannotDelete):
    def __init__(self, id: step):
        self.id = id
    def __str__(self) -> str:
        sess = _session_var.get(None)
        shown = sess._display_id(self.id) if sess is not None else self.id
        return f"Cannot delete {shown} because the node is not found"
class CannotDelete_Root(CannotDelete):
    def __str__(self) -> str:
        return f"Cannot delete the root node"

class ArgumentError(AoA_Error):
    def __init__(self, arg: ToolCall_arg, reason: str):
        self.arg = arg
        self.reason = reason
    def __str__(self) -> str:
        return f"Bad Argument\n{self.reason}"
class ArgumentError_UnknownProofOperation(ArgumentError):
    def __init__(self, arg: ToolCall_arg):
        super().__init__(arg,
            f"Unknown proof operation {arg["operation"]}. " +
            f"Available operations: {list(OPERATION_REGISTRY.keys())}"
        )

class ArgumentError_MissingRequiredKeys(ArgumentError):
    def __init__(self, arg: ToolCall_arg, operation: str, missing: list[str]):
        sorted_missing = [f"`{k}`" for k in sorted(missing)]
        if len(sorted_missing) >= 3:
            joined = ", ".join(sorted_missing[:-1]) + ", and " + sorted_missing[-1]
        elif len(sorted_missing) == 2:
            joined = " and ".join(sorted_missing)
        else:
            joined = sorted_missing[0]
        plural = "fields" if len(sorted_missing) > 1 else "field"
        super().__init__(
            arg,
            f"Operation `{operation}` requires {plural} {joined}",
        )
class ArgumentError_UnparsedTerm(ArgumentError):
    def __init__(self, arg: ToolCall_arg, term: str, reason: str):
        super().__init__(arg, f"Syntax error in term `{term}`\n{reason}")

    @staticmethod
    def from_internal_error(arg: ToolCall_arg, internal_error: InternalError_UnparsedTerm) -> 'ArgumentError_UnparsedTerm':
        """
        Convert an InternalError_UnparsedTerm to an ArgumentError_UnparsedTerm.
        """
        return ArgumentError_UnparsedTerm(arg, internal_error.term, internal_error.reason)

VALIDATORS: dict['type | TypeAliasType', Callable[[Any, str], Any]] = {}

def validator(typ: 'type | TypeAliasType'):
    """Decorator to register a custom validator for a type."""
    def decorator(fn: Callable[[Any, str], Any]):
        VALIDATORS[typ] = fn
        return fn
    return decorator

@validator(raw_proof)
def _validate_raw_proof(data: Any, path: str) -> Any:
    if data == "GivenLater" or data is None:
        return None
    if isinstance(data, dict):
        data = [data]
    return _validate_list(raw_op, data, path)

# Scalar leaf validation. Without these, `validate` silently passes any
# value for a scalar-typed field (e.g. `{"name": None}` as a FactByName),
# and the bad value crashes far from the parse site (e.g. a raw TypeError
# in `_of_clause` rendering the fact suffix).
@validator(str)
def _validate_str(data: Any, path: str) -> str:
    if isinstance(data, str):
        return data
    # LLMs routinely emit bare numbers for term/name fields; int/float → str
    # is the only unambiguous coercion, so accept it. Everything else
    # (null, bool, objects, arrays) is rejected.
    if isinstance(data, (int, float)) and not isinstance(data, bool):
        return str(data)
    raise ArgumentError({}, f"{path}: expected a string, got {type(data).__name__}")

@validator(bool)
def _validate_bool(data: Any, path: str) -> bool:
    if isinstance(data, bool):
        return data
    raise ArgumentError({}, f"{path}: expected a boolean, got {type(data).__name__}")

@validator(int)
def _validate_int(data: Any, path: str) -> int:
    if isinstance(data, int) and not isinstance(data, bool):
        return data
    raise ArgumentError({}, f"{path}: expected an integer, got {type(data).__name__}")

@validator(float)
def _validate_float(data: Any, path: str) -> float:
    if isinstance(data, (int, float)) and not isinstance(data, bool):
        return data
    raise ArgumentError({}, f"{path}: expected a number, got {type(data).__name__}")

def _is_union_origin(origin) -> bool:
    return origin is Union or origin is _types.UnionType

def validate(typ: 'type | TypeAliasType', data: Any, path: str) -> Any:
    """Validate and normalize `data` against `typ`. Returns canonical form."""
    if typ in VALIDATORS:
        return VALIDATORS[typ](data, path)
    if isinstance(typ, TypeAliasType):
        return validate(typ.__value__, data, path)
    if is_typeddict(typ):
        return _validate_typed_dict(typ, data, path)
    origin = get_origin(typ)
    if origin is list:
        return _validate_list(get_args(typ)[0], data, path)
    if _is_union_origin(origin):
        return _validate_union(get_args(typ), data, path)
    if origin is Literal:
        if data in get_args(typ):
            return data
        joined = _join_options([f"`{v}`" for v in get_args(typ)])
        raise ArgumentError(data, f"`{path}` must be one of {joined}")
    return data

def _validate_typed_dict(typ: type, data: Any, path: str) -> Any:
    if not isinstance(data, dict):
        raise ArgumentError({}, f"{path}: expected an object, got {type(data).__name__}")
    required = getattr(typ, "__required_keys__",
        set(getattr(typ, "__annotations__", {}).keys()))
    missing = [k for k in required if k not in data]
    if missing:
        raise ArgumentError_MissingRequiredKeys(data, path, missing)
    try:
        hints = get_type_hints(typ, globalns=globals(), include_extras=False)
    except Exception:
        return data
    for key, field_type in hints.items():
        if key in data:
            data[key] = validate(field_type, data[key], f"{path}.{key}")
    return data

def _validate_list(elem_type: 'type | TypeAliasType', data: Any, path: str) -> Any:
    if not isinstance(data, list):
        raise ArgumentError({}, f"{path}: expected an array, got {type(data).__name__}")
    for i, item in enumerate(data):
        data[i] = validate(elem_type, item, f"{path}[{i}]")
    return data

def _validate_union(args: tuple[type, ...], data: Any, path: str) -> Any:
    none_types = [a for a in args if a is type(None)]
    real_types = [a for a in args if a is not type(None)]
    if none_types and (data is None or data == "GivenLater"):
        return None
    if len(real_types) == 1:
        return validate(real_types[0], data, path)
    for t in real_types:
        if get_origin(t) is Literal:
            if data in get_args(t):
                return data
    non_literal = [t for t in real_types if get_origin(t) is not Literal]
    errors: list[tuple[type, Exception]] = []
    for t in non_literal:
        try:
            return validate(t, data, path)
        except (ArgumentError, KeyError, TypeError, ValueError) as e:
            errors.append((t, e))
    # If the data is a dict and exactly one TypedDict member's required keys
    # match, the user clearly intended that member — re-raise its specific
    # nested error instead of the generic "must be one of" message.
    if isinstance(data, dict):
        structural_matches: list[tuple[type, Exception]] = []
        for t, e in errors:
            if is_typeddict(t):
                required = getattr(t, "__required_keys__",
                    set(getattr(t, "__annotations__", {}).keys()))
                if required <= data.keys():
                    structural_matches.append((t, e))
        if len(structural_matches) == 1:
            raise structural_matches[0][1] from None
    for t in non_literal:
        if t in (str, int, bool, float):
            if isinstance(data, t):
                return data
    # No union member matched. Reject instead of silently passing `data`
    # through: list the acceptable forms in declaration order, naming
    # TypedDict members by their class name (matches the `$defs` keys the
    # agent sees in the raw tool schema), literal members by their value,
    # and the None member as JSON `null`.
    options: list[str] = []
    for t in args:
        if t is type(None):
            options.append("null")
        elif get_origin(t) is Literal:
            options.extend(f"`{v}`" for v in get_args(t))
        else:
            options.append(f"`{getattr(t, '__name__', str(t))}`")
    raise ArgumentError(data, f"`{path}` must be one of {_join_options(options)}")

def _join_options(options: list[str]) -> str:
    if len(options) >= 3:
        return ", ".join(options[:-1]) + ", or " + options[-1]
    return " or ".join(options)

## Minilang Runtime
### Evaluation Status

class EvaluationStatus(NamedTuple):
    class Status(Enum):
        SUCCESS = "success"
        CANCELLED = "cancelled"
        FAILURE = "failure"
        COMMENTED = "commented"
    status: Status
    time: timedelta
    reason: 'FailureReason | None'

    @staticmethod
    def Success(time: timedelta, reason: 'FailureReason | None' = None) -> 'EvaluationStatus':
        return EvaluationStatus(EvaluationStatus.Status.SUCCESS, time, reason)
    @staticmethod
    def Failure(time: timedelta, reason: 'FailureReason') -> 'EvaluationStatus':
        return EvaluationStatus(EvaluationStatus.Status.FAILURE, time, reason)
EVALUATION_CACNCELLED = EvaluationStatus(EvaluationStatus.Status.CANCELLED, 0.0, None)
EVALUATION_NOT_YET = EvaluationStatus.Failure(0.0, FailureReason("Not yet evaluated"))
EVALUATION_COMMENTED = EvaluationStatus(EvaluationStatus.Status.COMMENTED, 0.0, None)

def _status_can_continue(status: EvaluationStatus.Status) -> bool:
    return status in (EvaluationStatus.Status.SUCCESS, EvaluationStatus.Status.COMMENTED)

### Bindings

class VariableBinding(NamedTuple):
    internal_varname: varname
    external_varname: varname
    type: typ

class FactBinding(NamedTuple):
    expr: lambda_term  # internal_term
    name: varname      # external_name (may include "(k)" suffix for destructed atoms)
    pretty: term       # pretty

type Bindings = tuple[list[VariableBinding], list[FactBinding]]

def print_var_bindings(var_bindings: list[VariableBinding], indent: int, file: MyIO, banner='variables'):
    if var_bindings:
        print_indent(indent, file)
        file.write(banner)
        file.write(":\n")
        for vb in var_bindings:
            print_indent(indent + 1, file)
            if vb.external_varname == vb.internal_varname:
                file.write(f"- {vb.external_varname.unicode}: {vb.type.unicode}\n")
            else:
                file.write(f"- {vb.external_varname.unicode}: {vb.type.unicode}    (renamed from \"{vb.internal_varname.unicode}\")\n")

def print_fact_bindings(fact_bindings: list[FactBinding], indent: int, file: MyIO, banner='facts'):
    if fact_bindings:
        print_indent(indent, file)
        file.write(banner)
        file.write(":\n")
        for fb in fact_bindings:
            print_indent(indent + 1, file)
            file.write(f"- {fb.name.unicode}: {fb.pretty.unicode}\n")

def add_var_to_set(var: VariableBinding, ret: list[VariableBinding]) -> list[VariableBinding]:
    for v in ret:
        if v.external_varname == var.external_varname:
            return ret
    ret.append(var)
    return ret

def add_fact_to_set(fact: FactBinding, ret: list[FactBinding]) -> list[FactBinding]:
    for f in ret:
        if f.name == fact.name:
            return ret
    ret.append(fact)
    return ret


### Minilang Messages

class Message:
    @classmethod
    def unpack(cls, data) -> 'Message':
        raise NotImplementedError("unpack must be implemented by subclass")

class New_Item_Msg(Message):
    def __init__(self, items:Context):
        self.items = items
    @classmethod
    def unpack(cls, data) -> 'New_Item_Msg':
        return cls(Context.unpack(data))

class Goals_Msg(Message):
    """The number of new subgoals opened by the operation that produced
    this state.  The ML side still carries the full `term list` (used
    by the translator's `(*goal: …*)` annotations) but the RPC packer
    sends only the length — Python only needs the count (to drive
    `SubgoalMaker.new_subgoals_count`)."""
    def __init__(self, count: int) -> None:
        super().__init__()
        self.count = count
    @classmethod
    def unpack(cls, data) -> 'Goals_Msg':
        # data is an int — see agent_server.ML's packer
        return cls(data)

class Consider_Case_Msg(Message):
    def __init__(self, case: str, vars: list[Var], tvars: list[tuple[varname, typ]], hyps: list[Hyp]) -> None:
        self.case = case
        self.vars = vars
        self.tvars = tvars
        self.hyps = hyps
    @classmethod
    def unpack(cls, data) -> 'Consider_Case_Msg':
        (case, items_data) = data
        context = Context.unpack(items_data)
        vars = list(context.vars.items())
        tvars = list(context.tvars.items())
        hyps = list(context.hyps.items())
        return cls(case, vars, tvars, hyps)

class Intro_Bindings_Msg(Message):
    def __init__(self, missing: 'Bindings', auto_introduced: 'Bindings', final: 'Bindings') -> None:
        super().__init__()
        self.missing = missing
        self.auto_introduced = auto_introduced
        self.final = final

    @classmethod
    def unpack(cls, data) -> 'Intro_Bindings_Msg':
        (missing, auto_introduced, final) = data
        return cls(
            cls._unpack_bindings(missing),
            cls._unpack_bindings(auto_introduced),
            cls._unpack_bindings(final)
        )

    @staticmethod
    def _unpack_bindings(data):
        (var_names, prem_names) = data
        var_bindings = [
            VariableBinding(
                internal_varname=IsaTerm.from_isabelle(v[0]),
                external_varname=IsaTerm.from_isabelle(v[1]),
                type=IsaTerm.from_isabelle(v[2])
            ) for v in var_names
        ]
        fact_bindings = [
            FactBinding(
                expr=p[0],
                name=IsaTerm.from_isabelle(p[1]),
                pretty=IsaTerm.from_isabelle(p[2])
            ) for p in prem_names
        ]
        return (var_bindings, fact_bindings)

class Intro_Standardized_Msg(Message):
    """The explicit Intro used the silent `standard_tac` fallback, which rewrote
    the proof goal (e.g. `A ⊆ B` → `⋀x. x ∈ A ⟹ x ∈ B`). Signals the Intro node
    to print the resulting goal inline."""
    pass

class Simplify_Fallback_Nosys_Msg(Message):
    """The simplification timed out with system simplifiers and succeeded without them."""
    pass

class Simplify_Fallback_Once_Simproc_Msg(Message):
    """Simplification succeeded only after limiting each rule to fire at most once."""
    pass

class Simplify_Targets_Stale_Msg(Message):
    """Some rewrite target terms no longer exist in the current goal.
    The affected rules were discarded."""
    def __init__(self, discarded_names: list[str]) -> None:
        super().__init__()
        self.discarded_names = discarded_names
    @classmethod
    def unpack(cls, data: list) -> 'Simplify_Targets_Stale_Msg':
        return cls(data)

class Specialize_Result_Msg(Message):
    """Result facts produced by SPECIALIZE.
    Each entry is a (fact_name, pretty_printed_proposition) pair."""
    def __init__(self, facts: list[tuple[varname, term]]) -> None:
        super().__init__()
        self.facts = facts
    @classmethod
    def unpack(cls, data: list) -> 'Specialize_Result_Msg':
        # data is [(fact_name, pretty_expression), ...]
        return cls([(IsaTerm.from_isabelle(name), IsaTerm.from_isabelle(expr)) for name, expr in data])

class Newly_Fixed_Vars_Msg(Message):
    """Free variables that the ML side implicitly fixed when setting up a
    sub-proof goal (e.g. `Have "myf n = n + 7"` auto-fixes `n`). Surfaced as
    a `for_any:` block on the corresponding node."""
    def __init__(self, vars: list[tuple[varname, typ]]) -> None:
        super().__init__()
        self.vars = vars  # [(external_name, type_str), ...]
    @classmethod
    def unpack(cls, data) -> 'Newly_Fixed_Vars_Msg':
        return cls([(IsaTerm.from_isabelle(name), IsaTerm.from_isabelle(typ)) for (name, typ) in data])

class Pat_Completeness_Proof_Opened_Msg(Message):
    """The pat-completeness auto-proof during a `Define` operation left
    residual subgoals; a deferred block has been pushed onto the minilang
    stack for interactive discharge. `Define._refresh_the_beginning_opr`
    notices this and sets `_deferred_block_opened = True`."""
    pass

class Termination_Proof_Opened_Msg(Message):
    """The termination auto-proof during a `Define` operation (including
    the `BY_METRIC` metric path's internal sledge fallback) left residual
    well-foundedness / decrease subgoals; a deferred block has been
    pushed. Same handling as `Pat_Completeness_Proof_Opened_Msg`."""
    pass

class Define_Result_Msg(Message):
    """Emitted after a `Define` operation completes. Carries the function
    name and its (possibly inferred) type so the Python side can update
    `Define.type` even when the user omitted it."""
    def __init__(self, name: str, type: typ):
        self.name = name
        self.type = type

class Induction_Dropped_Facts_Msg(Message):
    """Emitted by INDUCT' when some `facts_to_generalize` were dropped
    because they don't mention any generalized variable."""
    def __init__(self, dropped_names: list[str]) -> None:
        super().__init__()
        self.dropped_names = dropped_names

class Discarded_Vars_Msg(Message):
    """Emitted by INDUCT for each variable it generalizes away (the induction
    target). Each pair is (internal skolem name, external name). The Induction
    node records these so that a later `the out-of-scope variable <internal>`
    error message (produced by Unify_Diagnostic when a stale fact referencing
    one of them clashes) resolves to the external name + the discarding step."""
    def __init__(self, pairs: list[tuple[str, str]]) -> None:
        super().__init__()
        self.pairs = pairs

class SetupRewriting_MayLoop_Msg(Message):
    """The rewriting rule may cause infinite looping in the simplifier."""
    pass

class Compute_Result_Msg(Message):
    """Emitted after a successful COMPUTE operation. Carries the fact name
    and the pretty-printed equation `term = result`."""
    def __init__(self, name: varname, result: term):
        super().__init__()
        self.name = name
        self.result = result

class SH_PRF_Msg(Message):
    """Proof method string and wall-clock time (ms) from a successful HAMMER."""
    def __init__(self, method: str, time_ms: int):
        super().__init__()
        self.method = method
        self.time_ms = time_ms

class Hint_Notice_Msg(Message):
    """Agent Hint Registry NOTICE: the operation used a registered constant/fact
    that has a soft hint. `name` is the registered (fully-qualified) name — the
    per-session dedup key; `text` is the authored notice shown to the agent.
    The operation still proceeds (a REJECT hint instead fails the op via an
    error, never reaching this message channel)."""
    def __init__(self, name: str, text: str):
        super().__init__()
        self.name = name
        self.text = text

def unpack_message(data) -> Message:
    match data:
        case (0, x):
            return New_Item_Msg.unpack(x)
        case (1, x):
            return Goals_Msg.unpack(x)
        case (2, x):
            return Consider_Case_Msg.unpack(x)
        case (3, x):
            return Intro_Bindings_Msg.unpack(x)
        case 4:
            return Simplify_Fallback_Nosys_Msg()
        case 9:
            return Simplify_Fallback_Once_Simproc_Msg()
        case 16:
            return Intro_Standardized_Msg()
        case (5, x):
            return Specialize_Result_Msg.unpack(x)
        case (6, x):
            return Newly_Fixed_Vars_Msg.unpack(x)
        case 7:
            return Pat_Completeness_Proof_Opened_Msg()
        case 8:
            return Termination_Proof_Opened_Msg()
        case (10, (name, ty)):
            return Define_Result_Msg(name, IsaTerm.from_isabelle(ty))
        case (11, names):
            return Simplify_Targets_Stale_Msg.unpack(names)
        case (12, names):
            return Induction_Dropped_Facts_Msg(names)
        case 13:
            return SetupRewriting_MayLoop_Msg()
        case (14, (name, result)):
            return Compute_Result_Msg(IsaTerm.from_isabelle(name), IsaTerm.from_isabelle(result))
        case (15, (method, time_ms)):
            return SH_PRF_Msg(method, time_ms)
        case (17, (name, text)):
            return Hint_Notice_Msg(name, text)
        case (18, pairs):
            return Discarded_Vars_Msg([(str(i), str(e)) for (i, e) in pairs])
        case _:
            raise Exception(f"BUG bad message kind: {data}")

### Search Facts by Patterns

class Search_Criterion:
    def __init__(self, positive: bool):
        self.positive = positive
    def dump(self) -> tuple[bool, Any]:
        raise NotImplementedError("dump must be implemented by subclass")
class Criterion_Name(Search_Criterion):
    def __init__(self, positive: bool, name: str):
        super().__init__(positive)
        self.name = name
    def dump(self) -> Any:
        return (self.positive, (0, self.name))
class Criterion_Intro(Search_Criterion):
    def __init__(self, positive: bool):
        super().__init__(positive)
    def dump(self) -> Any:
        return (self.positive, (1, ()))
class Criterion_Elim(Search_Criterion):
    def __init__(self, positive: bool):
        super().__init__(positive)
    def dump(self) -> Any:
        return (self.positive, (2, ()))
class Criterion_Dest(Search_Criterion):
    def __init__(self, positive: bool):
        super().__init__(positive)
    def dump(self) -> Any:
        return (self.positive, (3, ()))
class Criterion_Solves(Search_Criterion):
    def __init__(self, positive: bool):
        super().__init__(positive)
    def dump(self) -> Any:
        return (self.positive, (4, ()))
class Criterion_Simp(Search_Criterion):
    def __init__(self, positive: bool, pattern: term):
        super().__init__(positive)
        self.pattern = pattern
    def dump(self) -> Any:
        return (self.positive, (5, self.pattern.ascii))
class Criterion_XSimp(Search_Criterion):
    def __init__(self, positive: bool, pattern: term, for_any: list[Explicit_Var]):
        super().__init__(positive)
        self.pattern = pattern
        self.for_any = for_any
    def dump(self) -> Any:
        return (self.positive, (5, self.pattern.ascii))
        # TODO: implement the for_any
        # return (self.positive, (8, (self.pattern.ascii, self.for_any)))
class Criterion_Pattern(Search_Criterion):
    def __init__(self, positive: bool, pattern: term):
        super().__init__(positive)
        self.pattern = pattern
    def dump(self) -> Any:
        return (self.positive, (6, self.pattern.ascii))
class Criterion_XPattern(Search_Criterion):
    def __init__(self, positive: bool, pattern: term, for_any: list[Explicit_Var]):
        super().__init__(positive)
        self.pattern = pattern
        self.for_any = for_any
    def dump(self) -> Any:
        return (self.positive, (6, self.pattern.ascii))
        # TODO: implement the for_any
        #return (self.positive, (7, (self.pattern.ascii, self.for_any)))


### Minilang Runtime

def _pack_varnames(varnames: list[varname_spec] | None) -> list[str | None] | None:
    """Convert varname_spec list to plain strings for RPC serialization."""
    if varnames is None:
        return None
    return [v.ascii if v is not None else None for v in varnames]

def _pack_post_insts(insts: 'list[list[tuple[str, xterm | xtyp]]] | None') -> list[list[tuple[str, str]]]:
    """Pack post-rule schematic-instantiation rounds for the wire: a list of
    rounds, each a list of (var-name, value) pairs. Both components are
    ASCII-encoded — the variable name may carry Isabelle symbols (`?\\<alpha>`),
    and the value is an arbitrary term/type expression."""
    if not insts:
        return []
    return [[(ascii_of_unicode(name), ascii_of_unicode(value)) for name, value in rnd]
            for rnd in insts]

class Minilang_Operation(NamedTuple):
    command: str
    arg: Any

    def pack(self):
        return (self.command, self.arg)

    def __str__(self) -> str:
        return f"{self.command}({self.arg})"

    def __repr__(self) -> str:
        return self.__str__()

    @staticmethod
    def SORRY_NEXT(varnames : list[varname_spec] | None) -> 'Minilang_Operation':
        """Cheat one subgoal in the current HHF frame. If the frame
        still has remaining subgoals, return the state with one fewer
        goal (the common multi-subgoal-in-one-HHF case used by
        SubgoalMaker to derive each sibling GoalNode's starting
        state). If the frame becomes empty, pop the enclosing
        ENDBLK T_NXT and rebuild the MAGIC continuation. Errors on
        T_END — callers wanting to close the whole block should use
        SORRY_END_ALL instead."""
        return Minilang_Operation("SORRY_NEXT", _pack_varnames(varnames))
    @staticmethod
    def SORRY_END_ALL(varnames : list[varname_spec] | None) -> 'Minilang_Operation':
        """Cheat every remaining subgoal in the current HHF frame and
        pop the enclosing ENDBLK. Used by `StdBlock`'s failure-recovery
        fallback to discard an entire (possibly multi-goal) block —
        critical for `Define`'s deferred pat-completeness/termination
        block, which may contain multiple residuals that a single
        SORRY_NEXT would leave partially unclosed."""
        return Minilang_Operation("SORRY_END_ALL", _pack_varnames(varnames))
    @staticmethod
    def SORRY_ONLY() -> 'Minilang_Operation':
        """Cheat one subgoal in the current HHF frame without any
        NEXT or END transition — the sorry analogue of HAMMER.
        Used to skip-proof the last GoalNode child whose
        resulting_state feeds into the parent's _state_before_ending_."""
        return Minilang_Operation("SORRY_ONLY", None)
    @staticmethod
    def NEXT(varnames : list[varname_spec] | None) -> 'Minilang_Operation':
        return Minilang_Operation("NEXT", ([], _pack_varnames(varnames)))
    @staticmethod
    def END() -> 'Minilang_Operation':
        return Minilang_Operation("END", [])
    @staticmethod
    def HAVE(name: str, fixes: 'list[tuple[str, str | None]]',
             assumes: 'list[tuple[str | None, str]]',
             conclusion: xterm, auto_apply: bool) -> 'Minilang_Operation':
        return Minilang_Operation("HAVE", (
            name,
            [(n, ascii_of_unicode(t) if t else None) for n, t in fixes],
            [(n, ascii_of_unicode(t)) for n, t in assumes],
            ascii_of_unicode(conclusion),
            auto_apply
        ))
    @staticmethod
    def SETUP_REWRITING(name: str, fixes: 'list[tuple[str, str | None]]',
                        conditions: 'list[tuple[str | None, xterm]]',
                        redex: xterm, residue: xterm) -> 'Minilang_Operation':
        return Minilang_Operation("SETUP_REWRITING", (
            name,
            [(n, ascii_of_unicode(t) if t else None) for n, t in fixes],
            [(n, ascii_of_unicode(t)) for n, t in conditions],
            ascii_of_unicode(redex),
            ascii_of_unicode(residue)
        ))
    @staticmethod
    def SUFFICES(fixes: 'list[tuple[str, str | None]]',
                 assumes: 'list[tuple[str | None, str]]',
                 conclusion: xterm) -> 'Minilang_Operation':
        return Minilang_Operation("SUFFICES", (
            [(n, ascii_of_unicode(t) if t else None) for n, t in fixes],
            [(n, ascii_of_unicode(t)) for n, t in assumes],
            ascii_of_unicode(conclusion)
        ))
    @staticmethod
    def OBTAIN(variables: list[Explicit_Var], constraints: list[tuple[str, xterm]]) -> 'Minilang_Operation':
        vars = [(v["name"], ascii_of_unicode(t) if (t := v.get("type")) else None) for v in variables]
        return Minilang_Operation("OBTAIN", (vars, [(n, ascii_of_unicode(c)) for n, c in constraints]))
    @staticmethod
    def RULE(rule_ref: 'IsabelleFact | None',
             insts: 'list[list[tuple[str, xterm | xtyp]]] | None' = None) -> 'Minilang_Operation':
        return Minilang_Operation("RULE", (
            [rule_ref.pack()] if rule_ref is not None else [],
            _pack_post_insts(insts)))
    @staticmethod
    def HAMMER(fact_refs: 'list[IsabelleFact]', timeout: int = 20,
               cached_proof: 'tuple[str, int] | None' = None) -> 'Minilang_Operation':
        return Minilang_Operation("HAMMER", ([r.pack() for r in fact_refs], timeout, cached_proof))
    @staticmethod
    def CHAINING(name: str, fact_refs: 'list[IsabelleFact]') -> 'Minilang_Operation':
        return Minilang_Operation("CHAINING", (name, [r.pack() for r in fact_refs]))
    @staticmethod
    def INTRO(bindings: Bindings | None, allow_standard_fallback: bool) -> 'Minilang_Operation':
        if bindings is not None:
            var_bindings = [(vb.internal_varname.ascii, vb.external_varname.ascii, vb.type.ascii)
                           for vb in bindings[0]]
            fact_bindings = [(fb.expr, fb.name.ascii, fb.pretty.ascii)
                            for fb in bindings[1]]
            packed_bindings: Any = (var_bindings, fact_bindings)
        else:
            packed_bindings = None
        # 2nd slot was the dead `split_conj` flag (always False); repurposed as
        # `allow_standard_fallback` (True only for explicit/agent-issued Intro).
        return Minilang_Operation("INTRO", (packed_bindings, allow_standard_fallback))
    @staticmethod
    def SPLIT_CONJS() -> 'Minilang_Operation':
        return Minilang_Operation("SPLIT_CONJS", None)
    @staticmethod
    def SIMPLIFY(facts_with_targets: 'list[tuple[IsabelleFact, list[lambda_term] | None]]', use_system_simps: bool, premise_names: list[str], simplify_goal: bool, bindings: tuple[list[tuple[str, str, str]], list[tuple[lambda_term, str, str]]] | None) -> 'Minilang_Operation':
        packed_facts = [(r.pack(), targets) for r, targets in facts_with_targets]
        return Minilang_Operation("SIMPLIFY", (packed_facts, use_system_simps, premise_names, simplify_goal, bindings))
    @staticmethod
    def UNFOLD(fact_refs: 'list[IsabelleFact]') -> 'Minilang_Operation':
        return Minilang_Operation("UNFOLD", [r.pack() for r in fact_refs])
    @staticmethod
    def DEFINE(name: str, ty: xtyp | None, equations: list[xterm], metric: list[xterm]) -> 'Minilang_Operation':
        return Minilang_Operation("DEFINE", (
            name,
            ascii_of_unicode(ty) if ty is not None else None,
            [ascii_of_unicode(eq) for eq in equations],
            [ascii_of_unicode(m) for m in metric],
        ))
    @staticmethod
    def WITNESS(terms: list[xterm]) -> 'Minilang_Operation':
        return Minilang_Operation("WITNESS", [ascii_of_unicode(t) for t in terms])
    @staticmethod
    def BRANCH(cases: list[tuple[str, xterm]]) -> 'Minilang_Operation':
        return Minilang_Operation("BRANCH", [(n, ascii_of_unicode(t)) for n, t in cases])
    @staticmethod
    def CASE_SPLIT(target: xterm, vars: list[varname_spec] | None, rule: 'IsaTerm | None', no_simp: bool,
                   insts: 'list[list[tuple[str, xterm | xtyp]]] | None' = None) -> 'Minilang_Operation':
        return Minilang_Operation("CASE_SPLIT",
            (ascii_of_unicode(target), _pack_varnames(vars),
             rule.ascii if rule is not None else None,
             no_simp, _pack_post_insts(insts)))
    @staticmethod
    def INDUCT(target: xterm, vars: list[varname_spec] | None, arbitrary: list[xvarname],
               facts_to_generalize: list[str], rule: 'IsaTerm | None', no_simp: bool,
               insts: 'list[list[tuple[str, xterm | xtyp]]] | None' = None) -> 'Minilang_Operation':
        return Minilang_Operation("INDUCT",
            (ascii_of_unicode(target), _pack_varnames(vars),
             [ascii_of_unicode(t) for t in arbitrary],
             list(facts_to_generalize),
             rule.ascii if rule is not None else None,
             no_simp, _pack_post_insts(insts)))
    @staticmethod
    def SPECIALIZE(
        name: str,
        rule_ref: 'IsabelleFact',
        instantiations: list[tuple[str, xterm]],  # (var_name, term_string)
        fact_refs: 'list[IsabelleFact]'
    ) -> 'Minilang_Operation':
        return Minilang_Operation("SPECIALIZE", (
            name,
            rule_ref.pack(),
            [(n, ascii_of_unicode(t)) for n, t in instantiations],
            [r.pack() for r in fact_refs]
        ))
    @staticmethod
    def SKIP() -> 'Minilang_Operation':
        return Minilang_Operation("SKIP", None)
    @staticmethod
    def CONTRADICTION(hypothesis_name: str) -> 'Minilang_Operation':
        return Minilang_Operation("CONTRADICTION", hypothesis_name)
    @staticmethod
    def COMPUTE(name: str, term: 'xterm') -> 'Minilang_Operation':
        return Minilang_Operation("COMPUTE", (name, ascii_of_unicode(term)))

type Extended_Minilang_Operation = Minilang_Operation | list[Minilang_Operation]


class Minilang_State:
    def __init__(self, connection: Connection, name: str):
        self.connection = connection
        self.name = name
        self.messages : list[Message] = []
        # The leading (first) proof goal with its context (vars/hyps
        # from the top HHF's items), or None if the proof is solved.
        # Replaces the full MLPT proof tree — Python only ever accessed
        # top_goal() / top_goal_or_none() from the tree.
        self.leading_goal: Goal | None = None
        # Total number of goals in the current state's top HHF.
        # Used for display paths (has_pending_goal, should_I_show_pending_goal,
        # Root init).  This is the "display count" — may include siblings
        # from outer operations in nested contexts.  NOT used for
        # SubgoalMaker block-opening (that uses new_subgoals_count).
        self.display_goals_count: int = 0
        # Count of new subgoals that the operation producing this state
        # opened as direct children.  Populated from a `Goals_Msg` emitted
        # by the ML side.  `None` = op didn't emit Goals (SPECIALIZE etc.);
        # `0` = op emitted Goals with count 0 (HAMMER closing, INTRO no-op).
        # SubgoalMaker reads this for block-opening decisions.
        self.new_subgoals_count : int | None = None
        self._initialized: bool = False
    def initialized(self) -> bool:
        return self._initialized
    def __str__(self) -> str:
        return f"Minilang_State({self.name})"
    def __repr__(self) -> str:
        return self.__str__()
    state_counter : int = 0
    @classmethod
    def assign_name(cls) -> str:
        cls.state_counter += 1
        return f"${cls.state_counter}"
    @classmethod
    def assign(cls, connection : 'Connection | Minilang_State'):
        if isinstance(connection, Minilang_State):
            connection = connection.connection
        return Minilang_State(connection, cls.assign_name())
    @staticmethod
    def _unpack_flat_goal(data) -> tuple['Goal | None', int]:
        """Unpack the flat goal representation from the ML RPC.
        Wire format: tag 0 = solved (no goal); tag 1 = (items, term, count)."""
        match data:
            case 0:
                return (None, 0)
            case (1, (items_data, conclusion_str), count):
                context = Context.unpack(items_data)
                return (Goal(context, IsaTerm.from_isabelle(conclusion_str)), count)
            case _:
                raise InternalError(f"Bad flat goal data: {data!r}")

    async def execute(self, opr: Extended_Minilang_Operation, assign_to: 'Minilang_State | None', *, log: bool = True) -> 'Minilang_State':
        # `log=False` is for throwaway probes (e.g. InferenceRule._rewrite_trial)
        # whose operation must NOT leave a record in the live proof-op log; Isabelle
        # time accounting (on_operation_start/end) stays unconditional so a probe
        # still legitimately charges the time it spent.
        if assign_to is None:
            assign_to = Minilang_State(self.connection, type(self).assign_name())
        if isinstance(opr, Minilang_Operation):
            dest_name = assign_to.name
            session = the_session()
            if log:
                session.log_proof_operation(
                    step="execute",
                    operation=opr.command,
                    details={
                        "from_state": self.name,
                        "to_state": dest_name,
                        "operation": str(opr),
                    }
                )
            session.on_operation_start(self.name, opr.command, opr.arg)
            now = time()
            try:
                (msgs, flat_goal) = await self.connection.callback("IsaMini.proof_opr",
                                                        (self.name, dest_name, (opr.command, opr.arg)))
            except IsabelleError as err:
                session.on_operation_end(self.name, opr.command, opr.arg,
                    EvaluationStatus.Failure(time() - now, FailureReason(''.join(err.errors))))
                if log:
                    session.log_proof_operation_error(
                        error_message=str(err),
                        errors=err.errors,
                        operation=str(opr)
                    )
                if err.errors == ["beginning_state_not_found"]:
                    raise InternalError("The beginning state of the execution is not initialized!")
                raise
            session.on_operation_end(self.name, opr.command, opr.arg,
                EvaluationStatus.Success(time() - now))
            msgs = [unpack_message(msg) for msg in msgs]
            (assign_to.leading_goal, assign_to.display_goals_count) = \
                Minilang_State._unpack_flat_goal(flat_goal)
            assign_to._initialized = True
            assign_to.messages = msgs
            goals_msgs = [m for m in msgs if isinstance(m, Goals_Msg)]
            match goals_msgs:
                case []:
                    assign_to.new_subgoals_count = None
                case [gm]:
                    assign_to.new_subgoals_count = gm.count
                case _:
                    raise InternalError(
                        f"Expected at most one Goals_Msg per operation, "
                        f"got {len(goals_msgs)} for {opr.command}")
        else:
            raise NotImplementedError("Here we should implement the execution of a list of Minilang operations")
            #msgs = opr(self, assign_to)
        return assign_to
    async def sorry_next(self, varnames: list[varname_spec] | None, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        """Cheat one subgoal in the current frame. See
        `Minilang_Operation.SORRY_NEXT` for semantics."""
        return await self.execute(Minilang_Operation.SORRY_NEXT(varnames), assign_to)
    async def sorry_end_all(self, varnames: list[varname_spec] | None, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        """Cheat every remaining subgoal in the current frame and pop
        the enclosing ENDBLK. See `Minilang_Operation.SORRY_END_ALL`
        for semantics."""
        return await self.execute(Minilang_Operation.SORRY_END_ALL(varnames), assign_to)
    async def sorry_only(self, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        """Cheat one subgoal without NEXT/END. See
        `Minilang_Operation.SORRY_ONLY` for semantics."""
        return await self.execute(Minilang_Operation.SORRY_ONLY(), assign_to)
    async def skip(self, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        return await self.execute(Minilang_Operation.SKIP(), assign_to)
    async def clone(self, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        if not self.initialized():
            if assign_to is None:
                assign_to = Minilang_State(self.connection, type(self).assign_name())
            assign_to.messages = list(self.messages)
            assign_to.new_subgoals_count = self.new_subgoals_count
            return assign_to
        ret = await self.execute(Minilang_Operation.SKIP(), assign_to)
        ret.messages = self.messages
        ret.new_subgoals_count = self.new_subgoals_count
        return ret
    async def reset(self) -> None:
        """Remove this state from the Isabelle state table and mark as uninitialized."""
        await self.connection.callback("IsaMini.reset_state", self.name)
        self.leading_goal = None
        self.display_goals_count = 0
        self._initialized = False
        self.new_subgoals_count = None
    async def fetch_facts(self, facts: Sequence[Fact]) -> 'list[IsabelleFact | Interaction_RetrieveForProof]':
        """Resolve a list of facts.
        - FactByName: batched RPC lookup → IsabelleFact_Presented or IsabelleFact_Unfound
        - FactByProposition: directly → IsabelleFact_ProveInTime
        - FactByDescription: → Interaction_RetrieveForProof (needs interaction)
        Callers passing only FactByName|FactByProposition can safely cast to list[IsabelleFact]."""
        facts = [f for f in facts if f is not None]
        out: list[IsabelleFact | Interaction_RetrieveForProof] = [None] * len(facts)  # type: ignore
        # Collect FactByName indices for batch lookup
        name_indices: list[int] = []
        name_queries: list[str] = []
        for i, fact in enumerate(facts):
            if "name" in fact:
                name_indices.append(i)
                name_queries.append(fact["name"])
            elif "proposition" in fact:
                prop = cast(FactByProposition, fact)["proposition"]
                out[i] = IsabelleFact_ProveInTime(IsaTerm.from_agent(prop),
                                                   assigned_name=the_session().next_pit_name())
            else:
                desc = " ".join(cast(FactByDescription, fact)["english"].split())
                out[i] = Interaction_RetrieveForProof(
                    state=self, query=desc, kinds=[EntityKind.THEOREM])
        # Batch resolve all FactByName
        if name_queries:
            entities = [(EntityKind.THEOREM, name) for name in name_queries]
            results = await self._retrieve_entity(entities)
            for idx, (query_name, result) in zip(name_indices,
                                                  zip(name_queries, results)):
                fact = facts[idx]
                if result is None:
                    out[idx] = IsabelleFact_Unfound(fact)
                else:
                    short_name, exprs, roles, _, is_local = result
                    out[idx] = IsabelleFact_Presented(
                        full_name=query_name, short_name=short_name,
                        fact=fact, expression=exprs, roles=roles,
                        is_local=is_local)
        return out
    async def refresh_facts(self, facts: list[IsabelleFact]) -> list[IsabelleFact]:
        """Re-validate cached Presented/Unfound facts against the current
        state. ProveInTime facts pass through unchanged. Returns a new
        list of fresh instances; inputs are not mutated. Precondition:
        self.initialized()."""
        out: list[IsabelleFact] = list(facts)
        query_indices: list[int] = []
        queries: list[tuple[EntityKind, str]] = []
        original_facts: list[Fact] = []
        for i, f in enumerate(facts):
            if isinstance(f, IsabelleFact_ProveInTime):
                continue
            assert isinstance(f, (IsabelleFact_Presented, IsabelleFact_Unfound))
            # Preserve the kind for Presented; default to THEOREM for
            # Unfound (the only producers of Unfound today are
            # theorem-kind lookups).
            kind = f.kind if isinstance(f, IsabelleFact_Presented) else EntityKind.THEOREM
            query_indices.append(i)
            queries.append((kind, cast(FactByName, f.fact)["name"]))
            original_facts.append(f.fact)
        if not queries:
            return out
        results = await self._retrieve_entity(queries)
        for idx, (kind, query_name), result, original_fact in zip(
                query_indices, queries, results, original_facts):
            if result is None:
                out[idx] = IsabelleFact_Unfound(original_fact)
            else:
                short_name, exprs, roles, _, is_local = result
                # Preserve is_conditional across refresh: _retrieve_entity does not
                # carry it, but the input fact (if Presented) already knows it.
                in_fact = facts[idx]
                prev_cond = (in_fact.is_conditional
                             if isinstance(in_fact, IsabelleFact_Presented) else False)
                out[idx] = IsabelleFact_Presented(
                    full_name=query_name, short_name=short_name,
                    fact=original_fact, expression=exprs,
                    kind=kind, roles=roles, is_local=is_local,
                    is_conditional=prev_cond)
        return out
    async def semantic_knn(self, query: str | None, k: int,
                     kinds: list[EntityKind],
                     term_patterns: list[str] = [],
                     type_patterns: list[str] = [],
                     theories_include: list[str] = [],
                     name_contains: list[str] = [],
                     exact_name: str | None = None,
                     target_type: str = "",
                     ) -> tuple[list[RetrievedEntity], list[str]]:
        """Backward-compatible 2-tuple wrapper around ``semantic_knn_counted``.
        Returns (results, warnings); drops the total match count."""
        results, warnings, _total = await self.semantic_knn_counted(
            query, k, kinds, term_patterns=term_patterns,
            type_patterns=type_patterns, theories_include=theories_include,
            name_contains=name_contains, exact_name=exact_name,
            target_type=target_type)
        return results, warnings

    async def semantic_knn_counted(self, query: str | None, k: int,
                     kinds: list[EntityKind],
                     term_patterns: list[str] = [],
                     type_patterns: list[str] = [],
                     theories_include: list[str] = [],
                     name_contains: list[str] = [],
                     exact_name: str | None = None,
                     target_type: str = "",
                     ) -> tuple[list[RetrievedEntity], list[str], int]:
        """Search k nearest entities by semantic similarity, returning resolved entities.
        If exact_name is given, does an exact lookup (score=1.0), ignoring other criteria.
        If query is None, returns pattern-filtered entities without semantic ranking.
        For TheoremK, extends the domain with local contextual thm keys.
        Pattern/theory filters (empty = no restriction) are forwarded to
        the entity enumeration callbacks for ML-side filtering.
        Returns (results, warnings, total) where warnings include notices about
        undeclared free variables in term patterns and total is the number of
        entities matching the filters (the full pool before the top-k cut)."""
        from Isabelle_Semantic_Embedding.semantics import Semantic_DB

        # Exact name lookup — bypass all search criteria
        # scored_recs elements are (score, rec, override) in ALL branches below:
        # override is None except for abbreviation constants hit by exact_name,
        # where it carries (semantics_heading, interpretation) from
        # constant_semantics_layers. The shapes MUST stay in sync — the three
        # construction sites converge on one shared unpacking loop at the end.
        # Ref-names of members surfaced by a >1-member bundle expansion (exact_name);
        # read by the shared unpacking loop to suppress their per-member declaring
        # definition. Empty (and harmless) on the non-exact path.
        bundle_member_names: set[str] = set()
        if exact_name is not None:
            scored_recs: list[tuple[float, SemanticRecord, tuple[str, str | None] | None]] = []
            warnings: list[str] = []
            # Full size of the multi-theorem fact (bundle) hit by exact_name, if
            # any; only set on the THEOREM-success path, used solely for the
            # truncation note. None when no bundle resolved.
            bundle_N: int | None = None
            for tag in kinds:
                if tag == EntityKind.THEOREM:
                    # A fact name may bind several theorems (`foo`, members
                    # `foo(1)/foo(2)`). Expand to its members (up to the cap)
                    # rather than reporting the bare name "Undefined".
                    try:
                        n_total, members = await key_of_theorems(
                            self.connection, exact_name,
                            limit=EXACT_NAME_BUNDLE_LIMIT, ctxt=self.name)
                    except UndefinedEntity:
                        continue
                    except IsabelleError as e:
                        # e.g. an explicit out-of-range index — surface the
                        # helpful message instead of the generic "Undefined".
                        warnings.append(e.errors[0] if e.errors else str(e))
                        continue
                    bundle_N = n_total
                    for uk, ref_name in members:
                        rec = Semantic_DB[uk]
                        rec = (rec._replace(name=ref_name) if rec is not None
                               else SemanticRecord(EntityKind.THEOREM, ref_name, None, None))
                        if n_total > 1:
                            bundle_member_names.add(ref_name)
                        scored_recs.append((1.0, rec, None))
                    continue
                try:
                    uk, full_name = await universal_key_and_name_of(self.connection, tag, exact_name, ctxt=self.name)
                except UndefinedEntity:
                    resolved: tuple[universal_key, str] | None = None
                    # Retry with the short (base) name for a qualified xname.
                    if "." in exact_name:
                        short = exact_name.rsplit(".", 1)[1]
                        try:
                            resolved = await universal_key_and_name_of(self.connection, tag, short, ctxt=self.name)
                        except Exception:
                            resolved = None
                    # Fall back to notation resolution: a bare operator symbol
                    # like `*` / `≤` isn't in the const name space, but it parses
                    # (as an operator section / infix / prefix / …) to a constant
                    # we can then look up by name. Only constants carry notation.
                    if resolved is None and tag == EntityKind.CONSTANT:
                        const_name = await self.resolve_notation(exact_name)
                        if const_name is not None:
                            try:
                                resolved = await universal_key_and_name_of(self.connection, tag, const_name, ctxt=self.name)
                            except Exception:
                                resolved = None
                    if resolved is None:
                        continue
                    uk, full_name = resolved
                except IsabelleError:
                    continue
                rec = Semantic_DB[uk]
                override: tuple[str, str | None] | None = None
                if tag == EntityKind.CONSTANT:
                    layered = await self.constant_semantics_layers(uk, full_name)
                    if layered is not None:
                        l_heading, l_rec = layered
                        override = (l_heading,
                                    l_rec.interpretation if l_rec is not None else None)
                if rec is not None:
                    scored_recs.append((1.0, rec, override))
                else:
                    scored_recs.append((1.0, SemanticRecord(tag, full_name, None, None), override))
            if not scored_recs:
                return [], (warnings or [f'Undefined: "{exact_name}"']), 0
            if bundle_N is not None and bundle_N > EXACT_NAME_BUNDLE_LIMIT:
                first_rest = EXACT_NAME_BUNDLE_LIMIT + 1
                rest = (f"use {exact_name}({bundle_N})" if first_rest == bundle_N
                        else f"use {exact_name}({first_rest}) … {exact_name}({bundle_N})")
                warnings.append(
                    f"{exact_name} has {bundle_N} theorems — showing the first "
                    f"{EXACT_NAME_BUNDLE_LIMIT}; {rest} for the rest.")
            total = len(scored_recs)
            # Skip to entity resolution below
        else:

            term_patterns = [ascii_of_unicode(p) for p in term_patterns]
            type_patterns = [ascii_of_unicode(p) for p in type_patterns]
            target_type = ascii_of_unicode(target_type)
            # Build domain
            if EntityKind.THEOREM in kinds:
                local_entries: list[tuple] = await self.connection.callback(
                    "IsaMini.contextual_thms", self.name)
                # contextual_thms are the proof-context-local lemmas → tag them
                # is_local=True so any no-embedding ones get the local default score.
                domain: Semantic_Vector_Store.Domain = Semantic_Vector_Store.ContextExtended(
                    [Semantic_Vector_Store.ExtraKey(key=bytes(k_), name=name, is_local=True)
                     for k_, name in local_entries])
            else:
                domain = Semantic_Vector_Store.ContextAll
            store: Semantic_Vector_Store = await self.connection.semantic_vector_store()  # type: ignore
            if query is not None:
                raw_results, warnings_raw, total = await store.lookup(query, k, kinds, domain,
                                       term_patterns=term_patterns,
                                       type_patterns=type_patterns,
                                       theories_include=theories_include,
                                       name_contains=name_contains,
                                       target_type=target_type,
                                       ctxt=self.name)
                warnings = [_clean_warning(w) for w in warnings_raw]
                scored_recs = [(score, rec, None) for score, rec in raw_results]
            else:
                # Pattern-only search: get filtered entities, look up records, no ranking.
                # Enumerate ALL matches (limit=-1) to know the total, then resolve
                # records only for the top-k slice (avoid resolving thousands).
                from Isabelle_RPC_Host.context import entities_of
                entries, is_local_map, warnings_raw = await entities_of(self.connection, kinds,
                                         term_patterns=term_patterns,
                                         type_patterns=type_patterns,
                                         theories_include=theories_include,
                                         name_contains=name_contains,
                                         limit=-1,
                                         target_type=target_type,
                                         ctxt=self.name)
                warnings = [_clean_warning(w) for w in warnings_raw]
                total = len(entries)
                # No query vector → no semantic similarity. Score no-embedding entities
                # by the provider default (local lemmas higher), then sort so local
                # lemmas surface first. Sort BEFORE the top-k slice so locals aren't cut.
                def _pat_score(uk: bytes) -> float:
                    return (store.emb_provider.default_local_score
                            if is_local_map.get(uk, False)
                            else store.emb_provider.default_score)
                entries.sort(key=lambda e: _pat_score(e[0]), reverse=True)
                scored_recs = []
                for uk, name, _ in entries[:k]:
                    rec = Semantic_DB[uk]
                    if rec is not None:
                        scored_recs.append((_pat_score(uk), rec, None))
                    else:
                        scored_recs.append((_pat_score(uk), SemanticRecord(EntityKind(uk[16]), name, None, None), None))
        if not scored_recs:
            return [], warnings, total
        # Resolve entities via RPC
        entity_keys = [(rec.kind, rec.name) for _, rec, _ in scored_recs]
        infos = await self._retrieve_entity(entity_keys)
        out: list[RetrievedEntity] = []
        for (score, rec, override), info in zip(scored_recs, infos):
            heading, interp = override if override is not None else (None, rec.interpretation)
            out.append(self._make_retrieved_entity(
                rec.kind, rec.name, info, score,
                ' '.join(interp.split()) if interp else None,
                semantics_heading=heading,
                suppress_def=rec.name in bundle_member_names))
        return out, warnings, total
    async def compute_bindings(self, var_names: list[varname], fact_names: list[varname]) -> Bindings:
        """
        Compute bindings for the leading proof goal by binding provided names in order.
        var_names[i] is bound to the i-th quantified variable in the goal.
        fact_names[j] is bound to the j-th premise in the goal.
        When the Minilang.INTRO_split_prem_conj config is on (the default for the
        Minilang agent), a conj-shaped premise's single provided name expands into
        multiple "name(k)" entries — one per atomic conjunct.
        Raises IsabelleError if the lengths don't match the goal structure.
        """
        bindings_data = await self.connection.callback("IsaMini.compute_bindings",
                                                  (self.name,
                                                   [v.ascii for v in var_names],
                                                   [f.ascii for f in fact_names]))
        return Intro_Bindings_Msg._unpack_bindings(bindings_data)
    async def need_intro(self, consider_conj: bool) -> bool:
        """
        Check if the leading proof goal needs INTRO (i.e., has quantified variables or premises).
        If consider_conj is True, also considers conjunction as needing intro.
        """
        result = await self.connection.callback("IsaMini.need_intro", (self.name, consider_conj))
        return result
    async def _retrieve_entity(self, entities: list[tuple[EntityKind, str]]
        ) -> list[tuple[short_name, list[term], list[str], list[full_name], bool] | None]:
        """Retrieve entity info by kind and name (short or full).
        Returns list of (short_name, extra_strings, roles, abbreviation_names, is_local) or None per entity.
        extra_strings: propositions for theorems/rules, [type] for constants, [] for others.
        roles: list of system rule set tags ('simp', 'intro', 'elim') for theorems, [] for others.
        abbreviation_names: full names of abbreviation constants involved in the entity.
        is_local: True iff the entity is a theorem visible only in the current proof context
                  (not in the global theory namespace); always False for non-theorem kinds."""
        args = [(int(kind), name) for kind, name in entities]
        results = await self.connection.callback(
            "IsaMini.retrieve_entity", (self.name, args))
        return [(IsaTerm.from_isabelle(r[0]), [IsaTerm.from_isabelle(e) for e in r[1]], list(r[2]),
                 list(r[3]), bool(r[4]))
                if r is not None else None for r in results]
    def _make_retrieved_entity(
        self, kind: EntityKind, full_name: str,
        info: 'tuple[short_name, list[term], list[str], list[full_name], bool] | None',
        score: float, interpretation: 'str | None',
        semantics_heading: 'str | None' = None,
        suppress_def: bool = False,
    ) -> RetrievedEntity:
        """Build a ``RetrievedEntity`` from a ``_retrieve_entity`` result tuple
        (or a ``None`` placeholder → empty expression). Pure construction: no RPC,
        no semantic embedding. Shared by ``semantic_knn`` (with its similarity
        ``score`` + ``interpretation``) and ``retrieve_entities_by_name`` (score
        ``1.0``, no interpretation)."""
        if info is None:
            sname: 'short_name' = IsaTerm.from_isabelle(full_name)
            exprs: list[term] = []
            roles: list[str] = []
            abbrev_names: 'list[full_name]' = []
            is_local = False
        else:
            sname, exprs, roles, abbrev_names, is_local = info
        if kind in _THEOREM_KINDS:
            entity: IsabelleEntity = IsabelleFact_Presented(
                full_name=full_name, short_name=sname,
                fact=FactByName(name=sname.ascii),
                expression=exprs, kind=kind, roles=roles,
                abbreviation_names=abbrev_names, is_local=is_local)
        else:
            entity = IsabelleEntity(
                full_name=full_name, short_name=sname,
                expression=exprs, kind=kind, roles=roles,
                abbreviation_names=abbrev_names)
        return RetrievedEntity(entity=entity, score=score, interpretation=interpretation,
                               semantics_heading=semantics_heading, suppress_def=suppress_def)

    async def retrieve_entities_by_name(
        self, names: list[str], kind: EntityKind = EntityKind.THEOREM,
    ) -> 'list[RetrievedEntity | None]':
        """Resolve entity NAMES to ``RetrievedEntity`` via the lightweight
        ``IsaMini.retrieve_entity`` ML callback ONLY — no semantic embedding,
        vector store, or ``Semantic_DB`` (unlike ``semantic_knn``). ``score`` is
        ``1.0`` and ``interpretation`` is ``None`` (both are semantic-search-only).
        Returns ``None`` in the slot of any name that does not resolve. Batched:
        one RPC for all names."""
        if not names:
            return []
        infos = await self._retrieve_entity([(kind, n) for n in names])
        return [self._make_retrieved_entity(kind, n, info, 1.0, None)
                if info is not None else None
                for n, info in zip(names, infos)]
    async def check_term(self, term_str: xterm) -> tuple[typ, Vars, Vars]:
        """
        Parse and check a term string using Syntax.read_term.
        Returns a tuple of (term_type, frees, vars) where:
        - term_type: pretty-printed type of the term
        - frees: dict of {name: type} for free variables
        - vars: dict of {name: type} for schematic variables (names formatted as ?name.idx)
        Raises InternalError_UnparsedTerm if parsing fails.
        """
        try:
            term_type, frees_list, vars_list = await self.connection.callback("IsaMini.check_term",
                                                                         (self.name, ascii_of_unicode(term_str)))
            frees = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in frees_list}
            vars = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in vars_list}
            return (IsaTerm.from_isabelle(term_type), frees, vars)
        except IsabelleError as e:
            # The ML check_term callback signals a parse/type failure as a single
            # `error "Unparsed: <msg>"` string (agent_server.ML), so `e.errors` is a
            # one-element list `["Unparsed: <msg>"]`. Match that prefix (mirrors
            # `unfold_syntax` below). The old `len(e.errors) >= 2 and
            # e.errors[0] == "Unparsed"` guard expected a 2-element list the ML never
            # produces, so it never fired — InternalError_UnparsedTerm was dead and a
            # bare IsabelleError leaked to callers (e.g. the Induction syntax-error
            # message path).
            _PREFIX = "Unparsed: "
            if e.errors and e.errors[0].startswith(_PREFIX):
                raise InternalError_UnparsedTerm(term_str, e.errors[0][len(_PREFIX):])
            else:
                raise

    async def induction_target_hits_leading_binder(self, target: xterm) -> bool:
        """True iff the induction `target` mentions a free variable that is a
        not-yet-introduced leading ∀/⋀ binder of the current goal — decided
        entirely ML-side in one context (see the
        ``IsaMini.induction_target_hits_leading_binder`` callback in
        agent_server.ML). Used to auto-inject an Intro before a body-leading
        Induction on a ∀/⋀-bound variable."""
        return await self.connection.callback(
            "IsaMini.induction_target_hits_leading_binder",
            (self.name, ascii_of_unicode(target)))

    async def unfold_syntax(self, term_str: str) -> tuple[str, str, str, str]:
        """Parse term and unfold higher-theory syntax.
        Returns (head_const_name, raw_main_display, normal_display, abbrev_head).
        ``head_const_name`` is the head of the fully expanded term; ``abbrev_head``
        is the head of the abbreviation-preserving parse — when the term's head is
        an abbreviation, it names the abbreviation constant itself (else it equals
        ``head_const_name``, or is "" when that parse fails / heads a non-constant).
        Raises InternalError_UnparsedTerm if parsing fails."""
        try:
            head_name, raw_display, normal_display, abbrev_head = await self.connection.callback(
                "IsaMini.unfold_syntax",
                (self.name, ascii_of_unicode(term_str)))
            raw = pretty_unicode(raw_display).replace("??.", "")
            return (head_name, raw, pretty_unicode(normal_display), abbrev_head)
        except IsabelleError as e:
            _PREFIX = "Unparsed: "
            if e.errors and e.errors[0].startswith(_PREFIX):
                raise InternalError_UnparsedTerm(term_str, e.errors[0][len(_PREFIX):])
            else:
                raise

    async def resolve_notation(self, symbol: str) -> str | None:
        """Resolve a bare notation symbol (e.g. ``*``, ``≤``, a postfix marker)
        to its underlying constant full name, trying operator-section / infix /
        prefix / postfix / binder probes ML-side. A notation attached to an
        abbreviation resolves to the abbreviation constant itself (abbreviations
        are first-class entities), not to its expansion's head. Returns the const
        name, or None when the symbol resolves to no constant (so callers can
        fall back). Never raises on an unresolvable symbol — the ML callback
        guards each probe and returns an empty string for "not a resolvable
        notation"."""
        name = await self.connection.callback(
            "IsaMini.resolve_notation",
            (self.name, ascii_of_unicode(symbol)))
        return name or None

    async def abbrev_expansion_head(self, const_full_name: str) -> tuple[bool, str | None]:
        """Whether ``const_full_name`` (an internal full constant name) is an
        abbreviation, and the head constant of its expansion (None when the
        expansion's head is not a constant). The rhs is NOT normalized ML-side:
        the head may itself be another abbreviation (one expansion layer only)."""
        is_abbrev, exp_head = await self.connection.callback(
            "IsaMini.abbrev_expansion_head",
            (self.name, ascii_of_unicode(const_full_name)))
        return (bool(is_abbrev), exp_head or None)

    async def constant_semantics_layers(self, uk: universal_key, full_name: str
        ) -> 'tuple[str, SemanticRecord | None] | None':
        """Two-layer semantics for a constant that may be an abbreviation
        (abbreviations are first-class entities and are interpreted on a par
        with ordinary constants):
        1. not an abbreviation -> None (caller renders as today);
        2. the abbreviation's own interpretation, when Semantic_DB has one;
        3. else the interpretation of its expansion's head constant;
        4. else a bare "Abbreviation constant ..." heading, no interpretation.
        For layers 2-4 returns (heading, record) where record is the
        SemanticRecord the heading describes — the abbreviation's own for
        layers 2/4 (possibly None in 4), the expansion head's for layer 3 —
        so callers can render its type and interpretation consistently."""
        from Isabelle_Semantic_Embedding.semantics import Semantic_DB
        is_abbrev, exp_head = await self.abbrev_expansion_head(full_name)
        if not is_abbrev:
            return None
        rec = Semantic_DB[uk]
        if rec is not None and rec.interpretation:
            return (f"Abbreviation constant {full_name}", rec)
        if exp_head is not None:
            # Best-effort: an expansion head that fails to intern ML-side
            # (e.g. a hidden constant) must not abort the whole query.
            try:
                exp_uk, exp_full = await universal_key_and_name_of(
                    self.connection, EntityKind.CONSTANT, exp_head, ctxt=self.name)
            except (UndefinedEntity, IsabelleError):
                exp_uk, exp_full = None, None
            if exp_uk is not None:
                exp_rec = Semantic_DB[exp_uk]
                if exp_rec is not None and exp_rec.interpretation:
                    return (f"Raw constant {exp_full}"
                            f" (head of the unfolded abbreviation {full_name})",
                            exp_rec)
        return (f"Abbreviation constant {full_name}", rec)

    async def schematic_variables_of(self, whole: bool = False) -> tuple[Vars, TVars]:
        """
        Get schematic variables from the proof goal(s).

        `whole=False` scans only the leading subgoal; `whole=True` scans the
        whole goal sequent (every open subgoal).

        Returns `(term_vars, type_vars)`: `term_vars` maps each schematic term
        variable (`?name.idx`) to its type, and `type_vars` maps each schematic
        type variable (`?'name.idx`) to its sort.
        """
        vars_list, tvars_list = await self.connection.callback(
            "IsaMini.schematic_variables_of", (self.name, whole))
        term_vars = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in vars_list}
        type_vars = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in tvars_list}
        return term_vars, type_vars

    async def potential_defs_of(self, constant_names: 'list[name]') -> list[IsabelleFact_Presented]:
        """
        Get potential definitions for constants via Potential_Defs_Of RPC.
        Each name is parsed as a term to extract the head constant.
        Returns list of IsabelleFact_Presented, deduplicated by proposition.
        """
        result = await self.connection.callback("IsaMini.potential_defs_of",
            (self.name, [n.ascii for n in constant_names]))
        return [IsabelleFact_Presented(full_name=full_name,
                        short_name=IsaTerm.from_isabelle(sname),
                        fact=FactByName(name=sname),
                        expression=[IsaTerm.from_isabelle(prop)],
                        is_conditional=is_cond)
                for full_name, sname, prop, is_cond in result]

    async def abbreviation_defs(self, full_names: list[str]) -> list[tuple[term, term] | None]:
        """Get pretty-printed abbreviation (lhs, rhs) pairs by full name.
        Returns None for non-abbreviation constants."""
        if not full_names:
            return []
        results = await self.connection.callback(
            "IsaMini.abbreviation_defs", (self.name, full_names))
        return [(IsaTerm.from_isabelle(r[0]), IsaTerm.from_isabelle(r[1]))
                if r is not None else None for r in results]

    async def check_looping_rules(self, fact_names: list[str],
                                   simplify_goal: bool,
                                   premise_names: list[str]
                                   ) -> list[tuple[int, str, list[tuple[str, lambda_term]]]]:
        """Check which user-provided rewrite rules are self-looping.
        Returns [(fact_index, rule_pretty, [(match_pretty, match_raw_term)])]
        for each looping rule with matching subterms in the rewrite targets."""
        if not fact_names:
            return []
        result = await self.connection.callback(
            "IsaMini.check_looping_rules",
            (self.name, fact_names, simplify_goal, premise_names))
        # Decode the agent-facing display strings (rule_pretty / match_pretty) at
        # the boundary; match_raw stays ascii — it is re-sent to Isabelle.
        return [(idx, pretty_unicode(rule_pretty),
                 [(pretty_unicode(mp), mr) for mp, mr in matches])
                for idx, rule_pretty, matches in result]

    async def validate_prove_in_time(self, statements: list[str]) -> list[str | None]:
        """Validate prove-in-time statements. Returns None per provable, error string per unprovable."""
        if not statements:
            return []
        session = the_session()
        session.on_operation_start(self.name, "PROVE_IN_TIME", statements)
        now = time()
        try:
            result = await self.connection.callback(
                "IsaMini.validate_prove_in_time", (self.name, statements))
            session.on_operation_end(self.name, "PROVE_IN_TIME", statements,
                EvaluationStatus.Success(time() - now))
            # Decode Isabelle RPC output at the boundary (same rule as
            # IsaTerm.from_isabelle / IsabelleError): these error strings carry
            # \<name> symbols that must render as unicode for the agent. Unlike
            # raised errors (wrapped by IsabelleError) this callback RETURNS its
            # text, so it must decode here.
            return [pretty_unicode(r) if r is not None else None for r in result]
        except IsabelleError as err:
            session.on_operation_end(self.name, "PROVE_IN_TIME", statements,
                EvaluationStatus.Failure(time() - now, FailureReason(''.join(err.errors))))
            raise

    async def concat_statement(self, fixes: list[tuple[str, str]],
                               assumes: list[str], concl: str) -> str:
        """Assemble for_any + premises + conclusion into a single Isabelle term string."""
        result = await self.connection.callback("IsaMini.concat_statement",
            (self.name,
             [(n, ascii_of_unicode(t)) for n, t in fixes],
             [ascii_of_unicode(a) for a in assumes],
             ascii_of_unicode(concl)))
        return pretty_unicode(result)

    async def fact_propositions(self, names: list[str]) -> list[tuple[str, str]]:
        """Resolve fact names to (name, standard-printed proposition) in this state's context.
        Names that don't resolve are dropped by the ML side. Propositions are raw Isabelle
        RPC strings; wrap with `IsaTerm.from_isabelle` at the call site."""
        if not names:
            return []
        return await self.connection.callback(
            "IsaMini.fact_propositions", (self.name, names))

### Interaction

# Helper shared by the `Interaction.answer` overrides: the "range-check +
# BadAnswer" pattern around candidate indexing, stated once. Raises
# `Interaction_BadAnswer` (defined below) at runtime, so declaration order
# doesn't matter.

def _check_index(idx: int, length: int) -> None:
    """Raise `Interaction_BadAnswer` if `idx` is out of `[0, length)`."""
    if idx < 0 or idx >= length:
        raise Interaction_BadAnswer(
            f"Index {idx} out of range (0–{length - 1}).")


class ForkingMode(Enum):
    FORKING_WITH_CTXT = 1         # fork inheriting parent conversation context
    FORKING_WITHOUT_CTXT = 2      # fork with fresh context, same model (opus)
    FORKING_CHEAPER_NO_CTXT = 3   # fork with fresh context, cheaper model (sonnet)

class InteractiveRetrievalMode(Enum):
    NO = "no"                                        # direct-append, no fork
    YES = "yes"                                      # fork-based, answer tool only
    YES_WITH_RECURSIVE_RETRIEVAL = "yes_recursive"   # fork-based, can also search

INTERACTIVE_RETRIEVAL_MAP = {m.value: m for m in InteractiveRetrievalMode}

# --- Typed answer payloads (one per answer tool variant) ---

@dataclass(frozen=True)
class AnswerIndexes:
    indexes: list[int]

@dataclass(frozen=True)
class AnswerIndex:
    index: int | None

@dataclass(frozen=True)
class AnswerIndexesOrName:
    indexes: list[int]
    name: str | None

@dataclass(frozen=True)
class AnswerIndexesOrSpec:
    indexes: list[int]
    statement: str | None

@dataclass(frozen=True)
class AnswerInstantiate:
    instantiations: list[tuple[str, str]]

@dataclass(frozen=True)
class AnswerRefutation:
    accept: bool
    reason: str

@dataclass(frozen=True)
class AnswerStruggleAssessment:
    is_stuck: bool
    summary: str

@dataclass(frozen=True)
class AnswerMissingLemmas:
    """Payload of `answer_missing_lemmas`: the missing-lemma survey's report.
    Each item is a plain dict (see tools/cc_answer_missing_lemmas.jsonc);
    an empty list means "nothing is missing"."""
    missing_lemmas: list

@dataclass(frozen=True)
class AnswerConstraintRequest:
    """Payload of `answer_constraint_request`: the dispatcher's verdict on a
    worker's reported constraints (`Interaction_ReviewConstraint`). `verdict` is
    "accept" or "reject". On accept, `constraints` RE-STATES (precisely) the
    condition(s) to add as `{name, term}` items — possibly correcting the
    worker's loose proposals. `reason` explains a rejection, or what changed when
    an accept revised the proposals. See tools/cc_answer_constraint_request.jsonc."""
    verdict: str
    constraints: list  # list[{name, term}]
    reason: str

AnswerPayload = (AnswerIndexes | AnswerIndex | AnswerIndexesOrName
                 | AnswerIndexesOrSpec | AnswerInstantiate
                 | AnswerRefutation | AnswerStruggleAssessment
                 | AnswerMissingLemmas)

class DeletedEntry(NamedTuple):
    summary: str
    rendered_yaml: str
    was_proved: bool

# Abstract tool identifiers (driver-agnostic)
type tool = str
TOOL_EDIT:   tool = "edit"
TOOL_DELETE: tool = "delete"
TOOL_SEARCH: tool = "query"
TOOL_READ:   tool = "recall"
TOOL_RECALL_REMOVED: tool = "recall_removed"
TOOL_REQUEST_LEMMAS: tool = "request"
TOOL_REPORT: tool = "report"
TOOL_SUBAGENT: tool = "subagent"
TOOL_CLOSE_SUBAGENT: tool = "cancel_subagent"
TOOL_REFRESH: tool = "refresh"
TOOL_COMMENT: tool = "comment"

TOOL_ANSWER_INDEXES:        tool = "answer_indexes"
TOOL_ANSWER_INDEX:          tool = "answer_index"
TOOL_ANSWER_INDEXES_OR_NAME: tool = "answer_indexes_or_name"
TOOL_ANSWER_INDEXES_OR_SPEC: tool = "answer_indexes_or_spec"
TOOL_ANSWER_INSTANTIATE:    tool = "answer_instantiate"
TOOL_ANSWER_REFUTATION:     tool = "answer_refutation"
TOOL_ANSWER_STRUGGLE_ASSESSMENT: tool = "answer_struggle_assessment"
TOOL_ANSWER_MISSING_LEMMAS: tool = "answer_missing_lemmas"
TOOL_ANSWER_CONSTRAINT_REQUEST: tool = "answer_constraint_request"

ANSWER_TOOLS: frozenset[tool] = frozenset({
    TOOL_ANSWER_INDEXES, TOOL_ANSWER_INDEX, TOOL_ANSWER_INDEXES_OR_NAME,
    TOOL_ANSWER_INDEXES_OR_SPEC, TOOL_ANSWER_INSTANTIATE,
    TOOL_ANSWER_REFUTATION, TOOL_ANSWER_STRUGGLE_ASSESSMENT,
    TOOL_ANSWER_MISSING_LEMMAS, TOOL_ANSWER_CONSTRAINT_REQUEST,
})

ALL_PROOF_TOOLS: tuple[tool, ...] = (
    TOOL_EDIT, TOOL_DELETE, TOOL_COMMENT, TOOL_SEARCH, TOOL_READ,
    TOOL_RECALL_REMOVED, TOOL_REQUEST_LEMMAS, TOOL_REPORT,
    TOOL_SUBAGENT, TOOL_CLOSE_SUBAGENT, TOOL_REFRESH,
    *ANSWER_TOOLS,
)

class Interaction:
    forking: ForkingMode = ForkingMode.FORKING_WITH_CTXT
    # Subclasses MUST add exactly one ANSWER_TOOLS member (the answer tool the
    # fork uses to submit its result); the base default carries only `query`.
    # Enforced at class-definition time by `__init_subclass__` below.
    fork_allowed_tools: list[tool] = [TOOL_SEARCH]

    def __init_subclass__(cls, **kwargs):
        super().__init_subclass__(**kwargs)
        n = sum(1 for t in cls.fork_allowed_tools if t in ANSWER_TOOLS)
        if n != 1:
            raise TypeError(
                f"{cls.__name__}.fork_allowed_tools must declare exactly one "
                f"ANSWER_TOOLS member (the fork's answer tool); got {n} "
                f"in {cls.fork_allowed_tools}")

    @property
    def answer_tool_name(self) -> str:
        for t in self.fork_allowed_tools:
            if t in ANSWER_TOOLS:
                return t
        raise NotImplementedError(
            f"{type(self).__name__}.fork_allowed_tools must declare an "
            f"ANSWER_TOOLS member")

    @property
    def is_non_forking(self) -> bool:
        return False

    async def prompt(self, indent: int, file: MyIO) -> None:
        raise NotImplementedError("`prompt` must be implemented by subclass")
    async def answer(self, answer: Any) -> Any:
        raise NotImplementedError("`answer` must be implemented by subclass")

    async def _render_prompt(self) -> str:
        """Render this interaction's prompt into a string. Used to build the
        text carried by ContinuingInteraction (candidate-list expansion or a
        full interaction replacement)."""
        buf = StringIO()
        await self.prompt(0, MyIO(buf))
        return buf.getvalue()

class ImmediateAnswer(Exception):
    """Raised by prompt() when the interaction resolves without LLM input."""
    def __init__(self, answer: Any):
        self.answer = answer

class ContinuingInteraction(Exception):
    """Raised by answer() to keep the fork alive instead of resolving it. Either
    re-prompt the SAME interaction with ``new_prompt`` (e.g. after the candidate
    list has been expanded), OR replace the pending interaction entirely with
    ``new_interaction`` (its ``prompt()`` is auto-rendered for the fork). The
    fork remains active in both cases."""
    def __init__(self, new_prompt: 'str | None' = None,
                 new_interaction: 'Interaction | None' = None):
        self.new_prompt = new_prompt
        self.new_interaction = new_interaction

class Interaction_BadAnswer(Exception):
    """Raised when an answer to an interaction is invalid. The interaction remains active."""
    pass


class Interaction_ReviewRefutation(Interaction):
    """Review a Worker's claim that a goal is unprovable."""
    forking = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools = [TOOL_ANSWER_REFUTATION, TOOL_SEARCH]

    def __init__(self, target: 'NonLeaf_Node', complaint: Any,
                 worker_handle: 'WorkerHandle'):
        self.target = target
        self.complaint = complaint
        # The live worker awaiting this review. The WorkerHandle.run_until_yield
        # loop owns the post-review resume (reject) / wind-down (accept); this
        # interaction only records the planner's verdict.
        self.worker_handle = worker_handle

    async def prompt(self, indent: int, file: MyIO) -> None:
        goal = self.target.goal() if hasattr(self.target, 'goal') else None  # type: ignore[attr-defined]  — target is role.target (NonLeaf_Node), guarded by hasattr
        goal_str = f"\nGoal: {goal.conclusion.unicode}" if goal else ""
        file.write(
            f"A sub-agent attempted {the_session()._display_id(self.target.id)} but argues the goal is flawed — unprovable or extremely hard to prove as stated.{goal_str}\n\n"
            f"Complaint: {the_session()._postprocess_outbound_text(self.complaint.detail)}\n\n"
            f"Do you accept this complaint and want to revise the proof goal or your proof strategy? Use `{tn(TOOL_ANSWER_REFUTATION)}` with:\n"
            f"  - accept: true to accept (and revise the goal/strategy), false to reject\n"
            f"  - reason: explanation of your judgment\n")

    async def answer(self, answer: AnswerRefutation) -> 'tuple[bool, str | None]':
        the_session().log_interaction("refutation_review",
            f"target={self.target.id} accept={answer.accept} reason={answer.reason}")
        # Normalize the reason's step ids for its consumer's namespace before it
        # leaves the reviewer's session.  An ACCEPTED reason is stored absolute
        # (the dispatcher re-relativizes it at display); a REJECTED reason goes
        # straight to the refuting worker, so rebase it into the worker's scope
        # (rooted at ``self.target``) and reject any reference the worker cannot
        # see — mirroring the suggestions policy (planner input is corrected).
        reason = answer.reason
        if reason:
            if answer.accept:
                reason = the_session()._absolutize_text(reason)
            else:
                reason, external = the_session()._rebase_suggestion_ids(self.target, reason)
                if external:
                    raise Interaction_BadAnswer(
                        f"Your reason references steps the sub-agent cannot see "
                        f"({', '.join(external)}): it only sees its own sub-proof. Describe the "
                        f"facts by name or rephrase without citing those steps.")
        # Unblock the worker either way; the WorkerHandle.run_until_yield loop
        # acts on the verdict (accept → wind down, reject → resume in-loop).
        self.worker_handle.resolve_review(accepted=answer.accept, reason=reason)
        return (answer.accept, reason)

    @property
    def session(self) -> 'Session':
        return self.worker_handle.session


class Interaction_StruggleCheckpoint(Interaction):
    """Assess whether a worker is genuinely stuck or making slow progress.

    Spawned automatically when a worker's delete/edit counters hit the struggle
    thresholds.  The fork inherits the worker's conversation (its full attempt
    history) so it can judge real progress, and returns ``(is_stuck, summary)``."""
    forking = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools = [TOOL_ANSWER_STRUGGLE_ASSESSMENT]

    def __init__(self, target: 'NonLeaf_Node',
                 delete_count: int, edit_count: int,
                 checkpoint_number: int):
        self.target = target
        self.delete_count = delete_count
        self.edit_count = edit_count
        self.checkpoint_number = checkpoint_number

    async def prompt(self, indent: int, file: MyIO) -> None:
        session = the_session()
        file.write(
            f"You have been working for a while "
            f"({self.edit_count} edits, {self.delete_count} deletes).\n\n")
        session.quickview_proof_scope(indent, file)
        file.write(
            f"\nAre you stuck?\n"
            f"Call `{tn(TOOL_ANSWER_STRUGGLE_ASSESSMENT)}` with:\n"
            f"  - is_stuck: true if you are stuck, false if making progress\n"
            f"  - summary: brief assessment of your situation\n")

    async def answer(self, answer: 'AnswerStruggleAssessment') -> 'tuple[bool, str]':
        return (answer.is_stuck, answer.summary)


def _missing_lemma_survey_interval_from_env() -> int:
    """Query-call interval of the missing-lemma survey, from the environment
    variable ``AOA_MISSING_LEMMA_SURVEY``: unset/empty/"0"/"off"/"false"/"no"
    disables (returns 0); "on"/"yes"/"true" enables with the default interval
    (10); a positive integer enables with that interval. Read per top-level
    Session (forks inherit), so the value is fixed for one invocation but a
    host restart picks up a changed environment."""
    raw = os.environ.get("AOA_MISSING_LEMMA_SURVEY", "").strip().lower()
    if raw in ("", "0", "off", "false", "no"):
        return 0
    if raw in ("on", "yes", "true"):
        return 10
    try:
        return max(0, int(raw))
    except ValueError:
        # Fail CLOSED: an unparseable value (typo like "tru", "1.5") must not
        # silently enable an opt-in feature.
        return 0


def _load_missing_lemma_feedback() -> list:
    """Adjudication feedback the external missing-lemma loop's watcher writes
    for the survey (path via ``AOA_MISSING_LEMMA_FEEDBACK``; the watcher
    rewrites the file mid-run, so read at CALL time, never cache). Any
    failure — env unset, file missing, bad JSON, wrong shape — returns []:
    the survey must behave exactly as before for non-watcher users."""
    path = os.environ.get("AOA_MISSING_LEMMA_FEEDBACK")
    if not path:
        return []
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, list) else []
    except Exception:
        return []


_MISSING_LEMMA_FEEDBACK_OUTCOME = {
    "already_in_heap":
        "already exists as `{lemma_name}` in `{theory}` — use it",
    "provided_but_unfindable":
        "already provided as `{lemma_name}` in `{theory}` (a known retrieval "
        "issue) — use it directly",
    "not_found":
        "verified absent from both the distribution and the AFP; prove it "
        "yourself",
    "import_failed":
        "its theory cannot be imported into this environment; prove it "
        "yourself",
}
_MISSING_LEMMA_FEEDBACK_CAP = 30


def _missing_lemma_key(item: dict) -> str:
    """Dedup key matching the watcher ledger's claim_key convention: the
    normalized name guess (survey items say ``name_guess``, request_lemmas
    wish-list items say ``name``), english prefix as the nameless fallback."""
    name = str(item.get("name_guess") or item.get("name") or "").strip().lower()
    if name:
        return "name:" + re.sub(r"[^a-z0-9]+", "_", name)
    eng = str(item.get("english") or "").strip().lower()
    return "eng:" + re.sub(r"\s+", " ", eng)[:80]


def _render_missing_lemma_feedback(feedback: list, runtime_reported: list) -> str:
    """The survey prompt's "already reported" section (文案用户签字
    2026-06-12). Pure function over plain data; returns "" when there is
    nothing to say, so the prompt stays byte-identical to the pre-feedback
    behavior. The result is written as a LITERAL — callers must never run it
    through further f-string/format interpolation (lemma names and english
    statements are model-generated text and may contain braces)."""
    lines: list[str] = []
    seen: set[str] = set()

    def add(item: dict, outcome: str) -> None:
        name = str(item.get("name_guess") or item.get("name") or "").strip()
        english = str(item.get("english") or "").strip()[:200]
        if not (name or english):
            return  # nothing identifiable to render
        lines.append(f"- `{name}` — {english} → {outcome}")

    for item in feedback:
        if not isinstance(item, dict):
            continue
        key = _missing_lemma_key(item)
        if key in seen:
            continue
        seen.add(key)
        tmpl = _MISSING_LEMMA_FEEDBACK_OUTCOME.get(item.get("status"))
        outcome = (tmpl.format(lemma_name=item.get("lemma_name") or "?",
                               theory=item.get("theory") or "?")
                   if tmpl else
                   "already reported and processed — do not re-report")
        add(item, outcome)

    # Runtime entries (reported this run, not adjudicated yet): self-dedup
    # latest-wins — the model re-reports one fact under many names/wordings —
    # then dedup against the feedback above, cap to keep the prompt bounded.
    pending: list[dict] = []
    pending_seen: set[str] = set()
    for item in reversed(runtime_reported):
        if not isinstance(item, dict):
            continue
        key = _missing_lemma_key(item)
        if key in seen or key in pending_seen:
            continue
        pending_seen.add(key)
        pending.append(item)
    for item in reversed(pending[:_MISSING_LEMMA_FEEDBACK_CAP]):
        add(item, "reported, adjudication pending")

    if not lines:
        return ""
    return ("The facts below were ALREADY reported by you earlier in this "
            "run and processed. Do NOT report them again:\n\n"
            + "\n".join(lines) + "\n\n")


class Interaction_MissingLemmaSurvey(Interaction):
    """Ask the agent whether it needs general-purpose background lemmas that it
    could not find in the loaded libraries.

    Spawned every ``AOA_MISSING_LEMMA_SURVEY`` `query` tool calls, once before
    a worker winds down, and once before the main agent winds down if it made
    ≥1 query since its last survey (see ``Session.run_missing_lemma_survey``
    and the ``session_end`` trigger at ``toplevel.run_case``).
    The fork inherits the parent context — it must see the search history to
    judge what was looked for and not found — and may only answer; the report
    is recorded to ``missing_lemmas.yaml`` for the external import-expansion
    loop. Nothing is fed back into the proof: the anti-repeat feedback
    section below enters ONLY this fork's prompt (the fork can only answer),
    never the proof mainline."""
    forking = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools = [TOOL_ANSWER_MISSING_LEMMAS]

    def __init__(self, trigger: str):
        self.trigger = trigger

    async def prompt(self, indent: int, file: MyIO) -> None:
        # Anti-repeat feedback: best-effort and fail-open — the survey must
        # never break on a feedback-channel fault (same philosophy as
        # run_missing_lemma_survey itself).
        try:
            feedback_section = _render_missing_lemma_feedback(
                _load_missing_lemma_feedback(),
                list(the_session().runtime.reported_missing_lemmas))
        except Exception:
            feedback_section = ""
        file.write(
            f"[System checkpoint] Review your proof attempt and your search "
            f"history so far.\n\n"
            f"Are there background facts — lemmas, theorems, or definitions you "
            f"would expect a standard mathematical library (the Isabelle/HOL "
            f"distribution or the AFP) to provide — that you needed but could "
            f"NOT find with the `{tn(TOOL_SEARCH)}` tool?\n\n"
            f"Report ONLY general-purpose library facts (e.g. a classical "
            f"inequality, a property of a standard function), not "
            f"problem-specific steps you must prove yourself.\n\n")
        if feedback_section:
            file.write(feedback_section)  # literal — never re-interpolated
        file.write(
            f"Call `{tn(TOOL_ANSWER_MISSING_LEMMAS)}` with one entry per "
            f"missing fact — or an empty `missing_lemmas` array if nothing is "
            f"missing. For each entry give your best-guess conventional name, "
            f"a precise English statement, an Isabelle statement sketch if you "
            f"can write one, the query descriptions that failed to find it, "
            f"and why your proof needs it.\n\n"
            f"State each fact in its MOST GENERAL, reusable form — "
            f"quantified over arbitrary variables / functions / intervals "
            f"— NOT specialised to the concrete values of your current "
            f"goal. E.g. report the general \"for continuous f on [a,b], the "
            f"uniform Riemann sum (b-a)/n·Σ f(a+i(b-a)/n) tends to "
            f"∫ f over [a,b]\", NOT the instance for your specific "
            f"function and interval. The `english` / `isabelle_statement` "
            f"fields hold the GENERAL statement; put the specific instance you "
            f"actually need (and why) in `why_needed`.\n")

    async def answer(self, answer: 'AnswerMissingLemmas') -> list:
        return answer.missing_lemmas


class Interaction_DifficultyEvaluation(Interaction):
    """Non-forking interaction presented to the parent agent when a system
    checkpoint detects that a worker is struggling.  The parent evaluates the
    target step's importance and chooses to let the worker continue or to
    abandon the step (auto-cancel + comment out)."""
    fork_allowed_tools = [TOOL_ANSWER_INDEX]

    @property
    def is_non_forking(self) -> bool:
        return True

    def __init__(self, target: 'NonLeaf_Node', detail: str):
        self.target = target
        self.detail = detail

    async def prompt(self, indent: int, file: MyIO) -> None:
        session = the_session()
        file.write(
            f"A system checkpoint detected that the sub-agent on step "
            f"{session._display_id(self.target.id)} is struggling:\n\n"
            f"{self.detail}\n\n"
            f"Current proof state:\n")
        session.quickview_proof_scope(indent, file)
        file.write(
            f"\nEvaluate this step's importance in the overall proof.\n\n"
            f"  0. Continue — let the sub-agent keep trying\n"
            f"  1. Abandon — cancel the sub-agent and comment out this step\n\n"
            f"Call `{tn(TOOL_ANSWER_INDEX)}` with your choice.\n")

    async def answer(self, answer: 'AnswerIndex') -> int:
        if answer.index is None:
            return 0
        _check_index(answer.index, 2)
        return answer.index


async def _validate_constraint_term(target: 'NonLeaf_Node', name: str,
                                    term: xterm) -> 'str | None':
    """§2a' pre-validation for a constraint the dispatcher accepted, to be added
    as a premise of `target` (an amendable Have/SetupRewriting). Returns an error
    message (dispatcher-facing, for an ``Interaction_BadAnswer`` re-prompt) or
    ``None`` when it passes all three gates:
      1. PARSE/TYPE — ``check_term`` succeeds;
      2. IS-A-PROPOSITION — its type is ``bool``/``prop`` (read off the SAME
         ``check_term`` return — pure Python, no extra ML round-trip);
      3. SCOPE — every free variable is in scope (the target's ``for_any`` vars, or
         the enclosing context); no schematic.
    Parsed against ``target._state_after_beginning()``. The enclosing-context vars
    are FIXED there (not free), but the target's ``for_any`` vars are BOUND in the
    goal (``⋀x. …``, not fixed in the context — ``goal.context.vars`` is empty for a
    ``for_any`` Have), so ``check_term`` reports them as frees; we ALLOW exactly
    those (plus the enclosing fixed vars, which never surface as frees). A free that
    is NEITHER is genuinely undeclared → reject (the OPPOSITE policy from
    ``general_lemmas``: there an undeclared free means "declare it"; here it means
    the constraint references something out of scope). A bad constraint is rejected
    BEFORE any tree mutation; the in-place ``add_constraints`` revert is the
    defence-in-depth backstop."""
    state = target._state_after_beginning()  # type: ignore[attr-defined]  — only ever an amendable StdBlock (Have/SetupRewriting)
    if not state.initialized():
        # No usable state to anchor the parse — defer to add_constraints'
        # re-refresh (which reverts on failure). Lenient: never a false reject.
        return None
    try:
        term_type, frees, schematics = await state.check_term(term)
    except InternalError_UnparsedTerm as e:
        return f"The constraint `{name}` does not parse as an Isabelle term: {e.reason}"
    except IsabelleError as e:
        if e.errors and str(e.errors[0]).startswith("Unparsed"):
            return f"The constraint `{name}` does not parse as an Isabelle term."
        raise
    if term_type.unicode not in ("bool", "prop"):
        return (f"The constraint `{name}` is not a proposition — its type is "
                f"`{term_type.unicode}`. A constraint must be a true/false "
                f"statement (a `bool`).")
    # The target's for_any vars are legitimate frees here (bound in its goal); any
    # OTHER free is undeclared. Schematics are always rejected.
    allowed = {n.unicode for n, _ in getattr(target, "for_any", [])}
    bad = [f.unicode for f in frees if f.unicode not in allowed]
    bad += [s.unicode for s in schematics]
    if bad:
        vlist = ", ".join(f"`{b}`" for b in bad)
        return (f"The constraint `{name}` references undeclared variable(s) "
                f"{vlist}. A constraint may only use variables already in the "
                f"sub-goal's scope, not introduce new ones.")
    return None


class Interaction_ReviewConstraint(Interaction):
    """Non-forking interaction: a worker reported that its sub-goal is missing
    CONSTRAINTS (conditions it needs but was not given when dispatched); the
    dispatcher — who owns the proof structure — adjudicates. Surfaces to the
    dispatcher via the channel and is resolved IN-LOOP in
    ``WorkerHandle.run_until_yield`` (never a park yield, so §B holds for a
    headless prover). ``answer`` returns ``(kind, feedback)``:
      - ``("reject", worker_msg)`` — the worker resumes with the rejection;
      - ``("accept_amended", worker_msg)`` — for an AMENDABLE target
        (Have/SetupRewriting): the re-stated constraint(s) are validated and
        added IN PLACE here (the fact becomes conditional), and the worker
        resumes with them in scope;
      - ``("accept_restructure", dispatcher_msg)`` — for a NON-amendable target
        (Obtain/Suffices): the constraints can't be added as premises, so the
        worker PARKS and the dispatcher reworks the proof structure."""
    fork_allowed_tools = [TOOL_ANSWER_CONSTRAINT_REQUEST]

    @property
    def is_non_forking(self) -> bool:
        return True

    def __init__(self, target: 'NonLeaf_Node', constraints: list,
                 worker_handle: 'WorkerHandle'):
        self.target = target
        self.constraints = constraints  # list[RequestConstraint] {description, proposition}
        self.worker_handle = worker_handle

    async def prompt(self, indent: int, file: MyIO) -> None:
        session = the_session()
        sid = session._display_id(self.target.id)
        file.write(f"The sub-agent on step `{sid}` reports its sub-goal is missing:\n")
        for c in self.constraints:
            desc = (c.get("description") or "").replace("\n", " ")
            prop = c.get("proposition") or ""
            file.write(f"  - {desc}: {prop}\n")
        if self.target.can_add_constraints():
            file.write(f"Accepting adds these as premises of step `{sid}` "
                       f"(its fact becomes conditional).\n")
        else:
            file.write(f"Step `{sid}` cannot take added premises — accepting "
                       f"means its proof plan needs restructuring, which you will "
                       f"do once the sub-agent suspends.\n")
        file.write("`accept` (these conditions are genuinely needed) or `reject`?\n")

    async def answer(self, answer: 'AnswerConstraintRequest') -> 'tuple[str, str]':
        the_session().log_interaction("constraint_review",
            f"target={self.target.id} verdict={answer.verdict}")
        verdict = (answer.verdict or "").strip().lower()
        reason = (answer.reason or "").strip()
        if verdict == "reject":
            if not reason:
                raise Interaction_BadAnswer(
                    "A `reason` is required when you reject — explain why the "
                    "sub-agent does not actually need the reported condition(s).")
            if not reason.endswith((".", "!", "?")):
                reason += "."
            return ("reject", f"Your request is rejected because: {reason}")
        if verdict != "accept":
            raise Interaction_BadAnswer('`verdict` must be "accept" or "reject".')
        # accept — restated constraints are required.
        restated = answer.constraints or []
        if not restated:
            raise Interaction_BadAnswer(
                "When you `accept`, restate the constraint(s) to add in "
                "`constraints` — each with a `name` and an Isabelle `term`.")
        parsed: list[PremiseBinding] = []
        for c in restated:
            if not isinstance(c, dict):
                raise Interaction_BadAnswer(
                    "Each constraint must be an object with `name` and `term`.")
            nm = (c.get("name") or "").strip()
            tm = c.get("term")
            if not nm or not isinstance(tm, str) or not tm.strip():
                raise Interaction_BadAnswer(
                    "Each accepted constraint needs a non-empty `name` and `term`.")
            parsed.append({"name": nm, "term": tm})
        target = self.target
        if target.can_add_constraints():
            for c in parsed:
                err = await _validate_constraint_term(target, c["name"], c["term"])
                if err is not None:
                    raise Interaction_BadAnswer(err)
            fail = await target.add_constraints(parsed)
            if fail is not None:
                raise Interaction_BadAnswer(fail)
            fb = "Your reported condition(s) were accepted and added to your goal."
            if reason:
                fb += f" {reason}"
            return ("accept_amended", fb)
        # NON-amendable target: the constraints are advisory (a thinking aid that
        # articulates the missing condition); the fix is restructuring, done by
        # the dispatcher once the worker parks. Validate leniently (no mutation).
        rendered = "; ".join(f"{c['name']}: {c['term']}" for c in parsed)
        detail = rendered
        if reason:
            detail += f"\nNote: {reason}"
        return ("accept_restructure", detail)


# Large-delete confirmation gate: both thresholds must be met (AND) over the
# merged stats of all targets of one delete call (nested targets deduped).
LARGE_DELETE_PROVED_THRESHOLD = 5
LARGE_DELETE_TOTAL_THRESHOLD = 10


class Interaction_ConfirmLargeDelete(Interaction):
    """Confirmation gate for deletions that would discard substantial
    completed proof work (see the ``LARGE_DELETE_*`` thresholds). Non-forking:
    the same agent that issued the ``delete`` answers inline, mid-call. The
    answer is ``"comment"`` / ``"cancel"`` / ``"proceed"``; a ``null`` index
    takes the recommended option (comment when available, else cancel).
    ``comment_available`` is False when a target is a structural container
    that ``Root.comment`` rejects — the comment option is then omitted."""
    fork_allowed_tools = [TOOL_ANSWER_INDEX]

    @property
    def is_non_forking(self) -> bool:
        return True

    def __init__(self, entries: 'list[tuple[step, int, int]]',
                 comment_available: bool):
        # entries: (absolute id, subtree total, subtree proved)
        self.entries = entries
        self.comment_available = comment_available

    async def prompt(self, indent: int, file: MyIO) -> None:
        session = the_session()
        singular = len(self.entries) == 1
        noun = "a step" if singular else f"{len(self.entries)} steps"
        file.write(
            f"You are about to delete {noun} containing substantial completed work:\n")
        for sid, total, proved in self.entries:
            op_noun = "operation" if total == 1 else "operations"
            file.write(
                f"  - step {session._display_id(sid)},"
                f" total {total} {op_noun}, {proved} proved\n")
        file.write(
            "This would discard a large amount of your previous proof work.\n\n"
            "Please reconsider whether you want to:\n")
        if self.comment_available:
            if singular:
                file.write(
                    "  0. Comment the step out instead (recommended) — it remains visible\n"
                    "     and can be restored later with `uncomment`.\n")
            else:
                file.write(
                    "  0. Comment the steps out instead (recommended) — they remain visible\n"
                    "     and can be restored later with `uncomment`.\n")
            file.write(
                "  1. Cancel the deletion and keep everything as is.\n"
                "  2. Proceed with the deletion anyway.\n")
        else:
            file.write(
                "  0. Cancel the deletion and keep everything as is.\n"
                "  1. Proceed with the deletion anyway.\n")

    async def answer(self, answer: 'AnswerIndex') -> str:
        if self.comment_available:
            if answer.index is None:
                return "comment"
            _check_index(answer.index, 3)
            return ("comment", "cancel", "proceed")[answer.index]
        if answer.index is None:
            return "cancel"
        _check_index(answer.index, 2)
        return ("cancel", "proceed")[answer.index]


class Fork_Pending(NamedTuple):
    """Carried by a fork session during its single-interaction lifetime.

    ``answer`` is the slot where the LLM's reply lands: the ``answer`` MCP
    tool completes it with the value returned by ``interaction.answer(...)``,
    and the fork's run loop reads it back. ``answer.done()`` doubles as the
    "already answered" predicate used to reject duplicate ``answer`` calls.

    (An ``asyncio.Future`` is used for the slot because it is the stdlib
    one-shot set-once container; the future is never awaited — only polled.)
    """
    interaction: Interaction
    answer: asyncio.Future[Any]


# --- Non-forking interaction channel ---

class InteractionPrompt(NamedTuple):
    interaction: Interaction
    text: str

class InteractionError(NamedTuple):
    text: str

class EditResult(NamedTuple):
    text: str
    is_error: bool

# Outbox message (tool task → executor); see InteractionChannel.
type executor_msg = InteractionPrompt | InteractionError | EditResult

class InteractionChannel:
    """Persistent bidirectional channel between a tool task and ToolExecutor.

    ``outbox`` (tool task → executor): an ``executor_msg`` — ``InteractionPrompt``,
    ``InteractionError``, or ``EditResult``.
    ``inbox`` (executor → tool task): parsed ``AnswerPayload``.
    """
    def __init__(self):
        self.outbox: asyncio.Queue = asyncio.Queue(maxsize=1)
        self.inbox: asyncio.Queue = asyncio.Queue(maxsize=1)


#### Fact Retrieval

_THEOREM_KINDS = frozenset({EntityKind.THEOREM, EntityKind.INTRODUCTION_RULE, EntityKind.ELIMINATION_RULE})

async def _try_resolve_as_named_fact(
    state: 'Minilang_State', name: str
) -> 'IsabelleFact_Presented | None':
    """Try to resolve free text as an accessible named theorem. Returns None if not found."""
    results = await state._retrieve_entity([(EntityKind.THEOREM, name)])
    result = results[0]
    if result is not None:
        short_name, exprs, roles, abbrev, is_local = result
        # Off-menu name resolution has no ML is_conditional flag (that arrives only
        # via the potential_defs_of callback); detect a premise from the rendered
        # prop as a best-effort instead — a conditional def shows a top-level
        # implication, rendered as Pure ⟹ (U+27F9) or object ⟶ (U+27F6).
        is_conditional = any(('⟹' in e.unicode) or ('⟶' in e.unicode) for e in exprs)
        return IsabelleFact_Presented(
            full_name=name, short_name=short_name,
            fact=FactByName(name=name),
            expression=exprs, roles=roles, abbreviation_names=abbrev,
            is_local=is_local, is_conditional=is_conditional)
    return None

_retrieval_db_conn: sqlite3.Connection | None = None

def _get_retrieval_db() -> sqlite3.Connection:
    global _retrieval_db_conn
    if _retrieval_db_conn is None:
        cache_dir = platformdirs.user_cache_dir("Isabelle_Semantic_Embedding", "Qiyuan")
        db_dir = os.path.join(cache_dir, "AoA_Collected")
        os.makedirs(db_dir, exist_ok=True)
        _retrieval_db_conn = sqlite3.connect(os.path.join(db_dir, "retrieval_training.db"))
        _retrieval_db_conn.execute("""CREATE TABLE IF NOT EXISTS retrieval_events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            timestamp TEXT NOT NULL,
            query TEXT NOT NULL,
            kinds TEXT NOT NULL,
            interaction_type TEXT NOT NULL,
            candidates TEXT NOT NULL,
            selected_indices TEXT NOT NULL,
            prove_in_time TEXT
        )""")
    return _retrieval_db_conn

FORKING_MODE_MAP = {
    "cheaper_no_ctxt": ForkingMode.FORKING_CHEAPER_NO_CTXT,
    "with_ctxt": ForkingMode.FORKING_WITH_CTXT,
    "without_ctxt": ForkingMode.FORKING_WITHOUT_CTXT,
}

class Interaction_Retrieve(Interaction):
    """Base class for interactive entity retrieval via forked agent."""
    INITIAL_K = 40
    FINAL_K = 40

    def __init__(self, state: Minilang_State,
            query: str, kinds: list[EntityKind],
            *,
            initial_k: int | None = None,
            single_choice: bool = False,
            term_patterns: list[str] | None = None,
            type_patterns: list[str] | None = None,
            theories_include: list[str] | None = None,
            name_contains: list[str] | None = None,
            target_type: str = "",
    ):
        self.query = query
        self.state = state
        self.k = initial_k or self.INITIAL_K
        self.kinds = kinds
        self.single_choice = single_choice
        self.term_patterns = term_patterns or []
        self.type_patterns = type_patterns or []
        self.theories_include = theories_include or []
        self.name_contains = name_contains or []
        self.target_type = target_type
        self._candidate_facts_cache: list[RetrievedEntity] | None = None
        # Empty query forces FORKING_WITH_CTXT (fork needs parent context to judge relevance)
        session = the_session()
        if not query:
            self.forking = ForkingMode.FORKING_WITH_CTXT
        else:
            self.forking = session.retrieval_forking_mode
        # Tool access in forks: YES = answer only, YES_RECURSIVE = answer + query (default)
        if session.interactive_retrieval == InteractiveRetrievalMode.YES:
            self.fork_allowed_tools = [TOOL_ANSWER_INDEXES]

    async def candidate_facts(self) -> list[RetrievedEntity]:
        if self._candidate_facts_cache is None:
            self._candidate_facts_cache, _ = await self.state.semantic_knn(
                self.query, self.k, self.kinds,
                term_patterns=self.term_patterns,
                type_patterns=self.type_patterns,
                theories_include=self.theories_include,
                name_contains=self.name_contains,
                target_type=self.target_type)
        return self._candidate_facts_cache

    def _entity_title(self) -> str:
        """Dynamic title for the entity kind(s): 'theorems', 'constants', etc."""
        _KIND_TERMS = {
            EntityKind.THEOREM: "theorems", EntityKind.CONSTANT: "constants",
            EntityKind.TYPE: "types", EntityKind.CLASS: "typeclasses",
            EntityKind.LOCALE: "locales",
            EntityKind.THEOREM_COLLECTION: "named theorem bundles",
            EntityKind.INTRODUCTION_RULE: "introduction rules",
            EntityKind.ELIMINATION_RULE: "elimination rules",
            EntityKind.INDUCTION_RULE: "induction rules",
            EntityKind.CASE_SPLIT_RULE: "case-split rules",
        }
        if len(self.kinds) == 1:
            return _KIND_TERMS.get(self.kinds[0], "entities")
        return "entities"

    async def _prompt_candidates(self, indent: int, file: MyIO) -> None:
        """Shared: render the numbered candidate list (without header)."""
        facts = await self.candidate_facts()
        if not facts:
            raise ImmediateAnswer([])
        for i, fetched in enumerate(facts):
            exprs = fetched.entity.expression
            print_indent(indent+1, file)
            if exprs:
                file.write(f"{i}. {fetched.entity.short_name.unicode}:")
                truncated = print_expression_list(indent+2, file, exprs)
            else:
                file.write(f"{i}. {fetched.entity.short_name.unicode}\n")
                truncated = False
            if fetched.interpretation and (fetched.entity.kind not in _THEOREM_KINDS or truncated):
                print_indent(indent+2, file)
                file.write(f"{fetched.interpretation}\n")

    async def _log_retrieval_training_data(self, selected_indices: list[int],
                                           prove_in_time: str | None = None) -> None:
        """Log retrieval event to the training DB for embedding model improvement."""
        try:
            facts = await self.candidate_facts()
            selected_set = set(selected_indices)
            candidates = json.dumps([
                {"full_name": f.entity.full_name, "score": f.score,
                 "expression": [e.unicode for e in f.entity.expression],
                 "selected": i in selected_set}
                for i, f in enumerate(facts)
            ])
            conn = _get_retrieval_db()
            conn.execute(
                "INSERT INTO retrieval_events "
                "(timestamp, query, kinds, interaction_type, candidates, selected_indices, prove_in_time) "
                "VALUES (?, ?, ?, ?, ?, ?, ?)",
                (datetime.utcnow().isoformat(), self.query,
                 json.dumps([k.label for k in self.kinds]),
                 type(self).__name__, candidates,
                 json.dumps(selected_indices), prove_in_time))
            conn.commit()
        except Exception as e:
            logging.getLogger(__name__).warning(f"Failed to log retrieval training data: {e}")

    async def prompt(self, indent: int, file: MyIO) -> None:
        raise NotImplementedError("subclasses must override prompt()")

    fork_allowed_tools = [TOOL_ANSWER_INDEXES, TOOL_SEARCH]

    async def answer(self, answer: AnswerIndexes) -> 'list[IsabelleEntity | IsabelleFact]':
        if not answer.indexes:
            if self.k < self.FINAL_K:
                self.k = self.FINAL_K
                self._candidate_facts_cache = None
                await self.candidate_facts()
                raise ContinuingInteraction(await self._render_prompt())
            else:
                await self._log_retrieval_training_data([])
                the_session().log_retrieval(self.query, ["none selected"])
                return []
        if self.single_choice and len(answer.indexes) > 1:
            raise Interaction_BadAnswer("Please select exactly one entry.")
        facts = await self.candidate_facts()
        selected: list[IsabelleEntity] = []
        for idx in answer.indexes:
            _check_index(idx, len(facts))
            selected.append(facts[idx].entity)
        await self._log_retrieval_training_data(list(answer.indexes))
        session = the_session()
        results = []
        for e in selected:
            expr = ", ".join(x.unicode for x in e.expression) if e.expression else ""
            results.append(f"{e.short_name.unicode}: {expr}" if expr else e.short_name.unicode)
        session.log_retrieval(self.query, results)
        return cast(list[IsabelleEntity | IsabelleFact], selected)


class Interaction_RetrieveForProof(Interaction_Retrieve):
    """Retrieve theorems/rules for proof operations. Supports prove-in-time and relevant constants."""

    def __init__(self, state: Minilang_State,
            query: str, kinds: list[EntityKind],
            **kwargs: Any):
        super().__init__(state, query, kinds, **kwargs)
        self._relevant_constants_cache: 'list[tuple[short_name, str, str | None]] | None' = None

    async def relevant_constants(self) -> 'list[tuple[short_name, str, str | None]]':
        """Fetch relevant constants via semantic search (cached).
        Returns list of (short_name, type, interpretation) triples."""
        if self._relevant_constants_cache is None:
            results, _ = await self.state.semantic_knn(self.query, 10, [EntityKind.CONSTANT])
            cache = [
                (r.entity.short_name,
                 r.entity.expression[0].unicode if r.entity.expression else "",
                 r.interpretation)
                for r in results if r.score >= 0.5]
            self._relevant_constants_cache = cache
        return self._relevant_constants_cache

    async def prompt(self, indent: int, file: MyIO) -> None:
        title = self._entity_title()
        print_indent(indent, file)
        file.write(f"You are looking for {title} establishing:")
        print_paragraph(indent, file, self.query)
        file.write("\n")
        constants = await self.relevant_constants()
        if constants:
            file.write("Relevant constants in scope:\n")
            for short_name, typ, interp in constants:
                print_indent(indent+1, file)
                file.write(f"- {short_name.unicode}: {typ}\n")
                if interp:
                    print_indent(indent+2, file)
                    file.write(f"{interp}\n")
            file.write("\n")
        file.write(f"Similar {title} from the library:\n")
        await self._prompt_candidates(indent, file)
        _atn = tn(TOOL_ANSWER_INDEXES_OR_SPEC)
        if self.single_choice:
            file.write(f"\nIf an entry above matches what you need, call `{_atn}` with its index.\n")
        else:
            file.write(f"\nCall `{_atn}` with the `indexes` of all matching {title}.\n")
        file.write(f"Otherwise, if none matches but the statement is trivially provable, "
                   f"formalize the statement into Isabelle propositions and call `{_atn}` with `statement`. "
                   "IMPORTANT: all numeric literals MUST be type-annotated, "
                   "example: `(2::nat)` not `2`.\n")
        if self.k >= self.FINAL_K:
            file.write(f"If none of the above applies, call `{_atn}` with no fields to give up "
                       "the search and prove the statement yourself later.\n")
        else:
            file.write(f"If none of the above applies, call `{_atn}` with no fields to see more candidates.\n")

    fork_allowed_tools = [TOOL_ANSWER_INDEXES_OR_SPEC, TOOL_SEARCH]

    async def answer(self, answer: AnswerIndexesOrSpec) -> 'list[IsabelleEntity | IsabelleFact]':  # type: ignore[override]  — intentionally accepts a richer answer shape than the base
        """Priority order: indexes > statement (> empty-expand).

        `indexes`   → select from the candidate list (delegates to super).
        `statement` → prove-in-time: treat as a new proposition to prove
                      inline (only when indexes is empty).
        (all empty) → expand the candidate list, or give up on the second
                      empty answer (delegates to super)."""
        session = the_session()
        if answer.statement is not None and not answer.indexes:
            await self._log_retrieval_training_data([], prove_in_time=answer.statement)
            session.log_retrieval(self.query, [f"prove-in-time: {answer.statement}"])
            return [IsabelleFact_ProveInTime(IsaTerm.from_agent(answer.statement),
                                              assigned_name=the_session().next_pit_name())]
        if not answer.indexes and answer.statement is None and self.k >= self.FINAL_K:
            await self._log_retrieval_training_data([])
            session.log_retrieval(self.query, ["unfound"])
            if self.single_choice:
                return [IsabelleFact_Unfound(
                    FactByDescription(english=self.query))]
            return []
        return await super().answer(AnswerIndexes(indexes=answer.indexes))


def _validate_instantiation_answer(
        answer: 'AnswerInstantiate',
        schematic_vars: 'list[tuple[str, str]]') -> 'list[tuple[str, str]]':
    """Shared front-half validation for an `answer_instantiate` response:
    require a non-empty `instantiations`, reject duplicate / missing / unknown
    variable names against `schematic_vars`, and return the (name, value) pairs
    ordered to match `schematic_vars`. Raises Interaction_BadAnswer on any
    violation."""
    if not answer.instantiations:
        names = ", ".join(n for n, _ in schematic_vars)
        raise Interaction_BadAnswer(
            f"This interaction requires `instantiations` for variables: {names}.")
    required = {n for n, _ in schematic_vars}
    provided: set[str] = set()
    by_name: dict[str, str] = {}
    for v, t in answer.instantiations:
        if v in provided:
            raise Interaction_BadAnswer(f"Variable `{v}` was instantiated twice.")
        provided.add(v)
        by_name[v] = t
    missing = required - provided
    if missing:
        raise Interaction_BadAnswer(
            f"Missing instantiations for: {', '.join(sorted(missing))}.")
    extra = provided - required
    if extra:
        sorted_extra = [f"`{v}`" for v in sorted(extra)]
        if len(sorted_extra) >= 3:
            joined = ", ".join(sorted_extra[:-1]) + ", and " + sorted_extra[-1]
        elif len(sorted_extra) == 2:
            joined = " and ".join(sorted_extra)
        else:
            joined = sorted_extra[0]
        plural = "variables" if len(sorted_extra) > 1 else "variable"
        raise Interaction_BadAnswer(
            f"Unknown schematic {plural}: {joined}. "
            f"Expected one of: {', '.join(f'`{v}`' for v in sorted(required))}.")
    return [(n, by_name[n]) for n, _ in schematic_vars]


class Interaction_InstantiateSchematics(Interaction):
    """Prompt the LLM to instantiate schematic variables of an induction /
    case-split rule.

    The pre-flight `IsaMini.analyze_induct` / `analyze_case_split` callback
    reports schematic variables appearing in the rule's consume premises.
    Under `consumes_policy = subgoals`, unconsumed premises are surfaced as
    `Prem<i>` subgoals, but only when they contain no schematic variables;
    this interaction closes that gap by asking the agent to make them
    concrete before the rule is applied.

    Consumes the `instantiations` field of `AnswerInstantiate`. Every
    schematic variable listed in `schematic_vars` must appear exactly once
    in the answer. Non-forking: the agent that issued the
    ``Induction``/``CaseSplit`` answers inline, mid-edit."""

    @property
    def is_non_forking(self) -> bool:
        return True

    def __init__(self,
                 state: 'Minilang_State',
                 rule_name: IsaTerm,
                 consume_premises: list[str],
                 schematic_vars: list[tuple[str, str]],
                 kind: Literal["induction", "case-split"]):
        self.state = state
        self.rule_name = rule_name
        self.consume_premises = consume_premises
        self.schematic_vars = schematic_vars
        self.kind = kind

    async def prompt(self, indent: int, file: MyIO) -> None:
        kind_word = "induction" if self.kind == "induction" else "case-split"
        n_vars = len(self.schematic_vars)
        print_indent(indent, file)
        file.write(
            f"The {kind_word} rule `{self.rule_name.unicode}` has "
            f"{'a schematic variable' if n_vars == 1 else f'{n_vars} schematic variables'} "
            "that must be instantiated before the rule can be applied:\n")
        for name, typ in self.schematic_vars:
            print_indent(indent + 1, file)
            file.write(f"- {name} :: {typ}\n")
        print_indent(indent, file)
        noun = "variable appears" if n_vars == 1 else "variables appear"
        file.write(f"The {noun} in the rule premises:\n")
        for i, prem in enumerate(self.consume_premises):
            print_indent(indent + 1, file)
            file.write(f"{i}. {prem}\n")
        print_indent(indent, file)
        file.write(f"Call `{tn(TOOL_ANSWER_INSTANTIATE)}` with `instantiations`, a list of "
                   "{variable, term} objects. Each term must be a "
                   "type-correct Isabelle expression.\n")

    fork_allowed_tools = [TOOL_ANSWER_INSTANTIATE, TOOL_SEARCH]

    async def answer(self, answer: AnswerInstantiate) -> IsaTerm:
        insts = _validate_instantiation_answer(answer, self.schematic_vars)
        err: str | None = await self.state.connection.callback(
            "IsaMini.validate_instantiation",
            (self.state.name, self.rule_name.ascii, insts))
        if err is not None:
            raise Interaction_BadAnswer(
                f"Instantiation rejected by Isabelle:\n{pretty_unicode(err)}")
        where_parts = " and ".join(
            f"{v} = \N{SINGLE LEFT-POINTING ANGLE QUOTATION MARK}{t}\N{SINGLE RIGHT-POINTING ANGLE QUOTATION MARK}"
            for v, t in insts)
        rule_src = f'"{self.rule_name.unicode}"[xwhere {where_parts}]'
        return IsaTerm.from_agent(rule_src)


class Interaction_InstantiatePostSchematics(Interaction):
    """Non-forking: after a RULE / CaseSplit / Induction op runs, residual
    schematic variables may still occur in some open subgoal (the rule's
    schematics were not all pinned by unification). This asks the agent —
    inline, mid-edit — to instantiate them so the operation produces a
    schematic-free state.

    Fired by the probe loop in `SubgoalMaker._execute_opr`, once per round,
    term variables first and then any remaining type variables (a term value
    pins most type vars via `infer_instantiate`); the loop re-detects after each
    round, so an under-instantiating or type-reintroducing round is caught next
    time. `answer` returns the round as a `list[(name, value)]`; the probe
    accumulates the rounds and bakes them into the op's `_post_insts` so the op
    replays deterministically from cache.

    Parameterized by `kind`: "term" offers `?x :: τ` and collects a term for
    each; "type" offers `?'a :: sort` and collects a type for each. The "type"
    prompt is self-contained — a pure-type-var goal hits it as the first/only
    interaction, with no preceding term round."""

    @property
    def is_non_forking(self) -> bool:
        return True

    fork_allowed_tools = [TOOL_ANSWER_INSTANTIATE, TOOL_SEARCH]

    def __init__(self,
                 state: 'Minilang_State',
                 schematic_vars: list[tuple[str, str]],
                 kind: Literal["term", "type"]):
        self.state = state
        self.schematic_vars = schematic_vars
        self.kind = kind

    async def prompt(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        if self.kind == "term":
            file.write(
                "The proof goal contains schematic variables that must be "
                "instantiated before you can continue:\n")
        else:
            file.write(
                "The proof goal contains schematic type variables that are not "
                "yet determined and must be instantiated before you can continue:\n")
        for name, ty in self.schematic_vars:
            print_indent(indent + 1, file)
            file.write(f"- {name} :: {ty}\n")
        print_indent(indent, file)
        if self.kind == "term":
            file.write(
                f"Call `{tn(TOOL_ANSWER_INSTANTIATE)}` with `instantiations`, a list of "
                "{variable, term} objects; each `term` must be a type-correct Isabelle "
                "expression.\n")
        else:
            file.write(
                f"Call `{tn(TOOL_ANSWER_INSTANTIATE)}` with `instantiations`, a list of "
                "{variable, term} objects; each `term` must be a well-formed Isabelle "
                "type.\n")

    async def answer(self, answer: AnswerInstantiate) -> 'list[tuple[str, str]]':
        insts = _validate_instantiation_answer(answer, self.schematic_vars)
        # Validate against the actual post-rule state via the same 2-phase
        # primitive used on replay (ASCII-encoded, matching the wire form).
        err: str | None = await self.state.connection.callback(
            "IsaMini.validate_inst_var",
            (self.state.name, [(ascii_of_unicode(n), ascii_of_unicode(t)) for n, t in insts]))
        if err is not None:
            raise Interaction_BadAnswer(
                f"Instantiation rejected by Isabelle:\n{pretty_unicode(err)}")
        return insts


class Interaction_MapCase(Interaction):
    """Ask the agent to pick which supplied `case_name`'s body should
    attach to an actual Isabelle case, when the agent's supplied
    `case_name`s did not line up exactly with the cases produced by the
    induction / case-split rule.

    Fires from `CaseSplit_Like._rematch`, which invokes this interaction
    sequentially — one goal at a time — gathering the agent's picks into
    a global mapping.

    Reuses the `indexes` field: at most one index picked from
    `supplied_options`; empty = drop the body (equivalent to saying
    "none of my supplied bodies belong to this actual case").
    Returns the selected supplied name (a string from
    `supplied_options`), or None when the answer is empty."""
    fork_allowed_tools = [TOOL_ANSWER_INDEX]

    def __init__(self,
                 actual_case: str,
                 supplied_options: list[str],
                 kind: Literal["case-split", "induction"],
                 goal: 'Goal | None',
                 ctxt_before: Context):
        self.actual_case = actual_case
        self.supplied_options = supplied_options
        self.kind = kind
        self.goal = goal
        self.ctxt_before = ctxt_before

    async def prompt(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        file.write(
            f"The {self.kind} operation produced a case `{self.actual_case}` "
            f"(as follows) that does not match any `case_name` you supplied.\n")
        if self.goal is None:
            print_indent(indent + 1, file)
            file.write("goal: unknown, evaluation pending\n")
        else:
            print_goal(self.goal, indent + 1, True, file, self.ctxt_before)
        print_indent(indent, file)
        file.write("Is any of your supplied proof intended for this case?\n")
        for i, name in enumerate(self.supplied_options):
            print_indent(indent + 1, file)
            file.write(f"{i}. {name}\n")
        print_indent(indent, file)
        file.write(f"Call `{tn(TOOL_ANSWER_INDEX)}` with the `index` if so, or with null to "
                   "leave this case without a proof for now.\n")

    async def answer(self, answer: AnswerIndex) -> str | None:
        if answer.index is None:
            return None
        _check_index(answer.index, len(self.supplied_options))
        return self.supplied_options[answer.index]


### The Abstract Model

type may_gen_node = Callable[['NodeConfig'], 'Node | None']

type printer = Callable[[int, MyIO], int]

class Warning(NamedTuple):
    class Position(Enum):
        HEADER = 0
        FOOTER = 1
    position: Position
    printer: str | printer

# abstract base class
class NodeConfig(NamedTuple):
    local_step: local_step
    ml_state: Minilang_State
    parent: 'NonLeaf_Node | None'

# `Parsed_Opr`: a parsed proof-op.  Carries:
#   - `cls`: the class that will be constructed (so runtime consumers can
#     ask "is this an Intro?" without peeking at raw dicts);
#   - `factory`: a sync callable that turns a `NodeConfig` into a
#     fully-constructed `Node`;
#   - `raw`: the original raw ToolCall dict (preserved for error reporting
#     — e.g. `unapplied_batch_warning` dumps the unapplied tail's raw dicts
#     so the agent can see what it submitted and re-submit).
# Retrieval and interactions are deferred to the Node's first
# `_refresh_me_alone` call via per-field `X is None` sentinels — no state
# needs to flow in at construction.
class Parsed_Opr(NamedTuple):
    cls: type
    factory: Callable[[NodeConfig], 'Node']
    raw: ToolCall_arg

# `proof` (type alias): the PARSED in-memory form of a proof body — a list of
# already-parsed `Parsed_Opr`s.  Node instance fields that carry a sub-proof
# store this form (never raw dicts), so `Parse_Nodes` is only invoked once
# per op at tool-call time, not on every refresh.
type proof = list[Parsed_Opr]
type proof_with_case_vars = tuple[list[name] | None, proof]


@dataclass
class EditOutcome:
    """Mutable record of the state of an edit operation in progress or
    just completed.  `append` / `insert_before_me` / `amend_me` and the
    top-level `fill` / `insert_before` / `amend` mutate an `EditOutcome`
    in place as they run — never raising `AoA_Error`; only `InternalError`
    (a bug) propagates.

    - `operation`: which user-facing edit was attempted (Fill/Insert/
      Amend).  Always set by the internal primitive from its `op` parameter.
    - `committed`: nodes added to the tree (in order).  On
      `TERMINATE_AND_REVERT` the reverted node is popped so `committed`
      reflects what is actually in the tree.
    - `failure`: a `CannotEdit` subclass when the edit ran into an
      expected failure, or `None` on full success.  Carries
      `operation` / `unapplied_oprs` / `is_error` in its fields.
    - `request`: the original `list[Parsed_Opr]` the caller submitted.
      Hooks (e.g. `Obvious._on_edit_failure`) inspect this to decide
      batch-size-aware policy."""
    operation: 'EditOperation'
    committed: 'list[Node]' = field(default_factory=list)
    failure: 'CannotEdit | None' = None
    request: 'list[Parsed_Opr]' = field(default_factory=list)

    async def commit_and_hook(
        self,
        can_continue: bool,
        node: 'Node',
        auto_intro: bool,
    ) -> 'tuple[EditFailureBehavior, bool]':
        """Post-attach bookkeeping shared by `append` / `insert_before_me`:
        refresh the newly-attached `node`, add it to `committed`, run
        `_on_edit_failure` if the refresh resolved to FAILURE.  On
        `TERMINATE_AND_REVERT`: delete the node from the tree and pop
        it from `committed`.  Returns `(behavior, cancelled)`; `cancelled`
        tells the caller the node was `_cancel`'d (no refresh, but still
        in the tree)."""
        cancelled = False
        if can_continue:
            try:
                # replace-aware: a fresh-fill InferenceRule that fails here may
                # self-convert to a Rewrite (returned rebinds `node`), so the
                # single cascade below, committed entry, and failure handling all
                # see the converted node. ProofTreeTooDeep still propagates.
                node = await _refresh_child_replace_aware(node, auto_intro)
            except ProofTreeTooDeep:
                the_session()._depth_limit_exceeded = True
                node.status = EvaluationStatus.Failure(
                    0.0, FailureReason("Proof tree depth exceeds the limit"))
        else:
            failed_id = node.parent._failed_predecessor_id(node) if node.parent else None
            await node._cancel(failed_id)
            cancelled = True
        if not cancelled:
            await node._refresh_all_after_me()
        self.committed.append(node)
        if cancelled or node.status.status != EvaluationStatus.Status.FAILURE:
            return (EditFailureBehavior.CONTINUE, cancelled)
        behavior, _ = node._on_edit_failure(self)
        if behavior is EditFailureBehavior.TERMINATE_AND_REVERT:
            parent = node.parent
            rp = node._delete_me()
            # The reverted node's refresh may have set _is_trivial on its
            # parent (e.g. a failed Obvious sets _is_trivial=False).  Now
            # that the node is gone, clear the flag so the slot is usable
            # again — otherwise GoalIsNontrivial blocks all future Obvious
            # attempts on that parent.
            if parent is not None:
                parent._is_trivial = None
            await rp._refresh_me_alone(auto_intro=False)
            if rp.parent is not None:
                await rp._refresh_all_after_me()
            self.committed.pop()
        return (behavior, cancelled)


# `_RawOp`: one element of the parsing pipeline's input linked list — a raw
# ToolCall dict (`op`) paired with the path string (`path`) used when
# constructing error messages about that op.  Path is precomputed once at
# `Parse_Op_List` entry (as `f"{container_path}[{i}]"`) so the recursion
# doesn't re-compute it per step.
class _RawOp(NamedTuple):
    op: raw_op
    path: str

# Result of resolving a `step` id that may name either an existing node OR an
# unfilled (open) proof slot — see `Node.locate_node_or_slot`.  The two variants
# use *different* field names on purpose: `Resolved_Slot.parent` cannot be
# misread as "the node I asked for" (it is the slot's owning block, not the slot
# itself, which has no node).
@dataclass
class Resolved_Node:
    """`id` named an existing materialized node."""
    node: 'Node'

@dataclass
class Resolved_Slot:
    """`id` named an unfilled slot: `parent` is its (existing) owning block,
    `slot_id` echoes the slot id (== parent._id_of_openning_prf_to_fill())."""
    parent: 'Node'
    slot_id: step

Resolved_Step = Resolved_Node | Resolved_Slot

class Node(ABC):
    parent: 'NonLeaf_Node | None'
    id: 'step'
    line: int
    _changes_pending_goal = True
    _is_declarative: ClassVar[bool] = False
    _the_single_printed_goal: 'Goal | None' = None
    """Set by quickview when this node prints a single goal (e.g. Rewrite's
    "goal changes into").  Used by the enclosing StdBlock to suppress
    duplicated goal printing at the end of the block."""

    def __init__(self, config: NodeConfig, thought: str):
        """
        ml_state: the state before executing the Node. This field is mutable!!
        """
        self.local_step = config.local_step # immutable
        self.thought = thought
        self.ml_state = config.ml_state # the pointer of self.ml_state is immutable
        self.parent = config.parent
        if self.parent is not None and self.parent.id:
            self.id = f"{self.parent.id}.{self.local_step}"
        else:
            self.id = self.local_step
        self._depth = (self.parent._depth + 1) if self.parent is not None else 0
        self._subgoal_level: int = 0 if self.parent is None else self.parent._subgoal_level
        session = the_session()
        if self._depth > session._depth_limit:
            raise ProofTreeTooDeep(self._depth, session._depth_limit, self.parent)
        self.status : EvaluationStatus = EVALUATION_NOT_YET
        self.warnings : list[Warning] = []
        self.changed : bool = False
        self._kind : str = "step"
        self._first_time = True
        self._cancelled_by: str | None = None
        self._has_considered_auto_intro = False
        self._is_trivial: bool | None = None
        self.age = session.age
        self.line = 0
        self._prev_eval_status: tuple[EvaluationStatus.Status, str | None] | None = None
        # Whether this node's subtree has already been announced as fully proved
        # in a tool response. Set by `Session.newly_completed_topmost` so the same
        # completion is reported only once; reset there when the subtree regresses
        # to unfinished (so a re-completion is announced afresh).
        self._completion_announced: bool = False

    def _on_upstream_change(self) -> None:
        """Called when a predecessor is amended or inserted, meaning
        the proof state flowing into this node may have changed.
        Override to clear caches that depend on upstream state."""
        self._is_trivial = None

    async def _execute_opr(self, from_state: 'Minilang_State',
                           opr: 'Minilang_Operation',
                           dest: 'Minilang_State | None') -> None:
        """Chokepoint for executing this node's own operation, taking an
        explicit `from_state` (the four call sites execute from two different
        receivers). The base is a plain execute; `SubgoalMaker` overrides it to
        detect residual schematic variables after RULE/CaseSplit/Induction and
        prompt the agent to instantiate them before the op is committed."""
        await from_state.execute(opr, dest)

    @classmethod
    def _validate_arg(cls, arg: Any, path: str) -> Any:
        """Validate arg against this class's registered ToolArg TypedDict."""
        meta = next((m for m in OPERATION_REGISTRY.values() if m.cls is cls), None)
        if meta is not None:
            return validate(meta.toolarg_typed_dict, arg, path)
        return arg

    @classmethod
    def gen_single(
        cls,
        arg: Any,
        path: str = "<direct>",
    ) -> Parsed_Opr:
        """Build the self `Parsed_Opr` for this op (one node — no tail).
        Default factory: `lambda cfg: cls(cfg, arg)` — fits every class
        whose `__init__` signature is `(config, arg)` and that has no
        nested proof fields to pre-parse.

        Subclasses override when the `__init__` signature differs (extra
        positional for pre-parsed `proof` / `proofs` / `cases`) or when
        the ToolArg carries nested fields that must be parsed at gen
        time.  Path is only used for error messages when parsing nested
        fields; it has a default for direct/test invocations like
        `Obvious.gen_single({"facts": []})`."""
        arg = cls._validate_arg(arg, path)
        return Parsed_Opr(cls=cls, factory=lambda cfg: cls(cfg, arg), raw=arg)

    @classmethod
    def gen(
        cls,
        arg: Any,
        remaining: 'LinkedList[_RawOp]',
        path: str,
    ) -> 'LinkedList[Parsed_Opr]':
        """Base: `Cons(gen_single(arg, path), Parse_Nodes(remaining))`.

        Most subclasses only override `gen_single` (which builds the
        self gn).  Classes that need access to `remaining` itself
        (Obvious's forbid-successor check; InferenceRule/Intro splice)
        override `gen` directly — non-splice paths can still delegate to
        `super().gen(...)`.
        """
        return Cons(cls.gen_single(arg, path), Parse_Nodes(remaining))

    @property
    def titled_id(self) -> str:
        """Return e.g. 'step 1' or 'goal 2.1' (worker-relative id)."""
        return f"{self._kind} {the_session()._display_id(self.id)}"
    def id_of_goal(self) -> step | None:
        return self.id
    def _reset_local_step(self, new_local_step: str) -> None:
        self.local_step = new_local_step
        self._recompute_id()
    def _recompute_id(self) -> None:
        if self.parent is not None and self.parent.id:
            self.id = f"{self.parent.id}.{self.local_step}"
        else:
            self.id = self.local_step
        for child in getattr(self, "sub_nodes", ()):
            child._recompute_id()
    def _print_step_id(self, indent: int, file: MyIO, update_line: bool = False) -> int:
        if update_line:
            self.line = file.current_line()
        print_indent(indent, file)
        file.write(f"- {self._kind} id: {the_session()._display_id(self.id)}\n")
        return indent + 1
    def print(self, indent: int, file : MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        return self._print_step_id(indent, file, update_line)
    def print_string(self, indent: int, show_warnings: bool = True) -> str:
        buffer = StringIO()
        self.print(indent, MyIO(buffer), show_warnings=show_warnings)
        return buffer.getvalue()
    def quickview_title(self) -> str:
        return type(self).__name__
    _done_label: str = "proven"
    def _should_print_done(self) -> bool:
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return False
        return not self.does_quickview_need_detail()
    def quickview_header(self, indent: int, file: MyIO) -> int:
        print_indent(indent, file)
        changed_mark = "changed, " if self.changed else ""
        done_mark = f"{self._done_label}, " if self._should_print_done() else ""
        match self.status.status:
            case EvaluationStatus.Status.FAILURE:
                status_mark = "failed, "
            case EvaluationStatus.Status.CANCELLED:
                status_mark = "pending, "
            case EvaluationStatus.Status.COMMENTED:
                status_mark = "commented, "
            case _:
                status_mark = ""
        line_mark = f"line {self.line}, " if the_session().quickview_line_numbers else ""
        marks = f"{changed_mark}{status_mark}{done_mark}{line_mark}".rstrip(", ")
        suffix = f" ({marks})" if marks else ""
        file.write(f"{self._kind} {the_session()._display_id(self.id)}: {self.quickview_title()}{suffix}\n")
        return indent + 1
    def does_quickview_need_detail(self) -> bool:
        return self.changed or not _status_can_continue(self.status.status)
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = self.quickview_header(indent, file)
        eval_key = (self.status.status,
                    self.status.reason.reason if self.status.reason else None)
        if eval_key != self._prev_eval_status:
            self._print_evaluation_status(indent, file)
            self._prev_eval_status = eval_key
        if self.does_quickview_need_detail():
            self._print_warnings(indent, file, list(Warning.Position))
        return indent
    def _print_evaluation_status(self, indent: int, file: MyIO) -> None:
        match self.status.status:
            case EvaluationStatus.Status.SUCCESS:
                pass
            case EvaluationStatus.Status.FAILURE:
                print_indent(indent, file)
                file.write("Error:")
                reason = self.status.reason
                assert reason is not None
                print_paragraph(indent, file, the_session()._postprocess_outbound_text(reason.reason))
            case EvaluationStatus.Status.CANCELLED:
                print_indent(indent, file)
                if self._cancelled_by:
                    cb = the_session()._display_id(self._cancelled_by)
                    if not the_session().showed_cancelled_notice:
                        file.write(f"Error: the evaluation is cancelled due to failure of step `{cb}`\n")
                        the_session().showed_cancelled_notice = True
                    else:
                        file.write(f"Error: cancelled (step `{cb}` failed)\n")
                else:
                    file.write("Error: the evaluation is cancelled due to failures in preceding nodes\n")
            case EvaluationStatus.Status.COMMENTED:
                print_indent(indent, file)
                file.write("(commented out)\n")
    def _print_evaluation_status_quickview(self, indent: int, file: MyIO) -> None:
        match self.status.status:
            case EvaluationStatus.Status.SUCCESS:
                pass
            case EvaluationStatus.Status.FAILURE:
                print_indent(indent, file)
                file.write("evaluation failed")
            case EvaluationStatus.Status.CANCELLED:
                print_indent(indent, file)
                file.write("evaluation cancelled")
    def _print_warnings(self, indent: int, file: MyIO, positions: list[Warning.Position], show_at: bool = False) -> None:
        warnings = [warning for warning in self.warnings if warning.position in positions]
        match warnings:
            case []:
                pass
            case _:
                print_indent(indent, file)
                file.write("notice")
                if show_at:
                    file.write(" at ")
                    file.write(the_session()._display_id(self.id))
                file.write(f":\n")
                for warning in warnings:
                    if isinstance(warning.printer, str):
                        # Warning text is built at refresh time (possibly by a
                        # different session than the one rendering now), so any
                        # embedded step id is relativized here at render time.
                        printer = the_session()._postprocess_outbound_text(warning.printer)
                        if '\n' in printer:
                            for i, line in enumerate(printer.splitlines()):
                                if i == 0:
                                    print_indent(indent+1, file)
                                    file.write(f"- ")
                                else:
                                    print_indent(indent+2, file)
                                file.write(f"{line}\n")
                        else:
                            print_indent(indent+1, file)
                            file.write(f"- {printer}\n")
                    else:
                        warning.printer(indent+1, file)
    def _print_all_warnings(self, file: MyIO) -> None:
        self._print_warnings(0, file, list(Warning.Position), show_at=True)
    def _print_thought(self, indent: int, file: MyIO) -> None:
        lines = self.thought.strip().splitlines()
        match lines:
            case []:
                pass
            case [line]:
                print_indent(indent, file)
                file.write(f"thought: {line}\n")
            case _:
                print_indent(indent, file)
                file.write(f"thought: |\n")
                for line in lines:
                    print_indent(indent+1, file)
                    file.write(line)
                    file.write("\n")
    def resulting_state(self) -> Minilang_State:
        """
        The resulting state after executing the node
        """
        if self.parent is None:
            raise InternalError("Don't know how to get the resulting state of a node when its parent is none")
        else:
            return self.parent._resulting_state_of_child(self)

    async def _cancel(self, cancelled_by: str | None = None) -> None:
        if self.status.status in (EvaluationStatus.Status.CANCELLED,
                                  EvaluationStatus.Status.COMMENTED):
            return
        self._cancelled_by = cancelled_by
        self.status = EVALUATION_CACNCELLED
        await self.resulting_state().reset()
    def _on_edit_failure(
        self, outcome: 'EditOutcome'
    ) -> 'tuple[EditFailureBehavior, EditOutcome]':
        """Hook called during `append`/`insert_before_me`/`amend_me` when
        this node has just been committed and its refresh resolved to
        FAILURE status.  `self` is that failing node; at call time
        `outcome.committed[-1] is self` and `outcome.operation` reflects
        the top-level edit action (Fill/Insert/Amend).

        Default behaviour: return `(CONTINUE, outcome)` — the batch
        continues, the failing node stays in the tree, the agent sees
        the FAILURE from tree structure.

        Override contract: return `(behavior, outcome)`.
        - `CONTINUE`: batch moves on; failing node stays in tree.
        - `TERMINATE`: batch stops; failing node stays in tree.
        - `TERMINATE_AND_REVERT`: batch stops; failing node is removed
          from the tree by the caller (but stays in `outcome.committed`).

        Hooks MAY mutate `outcome.failure` (typically to a
        `CannotEdit_EvaluationFailed(reason=..., operation=
        outcome.operation, ...)`).  Hooks inspect `outcome.request`
        for batch-size-aware decisions (typical: only
        TERMINATE_AND_REVERT on singleton)."""
        return (EditFailureBehavior.CONTINUE, outcome)
    @abstractmethod
    def assemble(self, output: list[Minilang_Operation] | None = None) -> list[Minilang_Operation]:
        """
        Assembling all the abstract tree model into the final sequence of Minilang operations
        """
        ...
    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        """
        must update self.status
        Convention: Any node must be up to date after calling any public Node method
        """
        self.age = the_session().age
        self._first_time = False
    def _hint_notice_state(self) -> 'Minilang_State | None':
        """The state whose `.messages` carry Agent Hint Registry NOTICEs emitted
        while this node's own operation parsed its authored terms. For a leaf
        that is its resulting state; `StdBlock` overrides it to the
        after-beginning state (where its beginning op's messages live).
        None when the node authored nothing / has no such state.

        Read at RENDER time by `Session._emit_pending_hint_notices` (NOT at
        refresh time): at render the node's status is already final, so the
        SUCCESS gate is satisfied, and `Minilang_State.messages` survives
        `root.reset()` (which clears only `warnings`)."""
        if self.parent is None or self.status.status != EvaluationStatus.Status.SUCCESS:
            return None
        return self.resulting_state()
    def _synthetic_hint_notices(self) -> 'list[Hint_Notice_Msg]':
        """Agent Hint Registry NOTICEs synthesized by the Python model (not carried
        on an ML `Minilang_State.messages`). Surfaced once per context by
        `Session._emit_pending_hint_notices`, deduped via `Session.shown_hints`
        (cleared on compaction so the notice re-shows). Default: none. Overrides
        must self-gate on their own status (the render-time walk calls this on every
        node, including FAILURE ones)."""
        return []
    async def _auto_intro_after_me(self) -> None:
        if self.parent is not None:
            await self.parent._auto_Intro_after_child(self)
    async def _refresh_all_after_me(self) -> None:
        """
        refreshing the status of all the nodes excluding and after the `self`
        """
        if self.parent is None:
            raise InternalError("Don't know how to refresh a node and all its after nodes when the node's parent is none")
        else:
            await self.parent._refresh_all_children_after(self, _status_can_continue(self.status.status))
    async def insert_before_me(
        self, gns: 'list[Parsed_Opr]',
        op: 'EditOperation' = EditOperation.INSERT,
    ) -> 'EditOutcome':
        """Insert `gns` as siblings immediately before `self`, in order.
        Catches Group-B construction errors (`GoalIsNontrivial`) into
        `EditOutcome.failure` and stops the batch.  After each commit,
        if the inserted node's status is FAILURE, invokes
        `_on_edit_failure`; the returned `EditFailureBehavior` decides
        whether the batch continues, stops, or stops-and-reverts.

        Optimization: per-node refresh skips the cascade
        (`_refresh_all_after_me`); one cascade runs after the batch."""
        outcome = EditOutcome(operation=op, request=gns)
        if self.parent is None:
            raise InternalError("Cannot insert_before_me on a parentless node")
        if not gns:
            return outcome
        parent = self.parent
        result = await parent._insert_before_child(self, gns)
        if result.error is not None and not result.created:
            e = result.error
            e.operation = op
            e.unapplied_oprs = list(gns)
            e.is_error = True
            idx = result.stopped_at
            assert idx is not None  # set together with result.error
            e.failed_opr = gns[idx] if idx < len(gns) else None
            e.failed_index = idx
            outcome.failure = e
            return outcome
        cascade_from: Node | None = None
        for i, node in enumerate(result.created):
            can_continue = parent._can_continue_before_child(node)
            cancelled = False
            if can_continue:
                # replace-aware: a fresh-fill InferenceRule may self-convert to a
                # Rewrite (rebinds `node`); keep result.created in sync.
                node = await _refresh_child_replace_aware(node, True)
                result.created[i] = node
            else:
                await node._cancel(parent._failed_predecessor_id(node))
                cancelled = True
            outcome.committed.append(node)
            if cancelled or node.status.status != EvaluationStatus.Status.FAILURE:
                if not cancelled:
                    cascade_from = node
                continue
            behavior, _ = node._on_edit_failure(outcome)
            if behavior is EditFailureBehavior.TERMINATE_AND_REVERT:
                for j in range(len(result.created) - 1, i, -1):
                    parent._remove_child(result.created[j])
                rp = node._delete_me()
                await rp._refresh_me_alone(auto_intro=False)
                if rp.parent is not None:
                    await rp._refresh_all_after_me()
                outcome.committed.pop()
                cascade_from = None
                break
            elif behavior is EditFailureBehavior.TERMINATE:
                for j in range(len(result.created) - 1, i, -1):
                    parent._remove_child(result.created[j])
                await node._refresh_all_after_me()
                cascade_from = None
                break
            else:
                cascade_from = node
        if cascade_from is not None:
            await cascade_from._refresh_all_after_me()
        if result.error is not None:
            e = result.error
            e.operation = op
            idx = result.stopped_at
            assert idx is not None  # set together with result.error
            e.unapplied_oprs = list(gns[idx:])
            e.is_error = len(outcome.committed) == 0
            e.failed_opr = gns[idx] if idx < len(gns) else None
            e.failed_index = idx
            outcome.failure = e
        return outcome
    async def insert_before(
        self, step: step, gns: 'list[Parsed_Opr]',
    ) -> 'EditOutcome':
        """Insert `gns` as siblings before `step`, in order.  Returns an
        `EditOutcome` — never raises AoA_Error.

        When `step` names a filling slot rather than an existing node,
        falls through to `fill` — the agent's intent ("add before the
        next position") is equivalent to filling that slot."""
        op = EditOperation.INSERT
        outcome = EditOutcome(operation=op, request=gns)
        if not gns:
            return outcome
        try:
            node = self.locate_node(step)
        except NodeNotFound:
            ids = step.split('.')
            try:
                parent = self._locate_node(ids[:-1], step, 0)
            except NodeNotFound:
                outcome.failure = CannotEdit_NodeNotFound(
                    target_step=step, operation=op, unapplied_oprs=list(gns), is_error=True)
                return outcome
            if parent._id_of_openning_prf_to_fill() == step:
                return await self.fill(step, gns)
            outcome.failure = CannotEdit_NodeNotFound(
                target_step=step, operation=op, unapplied_oprs=list(gns), is_error=True)
            return outcome
        # A SubgoalMaker's children are STRUCTURAL goals (the exhaustiveness
        # obligation + case GoalNodes), created internally — not editable steps.
        # Inserting a user op before one is meaningless and used to mint a corrupt
        # id (the front-insert arithmetic underflows on the obligation's [0]
        # local_step, e.g. `1.0` -> `1.-1A`). Reject cleanly via the no-raise
        # outcome.failure channel. Both the insert path (here) and the amend path
        # (`Node.amend`) are gated against a SubgoalMaker's structural children.
        if isinstance(node.parent, SubgoalMaker):
            outcome.failure = CannotEdit_SubgoalSibling(
                target_step=step, operation=op,
                unapplied_oprs=list(gns), is_error=True)
            return outcome
        if node.parent is not None and isinstance(node.parent, NonLeaf_Node):
            the_session().working_block = node.parent
        return await node.insert_before_me(gns, op=op)
    @abstractmethod
    async def append(
        self, gns: 'list[Parsed_Opr]',
        op: 'EditOperation' = EditOperation.FILL,
    ) -> 'EditOutcome':
        ...
    def _locate_node(self, ids: Sequence[local_step], id: step, pos: int = 0) -> 'Node':
        if pos == len(ids):
            return self
        raise NodeNotFound(id)
    def locate_node(self, id: step) -> 'Node':
        parts = id.split('.')
        return self._locate_node(parts, id)
    def locate_node_or_slot(self, id: step) -> 'Resolved_Step':
        """Resolve `id` to either an existing node or an unfilled proof slot,
        unifying the address space `subagent` accepts with the one `fill`
        accepts.  A slot `P.k` is resolved exactly as `Node.fill` does — locate
        the parent block and ask it for its open slot id
        (`_id_of_openning_prf_to_fill`).  A genuinely nonexistent id still
        raises `NodeNotFound`."""
        try:
            return Resolved_Node(self.locate_node(id))
        except NodeNotFound:
            pass
        ids = id.split('.')
        parent = self._locate_node(ids[:-1], id, 0)  # bad parent path → NodeNotFound
        if parent._id_of_openning_prf_to_fill() == id:
            return Resolved_Slot(parent, id)
        raise NodeNotFound(id)
    def _closes_my_parent(self) -> bool:
        # Whether, as the live tail child of my parent, I close my parent's
        # proof line (so the parent itself is not flagged; its obligation is
        # carried by my subgoal children). Default: a node does not close its
        # parent. SubgoalMaker overrides this. Read by NonLeaf_Node.opening().
        return False
    def unfinished_nodes(self, ret: set['Node']) -> None:
        if not _status_can_continue(self.status.status):
            ret.add(self)
    def subtree_stats(self) -> 'tuple[int, int]':
        """Size of this subtree as ``(total, proved)``. ``total`` counts every
        node including self. ``proved`` counts nodes covered by completed
        proof work: the whole subtree of a maximal ``is_proof_finished()``
        block (``StdBlock`` override), plus SUCCESS ``Obvious`` leaves (goals
        closed by the hammer; ``Obvious`` override) outside such blocks.
        Cheap structural successes (``Intro``, ``SplitConjs``, …) do not
        count on their own. A COMMENTED node and its entire subtree count as
        ``(0, 0)`` — comments are not code. Subclasses override
        ``_subtree_stats_live``, not this method."""
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return (0, 0)
        return self._subtree_stats_live()
    def _subtree_stats_live(self) -> 'tuple[int, int]':
        """`subtree_stats` of a non-COMMENTED node. Base case covers plain
        leaves; ``NonLeaf_Node`` overrides to recurse."""
        return (1, 0)
    async def aclose_all_subagents(self) -> None:
        """Recursively close every sub-agent in this node's subtree (cancel +
        detach, keeping each partial proof). The nodes THEMSELVES STAY in the tree —
        use when a node is KEPT but its sub-agents must be released: ``cancel_subagent``
        (the target stays; its worker and nested downstream go), a worker winding
        down its own leftover parked sub-agents, the session-close sweep.

        Deliberately a SEPARATE recursion from ``discard`` (which disposes a node
        that is LEAVING the tree): the two have the same effect today but mean
        different things and are kept independent so each can evolve on its own.
        Base case (``Leaf``): none; ``NonLeaf_Node`` overrides to recurse."""
        return None
    async def discard(self) -> None:
        """Dispose of this node as it LEAVES the tree — ``delete`` (the whole subtree
        is removed) or ``amend`` (the node is replaced; its descendants are
        re-parented onto the replacement, so only this node itself truly departs).
        Recursively closes every sub-agent in the subtree — that proof is being
        deleted or redone, so its workers are released — and is the hook for any
        other per-node resource a departing node may hold.

        Deliberately a SEPARATE recursion from ``aclose_all_subagents`` (which KEEPS
        the nodes and only frees their sub-agents): same effect today, different
        meaning, kept independent. Base case (``Leaf``): nothing to release;
        ``NonLeaf_Node`` overrides to recurse."""
        return None
    def _nearest_goal_for_subagent(self) -> 'Node | None':
        """The node a ``subagent`` call on `self` should actually target — the
        nearest delegatable goal. Default: `self` is not a goal → redirect to the
        parent; ``None`` at the top. Goal blocks (Have/Obtain/Suffices/GoalNode)
        and SetupRewriting override to return `self`; non-delegatable containers
        (GoalContainer/Root, GlobalEnv) override to return ``None`` directly (neither
        a target nor transparent — pointing at them is an error)."""
        return self.parent._nearest_goal_for_subagent() if self.parent is not None else None
    def can_add_constraints(self) -> bool:
        """Whether a missing CONSTRAINT (a condition the sub-goal needs but was
        not given) can be ADDED to this node in place — i.e. appended as a premise
        of the named fact this node poses. Default ``False``; ``Have`` and
        ``SetupRewriting`` override to ``True``. A non-amendable target
        (Obtain/Suffices) means the missing constraint is a structural problem the
        dispatcher must fix by reworking the proof (see ``add_constraints``)."""
        return False
    async def add_constraints(self, constraints: 'list[PremiseBinding]') -> 'str | None':
        """Append ``constraints`` (``{name, term}`` premises) to this node IN
        PLACE — the named fact becomes conditional on them — re-refresh this node
        and the downstream cascade, and return ``None`` on success or a rejection
        message string on failure (the mutation is reverted). Only nodes whose
        ``can_add_constraints()`` is True implement this; the default raises."""
        raise NotImplementedError(
            f"{type(self).__name__} cannot add constraints (can_add_constraints is False)")
    async def fill(self, id: step, gns: 'list[Parsed_Opr]') -> 'EditOutcome':
        """Fill a blank proof slot (or replace an existing failed step
        via the fallback path) with one or more newly-constructed
        nodes, delegating to the target's `append(gns)` once the slot
        is cleared.  Returns an `EditOutcome` — never raises AoA_Error."""
        op = EditOperation.FILL
        outcome = EditOutcome(operation=op, request=gns)
        if not gns:
            return outcome
        ids = id.split('.')
        try:
            node = self._locate_node(ids[:-1], id, 0)
        except NodeNotFound:
            outcome.failure = CannotEdit_NodeNotFound(
                target_step=id, operation=op, unapplied_oprs=list(gns), is_error=True)
            return outcome
        session = the_session()
        if isinstance(node, NonLeaf_Node):
            session.working_block = node
        to_fill = node._id_of_openning_prf_to_fill()
        if to_fill is None:
            outcome.failure = CannotEdit_NodeNotFound(
                target_step=id, operation=op, unapplied_oprs=list(gns), is_error=True)
            return outcome
        if to_fill != id:
            # Fallback: allow replacing a node (and all its successors)
            # when every node from the target onward has failed or been
            # cancelled.  Handles orphaned nodes left behind by exceptions
            # during append (e.g. InternalError in Intro) that would
            # otherwise make the step permanently unfillable.
            assert isinstance(node, NonLeaf_Node), (
                "fill's target must be a NonLeaf_Node — Leaf nodes have no "
                "children to fill into")
            found_i = None
            for i, child in enumerate(node.sub_nodes):
                if child.id == id:
                    found_i = i
                    break
            if found_i is None or any(
                _status_can_continue(c.status.status)
                for c in node.sub_nodes[found_i:]
            ):
                outcome.failure = CannotEdit_BadNode(
                    target_step=id, operation=op, unapplied_oprs=list(gns), is_error=True)
                return outcome
        # Replacement semantics: delete the target node (if it exists)
        # and everything after it via the standard deletion path, then
        # refresh the predecessor so the state chain is correct before
        # append.
        assert isinstance(node, NonLeaf_Node), (
            "fill's target must be a NonLeaf_Node — Leaf nodes have no "
            "children to fill into")
        rp: 'Node | None' = None
        for i, child in enumerate(node.sub_nodes):
            if child.id == id:
                # The target and every successor sibling leave the tree here
                # (the gate above guarantees none is SUCCESS). Close their
                # sub-agents before unlinking, or a worker parked on one of
                # these failed goals orphans — under nesting no live dispatcher
                # could ever resume or close it.
                for d in node.sub_nodes[i:]:
                    await d.discard()
                rp = child._delete_me()
                while i < len(node.sub_nodes):
                    node._delete_child(node.sub_nodes[i])
                node._is_trivial = None
                break
        if rp is not None and _status_can_continue(rp.status.status):
            await rp._refresh_me_alone(auto_intro=False)
            if rp.parent is not None:
                await rp._refresh_all_after_me()
        outcome = await node.append(gns, op=op)
        if (outcome.failure is not None
                and isinstance(outcome.failure, GoalIsNontrivial)
                and outcome.failure.target_step != id):
            outcome.failure.target_step = id
        return outcome
    def _id_of_openning_prf_to_fill(self) -> step | None:
        return None

    def _fixed_vars_after_me(self, ret: Vars) -> Vars:
        return ret
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        return ret
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return ret
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        return ret
    def _fixed_tvars_after_me(self, ret: TVars) -> TVars:
        return ret
    def _fixed_tvars_at_me(self, ret: TVars) -> TVars:
        return ret
    def _all_fixed_vars_before_me(self, ret: Vars) -> Vars:
        if self.parent is not None:
            self.parent._all_fixed_vars_before_a_child(self, ret)
        return ret
    def _all_fixed_facts_before_me(self, ret: Hyps) -> Hyps:
        if self.parent is not None:
            self.parent._all_fixed_facts_before_a_child(self, ret)
        return ret
    def _all_fixed_tvars_before_me(self, ret: TVars) -> TVars:
        if self.parent is not None:
            self.parent._all_fixed_tvars_before_a_child(self, ret)
        return ret
    def _ctxt_before_me(self) -> Context:
        vars = self._all_fixed_vars_before_me({})
        hyps = self._all_fixed_facts_before_me({})
        tvars = self._all_fixed_tvars_before_me({})
        return Context(vars, tvars, hyps)
    def _ctxt_at_me(self) -> Context:
        vars = self._all_fixed_vars_before_me({})
        self._fixed_vars_at_me(vars)
        tvars = self._all_fixed_tvars_before_me({})
        self._fixed_tvars_at_me(tvars)
        hyps = self._all_fixed_facts_before_me({})
        self._fixed_facts_at_me(hyps)
        return Context(vars, tvars, hyps)
    def _collect_discarded_vars(self, ret: 'dict[str, tuple[str, str]]') -> 'dict[str, tuple[str, str]]':
        """Collect, over this node's whole subtree, a mapping
        internal-skolem-name -> (external-name, discarding-step-id) for every
        variable an Induction generalized away (stored on each Induction node as
        `_discarded_vars`). Consulted by `Session._postprocess_outbound_text` to
        resolve `the out-of-scope variable <internal>` in error messages."""
        dv: 'dict[str, str] | None' = getattr(self, '_discarded_vars', None)
        if dv:
            for internal, external in dv.items():
                ret[internal] = (external, self.id)
        for c in getattr(self, 'sub_nodes', ()):
            c._collect_discarded_vars(ret)
        return ret
    def _rename_var(self, old_name: varname, new_name: varname) -> 'Node | None':
        """
        Return the modified node if the variable is found and renamed, None otherwise.
        """
        return None
    def _rename_fact(self, old_name: str, new_name: str) -> 'Node | None':
        """
        Return the modified node if the fact is found and renamed, None otherwise.
        """
        return None
    async def rename_var(self, old_name: varname, new_name: varname) -> None:
        ret = self._rename_var(old_name, new_name)
        if ret is None:
            raise CannotRename_VariableNotFound(old_name, new_name)
        else:
            await ret._refresh_me_alone(auto_intro=False)
            await ret._refresh_all_after_me()
    async def rename_fact(self, old_name: str, new_name: str) -> None:
        ret = self._rename_fact(old_name, new_name)
        if ret is None:
            raise CannotRename_FactNotFound(old_name, new_name)
        else:
            await ret._refresh_me_alone(auto_intro=False)
            await ret._refresh_all_after_me()
    def _print_fixed_vars_and_facts(self, indent: int, file: MyIO) -> None:
        fixed_vars = self._fixed_vars_at_me({})
        fixed_facts = self._fixed_facts_at_me({})
        if fixed_vars:
            print_indent(indent, file)
            file.write(f"variables:\n")
            for name, typ in fixed_vars.items():
                print_indent(indent+1, file)
                file.write(f"- {name.unicode}: {typ.unicode}\n")
        if fixed_facts:
            print_indent(indent, file)
            file.write(f"facts:\n")
            for name, trm in fixed_facts.items():
                print_indent(indent+1, file)
                file.write(f"- {name.unicode}: {trm.unicode}\n")
    def _warn_discarded_nodes(self, discarded_nodes: list['Node'], position: Warning.Position) -> None:
        ids = [node.titled_id for node in discarded_nodes]
        n = len(discarded_nodes)
        noun = "proof step" if n == 1 else "proof steps"
        verb = "has" if n == 1 else "have"
        msg = (f"Due to changes in the proof structure, "
               f"previous {noun} {string_of_and_list(ids)} {verb} been discarded")
        def printer(indent: int, file: MyIO) -> int:
            print_indent(indent, file)
            file.write('- ')
            file.write(msg)
            file.write('\n')
            return indent
        self.warnings.append(Warning(position, printer))
    def _on_reset(self) -> None:
        # End-of-response render cleanup: clear both the per-render `changed`
        # highlight and the node's deferred render warnings. For most nodes
        # warning visibility is co-gated with `changed` via
        # `does_quickview_need_detail` (`changed or status != SUCCESS`); note
        # `Rewrite` overrides that predicate to also surface warnings on a fresh
        # SUCCESS node, but the "show once, then clear" lifecycle still holds —
        # `Rewrite._refresh_me_alone` re-derives its HEADER warnings each refresh
        # and this reset clears them at end-of-response.
        self.warnings.clear()
        self.changed = False
    def reset(self) -> None:
        self._on_reset()
    def _delete_me(self) -> 'Node':
        """Delete this node and return the refresh point (predecessor sibling or parent)."""
        if self.parent is None:
            raise CannotDelete_Root()
        parent = self.parent
        idx = next(i for i, c in enumerate(parent.sub_nodes) if c is self)
        refresh_point = parent.sub_nodes[idx - 1] if idx > 0 else parent
        parent._delete_child(self)
        return refresh_point
    async def delete(self, ids: list[step]) -> list[step]:
        """Delete nodes by IDs. Returns list of unfound IDs (warnings)."""
        the_session().age += 1
        # Locate all, deduplicate
        nodes: list['Node'] = []
        seen: set[str] = set()
        not_found: list[step] = []
        for id in ids:
            try:
                node = self.locate_node(id)
            except NodeNotFound:
                not_found.append(id)
                continue
            if node.id not in seen:
                seen.add(node.id)
                nodes.append(node)
        if nodes and nodes[0].parent is not None and isinstance(nodes[0].parent, NonLeaf_Node):
            the_session().working_block = nodes[0].parent
        # Tear down any worker sub-agents within the subtrees being removed (the
        # deleted node + its descendants) before unlinking — never ancestors, so
        # deleting a strict descendant of a parked node leaves that worker parked.
        for node in nodes:
            await node.discard()
        # Delete all, collect refresh points
        deleted_ids = seen
        refresh_points: list['Node'] = []
        for node in nodes:
            rp = node._delete_me()
            refresh_points.append(rp)
        # Filter out refresh points that were themselves deleted
        refresh_points = [rp for rp in refresh_points if rp.id not in deleted_ids]
        # Sort by line for efficient ordering (harmless if line uninitialized)
        refresh_points.sort(key=lambda n: n.line)
        # Refresh each point, skip if already refreshed this session age
        for rp in refresh_points:
            if rp.age < the_session().age:
                if not _status_can_continue(rp.status.status):
                    continue
                await rp._refresh_me_alone(auto_intro=False)
                if rp.parent is not None:
                    await rp._refresh_all_after_me()
        return not_found
    async def amend_me(
        self, gns: 'list[Parsed_Opr]',
        op: 'EditOperation' = EditOperation.AMEND,
    ) -> 'tuple[EditOutcome, Node]':
        """Replace `self` with nodes built from `gns`.

        For `len(gns) == 1`: in-place replacement via `_amend_child`'s
        `_amend_from` path — the new node inherits `self`'s sub_nodes.
        If the replacement resolves to FAILURE, the hook
        `_on_edit_failure` may return `TERMINATE_AND_REVERT`, in which
        case `self` is restored in place (including its sub_nodes).

        For `len(gns) != 1`: delete `self`, then insert `gns` at its
        former slot.  `self`'s sub_nodes are dropped.

        Returns `(outcome, original_self)`.  Never raises AoA_Error."""
        outcome = EditOutcome(operation=op, request=gns)
        if self.parent is None:
            outcome.failure = CannotEdit_Root(
                target_step=self.id,
                operation=op, unapplied_oprs=list(gns), is_error=True)
            return outcome, self
        if not gns:
            return outcome, self
        if len(gns) == 1:
            try:
                new_node, old, saved = await self.parent._amend_child(self, gns[0])
            except (GoalIsNontrivial, ProofTreeTooDeep, CannotEdit_NonDeclarative) as e:
                if isinstance(e, ProofTreeTooDeep):
                    the_session()._depth_limit_exceeded = True
                e.operation = op
                e.unapplied_oprs = list(gns)
                e.is_error = True
                outcome.failure = e
                return outcome, self
            # (auto-convert of a fresh-fill InferenceRule amended in here is
            # handled inside `_amend_child` via `_refresh_child_replace_aware`, so
            # `new_node` is already the converted Rewrite if it applied.)
            outcome.committed.append(new_node)
            if new_node.status.status == EvaluationStatus.Status.FAILURE:
                behavior, outcome = new_node._on_edit_failure(outcome)
                if behavior is EditFailureBehavior.TERMINATE_AND_REVERT:
                    parent = new_node.parent
                    if parent is None:
                        raise InternalError("Cannot revert amend on root node")
                    for i, c in enumerate(parent.sub_nodes):
                        if c is new_node:
                            if (isinstance(new_node, NonLeaf_Node)
                                    and isinstance(old, NonLeaf_Node)):
                                old.sub_nodes[:] = new_node.sub_nodes
                                new_node.sub_nodes.clear()
                                for child in old.sub_nodes:
                                    child.parent = old
                            parent.sub_nodes[i] = old
                            old.parent = parent
                            if parent._can_continue_before_child(old):
                                await old._refresh_me_alone(auto_intro=False)
                            else:
                                await old._cancel(parent._failed_predecessor_id(old))
                            await old._refresh_all_after_me()
                            break
                    outcome.committed.pop()
                    # Revert restores `old` (which kept its handle) into the tree
                    # at `parent.sub_nodes[i] = old` above, before its refresh — so
                    # the worker rides along on an in-tree node; no worker code here.
                    return outcome, old
            # COMMIT (SUCCESS or FAILURE-non-revert): decide the worker's fate.
            # Reached for both because only TERMINATE_AND_REVERT returns early above.
            if saved is not None:
                if (isinstance(new_node, StdBlock)
                        and _amend_preserves_worker(old, new_node)
                        and not new_node.is_proof_finished()):
                    saved.retarget(new_node)
                else:
                    # Cancel the parked worker, then sweep any nested sub-agent now
                    # hosted under new_node (a base-NonLeaf `_amend_from` moved
                    # child's sub_nodes — and any nested worker — onto new_node; the
                    # cancelled worker's own wind-down iterates the now-empty
                    # child.sub_nodes and would miss it).
                    await saved.aclose()
                    await new_node.aclose_all_subagents()
            return outcome, old
        # Multi-amend: delete self + insert gns at former slot.
        parent = self.parent
        idx_in_parent = next(
            (k for k, c in enumerate(parent.sub_nodes) if c is self), -1)
        if idx_in_parent < 0:
            raise InternalError("amend_me: self is not a child of its parent")
        next_sibling = (parent.sub_nodes[idx_in_parent + 1]
                        if idx_in_parent + 1 < len(parent.sub_nodes)
                        else None)
        old_self = self
        # `old_self` and its whole subtree leave the tree (its sub_nodes are
        # dropped, not re-parented). Close every sub-agent below it before
        # unlinking, or they orphan.
        await old_self.discard()
        rp = old_self._delete_me()
        if rp is not None and _status_can_continue(rp.status.status):
            await rp._refresh_me_alone(auto_intro=False)
            if rp.parent is not None:
                await rp._refresh_all_after_me()
        if next_sibling is not None:
            sub_outcome = await next_sibling.insert_before_me(gns, op=op)
        else:
            assert isinstance(parent, StdBlock), (
                "amend of last child requires StdBlock parent (for append)")
            sub_outcome = await parent.append(gns, op=op)
        return sub_outcome, old_self
    async def _amend_from(self, old: 'Node') -> None:
        self._first_time = False
    async def amend(self, id: step, gns: 'list[Parsed_Opr]') -> 'EditOutcome':
        """Replace the node at `id` with nodes built from `gns`.  Returns
        an `EditOutcome` — never raises AoA_Error.

        When the target node is not found, falls back to `fill` if `id`
        matches the fill-position of its parent block (handles the common
        case where a prior fill+revert deleted the node)."""
        op = EditOperation.AMEND
        outcome = EditOutcome(operation=op, request=gns)
        if not gns:
            return outcome
        try:
            old_node = self.locate_node(id)
        except NodeNotFound:
            fill_outcome = await self.fill(id, gns)
            if fill_outcome.failure is None:
                return fill_outcome
            # `fill` was a genuine attempt on a valid slot but the
            # operation itself was rejected (e.g. `Obvious` on a
            # non-trivial goal, or evaluation failed).  Surface that
            # actionable reason rather than masking it as "node not
            # found".  Only when `fill` *also* couldn't locate/claim a
            # fillable slot (NodeNotFound / BadNode) do we report the
            # amend-flavoured "node is not found".
            if not isinstance(
                fill_outcome.failure,
                (CannotEdit_NodeNotFound, CannotEdit_BadNode),
            ):
                return fill_outcome
            outcome.failure = CannotEdit_NodeNotFound(
                target_step=id, operation=op,
                unapplied_oprs=list(gns), is_error=True)
            return outcome
        # A SubgoalMaker's direct children are STRUCTURAL goals (the exhaustiveness
        # obligation + case GoalNodes), created internally — not editable steps.
        # Amending one would silently replace the GoalNode with an arbitrary op-node
        # (single op, model.py `_amend_child`) or destructively delete it then
        # re-insert among the structural children (multi op) — both corrupt the
        # tree. Reject cleanly via outcome.failure; NEVER raise here (a CannotEdit
        # raised through `_amend_child` would escape `amend_me`'s catch tuple and
        # `sys.exit(1)` the host). Parallel to the gate in `Node.insert_before`.
        if isinstance(old_node.parent, SubgoalMaker):
            outcome.failure = CannotEdit_SubgoalSibling(
                target_step=id, operation=op,
                unapplied_oprs=list(gns), is_error=True)
            return outcome
        if old_node.parent is not None and isinstance(old_node.parent, NonLeaf_Node):
            the_session().working_block = old_node.parent
        sub_outcome, _ = await old_node.amend_me(gns, op=op)
        return sub_outcome

_OF_PREMISE_MISMATCH_RE = re.compile(
    r'OF: the fact has (\d+) premise\(s\), but (\d+) discharge argument\(s\) were given')

class Leaf(Node):
    def _should_print_done(self) -> bool:
        return False
    def __init__(self, config: NodeConfig, thought: str):
        super().__init__(config, thought)
    @abstractmethod
    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        ...
    def assemble(self, output: list[Minilang_Operation] | None = None) -> list[Minilang_Operation]:
        if output is None:
            output = []
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return output
        op = self.the_operation()
        if isinstance(op, FailureReason):
            raise InternalError(f"Cannot assemble a node with failed operation: {op.reason}")
        output.append(op)
        return output
    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            await self.ml_state.clone(self.resulting_state())
            self.age = the_session().age
            return
        now = time()
        await super()._refresh_me_alone(auto_intro)
        op = self.the_operation()
        if isinstance(op, FailureReason):
            self.status = EvaluationStatus.Failure(time() - now, op)
            return
        try:
            await self._execute_opr(self.ml_state, op, self.resulting_state())
            self.status = EvaluationStatus.Success(time() - now)
        except IsabelleError as err:
            msg = ''.join(err.errors)
            m = _OF_PREMISE_MISMATCH_RE.search(msg)
            if m:
                n_prems = int(m.group(1))
                msg += (f"\nEach `discharge` entry corresponds to one premise of the fact (left-to-right). "
                        f"`discharge` must have at most {n_prems} entries.")
            self.status = EvaluationStatus.Failure(time() - now, FailureReason(msg))
            return
        if auto_intro and not self._has_considered_auto_intro:
            self._has_considered_auto_intro = True
            await self._auto_intro_after_me()

    async def append(
        self, gns: 'list[Parsed_Opr]',
        op: 'EditOperation' = EditOperation.FILL,
    ) -> 'EditOutcome':
        # Unreachable in practice: callers of `append` (fill, amend_me,
        # tests) all target NonLeaf_Node instances.  Treat as a bug.
        raise InternalError(
            f"append called on Leaf node {self.id}; "
            f"expected a NonLeaf_Node target")

def _quickview_children_compressed(children: 'Sequence[Node]', indent: int, file: MyIO) -> None:
    i = 0
    while i < len(children):
        child = children[i]
        if not child.changed and not child.does_quickview_need_detail():
            run_start = i
            i += 1
            while i < len(children) and not children[i].changed and not children[i].does_quickview_need_detail():
                i += 1
            run_len = i - run_start
            if run_len >= 5:
                children[run_start].quickview(indent, file)
                print_indent(indent, file)
                file.write("... all ok\n")
                children[i - 2].quickview(indent, file)
                children[i - 1].quickview(indent, file)
            else:
                for j in range(run_start, i):
                    children[j].quickview(indent, file)
        else:
            child.quickview(indent, file)
            i += 1

class NodeReplaced(Exception):
    """Raised by a node that replaced itself in its parent's sub_nodes during its
    own refresh (a failed fresh-fill InferenceRule that auto-converts to a Rewrite).
    Only ever raised when the parent's `_child_replace_enabled` is set — which is
    set exclusively by `_refresh_child_replace_aware`, the same frame that catches
    it — so it never leaks to an unprepared caller. The catcher continues with
    `new_node`."""
    def __init__(self, new_node: 'Node'):
        self.new_node = new_node

async def _refresh_child_replace_aware(child: 'Node', auto_intro: bool) -> 'Node':
    """Refresh `child`, allowing it to self-replace via `NodeReplaced`, and return
    the (possibly replaced) child. Sets `_child_replace_enabled` on `child.parent`
    — exactly the object an InferenceRule child reads in its guard — for the
    duration of this one call (save/restore), so a raise is only produced where it
    is caught right here. Drivers that want auto-convert support call this instead
    of `child._refresh_me_alone(...)`. `NodeReplaced` is the only exception caught;
    others (e.g. ProofTreeTooDeep) propagate unchanged."""
    container = child.parent
    if not isinstance(container, NonLeaf_Node):
        await child._refresh_me_alone(auto_intro)
        return child
    prev = container._child_replace_enabled
    container._child_replace_enabled = True
    try:
        await child._refresh_me_alone(auto_intro)
        return child
    except NodeReplaced as e:
        return e.new_node
    finally:
        container._child_replace_enabled = prev

def _amend_preserves_worker(old: 'Node', final: 'Node') -> bool:
    """The keep-worker condition for a non-destructive single-op ``amend`` (used by
    ``Node.amend_me``): the top-level node class is unchanged, it is NOT a
    SubgoalMaker (those re-parse their bodies — the live carried nodes don't
    survive), and the new block cleanly re-opened against Isabelle. The status gate
    is ``== SUCCESS`` deliberately — ``!= FAILURE`` would also admit CANCELLED (e.g.
    a broken predecessor sibling makes ``_amend_child`` ``_cancel`` the new node and
    reset its goal state) and COMMENTED, neither of which is a live, re-opened
    target."""
    return (type(final) is type(old)
            and not isinstance(old, SubgoalMaker)
            and final.status.status == EvaluationStatus.Status.SUCCESS)

class NonLeaf_Node(Node):
    sub_nodes: list['Node']
    # A live sub-agent (running or parked) proving this node's subtree, or None.
    worker_handle: 'WorkerHandle | None'

    class _InsertBatchResult(NamedTuple):
        created: 'list[Node]'
        stopped_at: 'int | None'
        error: 'GoalIsNontrivial | ProofTreeTooDeep | None'

    def _validate_child_class(self, cls: 'type[Node]') -> 'CannotEdit | None':
        return None

    def __init__(self, config: NodeConfig, thought: str, sub_nodes: list['Node']):
        super().__init__(config, thought)
        self.sub_nodes = sub_nodes
        self.worker_handle = None
        # True while a child of this node is refreshed inside a context that
        # catches NodeReplaced (set by `_refresh_child_replace_aware`); an
        # InferenceRule child checks this before self-replacing.
        self._child_replace_enabled = False
    def _on_upstream_change(self) -> None:
        super()._on_upstream_change()
        for child in self.sub_nodes:
            child._on_upstream_change()

    def opening(self) -> bool:
        # Derived (not stored): a block is closed iff its live tail child is a
        # SubgoalMaker that opened a parent-closing block and still holds all the
        # cases it opened (see `_closes_my_parent`). Deriving this on every read
        # — rather than mutating a stored `_closed_by` flag in comment /
        # uncomment / delete / refresh — is what keeps open/closed consistent
        # across every edit. SubgoalMaker and Root override to a constant.
        tail = self.sub_nodes[-1] if self.sub_nodes else None
        return not (tail is not None and tail._closes_my_parent())
    async def _truncate_siblings_after(self, child: Node) -> None:
        # Drop the siblings AFTER `child` once `child` opened a subgoal block;
        # they are meaningless. Does NOT mark the parent closed — `opening()`
        # derives that from `child` being the live tail (see `opening`).
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                discarded_nodes = self.sub_nodes[i+1:]
                del self.sub_nodes[i+1:]
                if discarded_nodes:
                    self._warn_discarded_nodes(
                        discarded_nodes,
                        Warning.Position.FOOTER)
                # The truncated siblings leave the tree; close their sub-agents.
                for d in discarded_nodes:
                    await d.aclose_all_subagents()
                return
        raise InternalError("The target node is not my children")
    async def _refresh_footer(self) -> FailureReason | None:
        return None
    def _can_continue_before_child(self, child: 'Node') -> bool:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i == 0:
                    # The firstborn's "predecessor" is the parent block itself:
                    # it can be executed iff the block's own beginning op
                    # succeeded (status can continue). A cancelled/failed block
                    # has no post-beginning state to chain from, so its first
                    # child must be cancelled, not executed — else it would run a
                    # Minilang op from a non-existent ML state
                    # (`beginning_state_not_found` -> InternalError).
                    return _status_can_continue(self.status.status)
                return _status_can_continue(self.sub_nodes[i-1].status.status)
        raise InternalError("The target node is not my children")
    def _failed_predecessor_id(self, child: 'Node') -> str | None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i > 0 and not _status_can_continue(self.sub_nodes[i-1].status.status):
                    pred = self.sub_nodes[i-1]
                    if (pred.status.status == EvaluationStatus.Status.CANCELLED
                            and pred._cancelled_by is not None):
                        return pred._cancelled_by
                    return pred.id
                return None
        return None
    async def _refresh_all_children_after(self, after: 'Node | Literal["end"]', can_continue_i: bool) -> None:
        """
        refreshing the status of all the nodes excluding and after the `after`
        """
        can_continue : bool | None = None
        failed_id: str | None = None
        if after == "end":
            can_continue = True
        else:
            for child in self.sub_nodes:
                if can_continue is None:
                    if child is after:
                        can_continue = can_continue_i
                        if not can_continue_i:
                            failed_id = child.id
                else:
                    if can_continue:
                        # replace-aware: a first-failing fresh-fill InferenceRule
                        # (e.g. previously CANCELLED, now executing for the first
                        # time on this cascade) may self-convert to a Rewrite.
                        child = await _refresh_child_replace_aware(child, True)
                        if not _status_can_continue(child.status.status):
                            can_continue = False
                            failed_id = child.id
                    else:
                        await child._cancel(failed_id)
        if can_continue is None:
            raise InternalError("Cannot find the target to refresh in my children")
        else:
            if can_continue:
                can_continue = (await self._refresh_footer()) is None
            if can_continue:
                if self.parent is not None:
                    await self.parent._refresh_all_children_after(self, can_continue)
    async def _auto_Intro_after_child(self, child: 'Node') -> None:
        child_idx: int | None = None
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                child_idx = i
                break
        if child_idx is None:
            return
        next_idx = child_idx + 1
        if any(isinstance(s, (Intro, Induction)) for s in self.sub_nodes[next_idx:]):
            return
        if not await child.resulting_state().need_intro(False):
            return
        if next_idx < len(self.sub_nodes):
            # Same fractional-id arithmetic as _insert_before_child: route it
            # through the shared, collision-free primitive (the old inline form
            # had the byte-identical collision bug when next == child + [1]).
            new_id = local_step_between(child.local_step,
                                        self.sub_nodes[next_idx].local_step)
        else:
            if not self.opening():
                return
            new_id = self._local_step_of_next_proof_step()
        ml_state = await child.resulting_state().clone(None)
        config = NodeConfig(new_id, ml_state, self)
        try:
            intro = Intro(config, "", None, _auto_injected=True)
        except ProofTreeTooDeep:
            return
        the_session().auto_intro_nodes.append(intro)
        self.sub_nodes.insert(next_idx, intro)
        await intro._refresh_me_alone(auto_intro=True)
    def _local_step_of_next_proof_step(self) -> local_step:
        if self.sub_nodes:
            return incr_id_major(self.sub_nodes[-1].local_step)
        else:
            return "1"
    async def _insert_before_child(self, before: 'Node', gns: 'list[Parsed_Opr]') -> '_InsertBatchResult':
        """Batch-insert `gns` as siblings immediately before `before`.
        Invalidates the status of `before` and all nodes after it (once).
        Catches `GoalIsNontrivial` from node construction; already-created
        nodes are kept in the tree."""
        if not gns:
            return self._InsertBatchResult([], None, None)
        insert_idx: int | None = None
        for i, child in enumerate(self.sub_nodes):
            if child is before:
                insert_idx = i
                break
        if insert_idx is None:
            raise InternalError("Cannot find the target to insert-before in my children")
        before_segs = split_id_into_segs(before.local_step)
        created: list[Node] = []
        stopped_at: int | None = None
        error: GoalIsNontrivial | ProofTreeTooDeep | None = None
        for k, gn in enumerate(gns):
            child_err = self._validate_child_class(gn.cls)
            if child_err is not None:
                stopped_at = k
                error = child_err  # type: ignore[assignment]  — CannotEdit subclass
                break
            if insert_idx + k == 0 and k == 0:
                segs = list(before_segs)
                if segs[-1] > 1:
                    segs[-1] -= 1
                else:
                    segs[-1] -= 1
                    segs.append(1)
                new_id = cat_segs_into_id(segs)
            else:
                prev_step = created[k - 1].local_step if k > 0 else self.sub_nodes[insert_idx - 1].local_step
                # Fractional id strictly between `prev_step` and `before`. The old
                # inline `prev + [1]` collided when `before` had no gap above its
                # predecessor (e.g. before=`0A1`, predecessor=`0A`); local_step_between
                # is byte-identical where it was correct and fixes the collision.
                new_id = local_step_between(prev_step, before.local_step)
            config = NodeConfig(new_id, await before.ml_state.clone(None), self)
            try:
                node = gn.factory(config)
            except (GoalIsNontrivial, ProofTreeTooDeep) as e:
                if isinstance(e, ProofTreeTooDeep):
                    the_session()._depth_limit_exceeded = True
                stopped_at = k
                error = e
                break
            created.append(node)
            self._is_trivial = None
        if created:
            existing_ids = {id(x) for x in self.sub_nodes}
            for node in created:
                if id(node) in existing_ids:
                    raise InternalError("The target node to insert is already in my children")
            self.sub_nodes[insert_idx:insert_idx] = created
            for sibling in self.sub_nodes[insert_idx + len(created):]:
                sibling._on_upstream_change()
        return self._InsertBatchResult(created, stopped_at, error)
    def _remove_child(self, child: Node) -> None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                self.sub_nodes.pop(i)
                return
        raise InternalError("The target node is not my children")
    def latest_refreshed_state(self) -> Minilang_State:
        for child in reversed(self.sub_nodes):
            if child.status.status == EvaluationStatus.Status.SUCCESS:
                return child.resulting_state()
        return self._retrieval_fallback_state()

    def _retrieval_fallback_state(self) -> Minilang_State:
        if self.status.status != EvaluationStatus.Status.SUCCESS:
            if self.parent is not None and isinstance(self.parent, NonLeaf_Node):
                return self.parent.latest_refreshed_state()
        return self.ml_state

    @abstractmethod
    def _resulting_state_of_all_children(self) -> Minilang_State:
        ...
    def _resulting_state_of_child(self, node: Node) -> Minilang_State:
        for i, child in enumerate(self.sub_nodes):
            if child is node:
                if i < len(self.sub_nodes) - 1:
                    return self.sub_nodes[i+1].ml_state
                else:
                    return self._resulting_state_of_all_children()
        raise InternalError("The target node is not my children")
    def _locate_node(self, ids: Sequence[local_step], id: step, pos: int = 0) -> 'Node':
        if pos == len(ids):
            return self
        local_step = ids[pos]
        for child in self.sub_nodes:
            if child.local_step == local_step:
                return child._locate_node(ids, id, pos + 1)
        raise NodeNotFound(id)
    def _all_fixed_vars_before_a_child(self, child: Node, ret: Vars) -> Vars:
        self._all_fixed_vars_before_me(ret)
        self._fixed_vars_at_me(ret)
        for c in self.sub_nodes:
            if c is child:
                return ret
            elif c.status.status != EvaluationStatus.Status.COMMENTED:
                c._fixed_vars_after_me(ret)
        raise InternalError("The target node is not my children")
    def _all_fixed_facts_before_a_child(self, child: Node, ret: Hyps) -> Hyps:
        self._all_fixed_facts_before_me(ret)
        self._fixed_facts_at_me(ret)
        for c in self.sub_nodes:
            if c is child:
                return ret
            elif c.status.status != EvaluationStatus.Status.COMMENTED:
                c._fixed_facts_after_me(ret)
        raise InternalError("The target node is not my children")
    def _all_fixed_tvars_before_a_child(self, child: Node, ret: TVars) -> TVars:
        self._all_fixed_tvars_before_me(ret)
        self._fixed_tvars_at_me(ret)
        for c in self.sub_nodes:
            if c is child:
                return ret
            elif c.status.status != EvaluationStatus.Status.COMMENTED:
                c._fixed_tvars_after_me(ret)
        raise InternalError("The target node is not my children")
    def unfinished_nodes(self, ret: set['Node']) -> None:
        super().unfinished_nodes(ret)
        if self.status.status != EvaluationStatus.Status.COMMENTED:
            for child in self.sub_nodes:
                child.unfinished_nodes(ret)
    def _subtree_stats_live(self) -> 'tuple[int, int]':
        total = 1
        proved = 0
        for child in self.sub_nodes:
            t, p = child.subtree_stats()
            total += t
            proved += p
        return (total, proved)
    async def discard(self) -> None:
        for child in self.sub_nodes:
            await child.discard()
        if self.worker_handle is not None:
            await self.worker_handle.aclose()
        await super().discard()
    async def aclose_all_subagents(self) -> None:
        for child in self.sub_nodes:
            await child.aclose_all_subagents()
        if self.worker_handle is not None:
            await self.worker_handle.aclose()
    def _print_all_warnings(self, file: MyIO) -> None:
        self._print_warnings(0, file, [Warning.Position.HEADER], show_at=True)
        for child in self.sub_nodes:
            child._print_all_warnings(file)
        self._print_warnings(0, file, [Warning.Position.FOOTER], show_at=True)
    def does_quickview_need_detail(self) -> bool:
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return self.changed
        return super().does_quickview_need_detail() or \
            any(child.does_quickview_need_detail() for child in self.sub_nodes)
    def _print_suspended_worker_hint(self, indent: int, file: MyIO) -> None:
        pass
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        self._print_suspended_worker_hint(indent, file)
        if self.does_quickview_need_detail():
            _quickview_children_compressed(self.sub_nodes, indent, file)
        return indent
    def _rename_var(self, old_name: varname, new_name: varname) -> 'Node | None':
        for child in self.sub_nodes:
            if (result := child._rename_var(old_name, new_name)) is not None:
                return result
        return None
    def _rename_fact(self, old_name: str, new_name: str) -> 'Node | None':
        for child in self.sub_nodes:
            if (result := child._rename_fact(old_name, new_name)) is not None:
                return result
        return None
    def reset(self) -> None:
        super().reset()
        for child in self.sub_nodes:
            child.reset()
    def _delete_child(self, child: Node) -> None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                self.sub_nodes.pop(i)
                return
        raise InternalError("The target node is not my children")
    async def _amend_child(self, child: 'Node', gn: Parsed_Opr) -> 'tuple[Node, Node, WorkerHandle | None]':
        child_err = self._validate_child_class(gn.cls)
        if child_err is not None:
            raise child_err
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                config = NodeConfig(child.local_step, await child.ml_state.clone(None), self)
                new_node = gn.factory(config)
                self.sub_nodes[i] = new_node
                self._is_trivial = None
                for sibling in self.sub_nodes[i+1:]:
                    sibling._on_upstream_change()
                # Non-destructive amend: the worker handle (if any) STAYS on
                # `child` through the refresh; the sole caller `amend_me` makes the
                # keep/cancel decision once it sees the commit-vs-revert outcome.
                # `saved` is surfaced so `amend_me` can retarget/aclose it. (Leaf
                # has no `worker_handle`.)
                saved = child.worker_handle if isinstance(child, NonLeaf_Node) else None
                try:
                    await new_node._amend_from(child)
                    if self._can_continue_before_child(new_node):
                        # replace-aware: a fresh-fill InferenceRule amended in may
                        # self-convert to a Rewrite (rebinds new_node).
                        new_node = await _refresh_child_replace_aware(new_node, True)
                    else:
                        await new_node._cancel(self._failed_predecessor_id(new_node))
                    await new_node._refresh_all_after_me()
                except BaseException:
                    # amend hard-failed (incl. cancellation — CancelledError is a
                    # BaseException): cancel the parked worker AND any nested
                    # sub-agent. `child.sub_nodes` may already be moved onto
                    # new_node by `_amend_from`, so sweep BOTH locations (aclose is
                    # idempotent).
                    if isinstance(child, NonLeaf_Node):
                        await child.aclose_all_subagents()
                    await new_node.aclose_all_subagents()
                    raise
                return new_node, child, saved
        raise InternalError("The target node is not my children")
    async def _amend_from(self, old: 'Node') -> None:
        await super()._amend_from(old)
        if not isinstance(old, NonLeaf_Node):
            return
        self.sub_nodes[:] = old.sub_nodes
        old.sub_nodes.clear()
        for child in self.sub_nodes:
            child.parent = self
    def should_I_show_pending_goal(self) -> tuple[Goal, step] | None:
        return None
    @abstractmethod
    def _ctxt_of_filling(self) -> Context:
        ...

class StdBlock(NonLeaf_Node):
    # Pre-parsed sub-proof body (list[Parsed_Opr]).  Subclasses that accept a
    # `proof` field set this in __init__; consumed by `_attach_proof` on
    # first refresh.
    _proof: 'proof | None'
    _body_affects_siblings = False
    _can_host_inherited_children = True
    def __init__(self, config: NodeConfig, thought: str, sub_nodes: list['Node']):
        super().__init__(config, thought, sub_nodes)
        self._proof = None
        # Convention: the _state_before_ending_ should be used only when self.has_ending_opr()
        self._state_before_ending_ = Minilang_State.assign(config.ml_state)
        self._body_subnodes_succeeded = False
        self._allow_multi_goal = False
        self.open_pending_proof_line: int | None = None
        self._prev_pending_goal: Goal | None = None

    @classmethod
    def gen_single(cls, arg: Any, path: str = "<direct>") -> Parsed_Opr:
        """Default for StdBlock subclasses (Have / Suffices / Obtain):
        parse the optional `proof` body eagerly and pass the pre-parsed
        `proof | None` as the second ctor positional.  Subclasses whose
        `__init__` signature is `(config, arg, parsed_proof)` inherit
        this with no override.

        The `cast(Any, cls)` tells pyright that `cls` is actually a
        subclass (Have/Suffices/Obtain) whose `__init__` takes
        `(config, arg, parsed_proof)`, not the generic `type[StdBlock]`
        which it infers (StdBlock's own `__init__` is
        `(config, thought, sub_nodes)`)."""
        arg = cls._validate_arg(arg, path)
        parsed = _parse_optional_raw_proof(arg.get("proof"), f"{path}.proof")
        return Parsed_Opr(
            cls=cls,
            factory=lambda cfg: cast(Any, cls)(cfg, arg, parsed),
            raw=arg)
    async def _cancel(self, cancelled_by: str | None = None) -> None:
        if self.status.status in (EvaluationStatus.Status.CANCELLED,
                                  EvaluationStatus.Status.COMMENTED):
            return
        await super()._cancel(cancelled_by)
        await self._state_before_ending_.reset()
        for child in self.sub_nodes:
            await child._cancel(cancelled_by)
    @abstractmethod
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason | None':
        ...
    def ending_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.END()
    def has_ending_opr(self) -> bool:
        return self.ending_opr() is not None
    @abstractmethod
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        ...
    @abstractmethod
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        ...
    @abstractmethod
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        ...
    # def _state_before_ending(self) -> Minilang_State:
    #     return self._state_before_ending_
    #     #if self.has_ending_opr():
    #     #else:
    #     #    raise InternalError("The node doesn't have an ending operation, but the method `_state_before_ending` is called")
    def _resulting_state_of_all_children(self) -> Minilang_State:
        return self._state_before_ending_
        # if self.has_ending_opr():
        #     return self._state_before_ending()
        # else:
        #     return self.resulting_state()
    def _retrieval_fallback_state(self) -> Minilang_State:
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            return self._state_after_beginning()
        if self.parent is not None and isinstance(self.parent, NonLeaf_Node):
            return self.parent.latest_refreshed_state()
        return self.ml_state
    def _state_after_beginning(self) -> Minilang_State:
        if self.sub_nodes:
            return self.sub_nodes[0].ml_state
        else:
            return self._state_before_ending_
    def _hint_notice_state(self) -> 'Minilang_State | None':
        # A block's authored term (e.g. a Have/Suffices conclusion) is parsed by
        # its beginning op, so any hint notice lands in the after-beginning state.
        # Guard on `beginning_opr() is None` (B6): blocks with no own beginning op
        # (Root, GlobalEnv) author nothing, so they must not re-scan their first
        # child's input state.
        if (self.status.status != EvaluationStatus.Status.SUCCESS
                or self.beginning_opr() is None):
            return None
        return self._state_after_beginning()
    def goal(self) -> 'Goal | None':
        return self._state_after_beginning().leading_goal
    def assemble(self, output: list[Minilang_Operation] | None = None) -> list[Minilang_Operation]:
        if output is None:
            output = []
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return output
        opr = self.beginning_opr()
        if isinstance(opr, FailureReason):
            raise InternalError(f"Cannot assemble a node with failed beginning operation: {opr.reason}")
        if opr is not None:
            output.append(opr)
        for child in self.sub_nodes:
            child.assemble(output)
        opr = self.ending_opr()
        if opr is not None:
            output.append(opr)
        return output

    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        # Re-read `beginning_opr` here instead of taking it as an arg:
        # overrides (e.g. CaseSplit_Like) can do async preparation first
        # (setting cached state on `self`) and let this super-call read
        # the updated opr fresh, without having to rebuild anything.
        # Invariant: `_refresh_me_alone` only calls this when the opr
        # is a concrete `Minilang_Operation` (None / FailureReason are
        # dispatched separately).
        opr = self.beginning_opr()
        assert isinstance(opr, Minilang_Operation), \
            f"_refresh_the_beginning_opr expects a Minilang_Operation, got {type(opr).__name__}"
        try:
            await self._execute_opr(self.ml_state, opr, self._state_after_beginning())
            return None
        except IsabelleError as err:
            return self._beginning_opr_err_msgs(err)
    async def _refresh_footer(self) -> FailureReason | None:
        ending_opr = self.ending_opr()
        if ending_opr is None:
            await self._state_before_ending_.clone(self.resulting_state())
        else:
            try:
                await self._execute_opr(self._state_before_ending_, ending_opr, self.resulting_state())
            except IsabelleError as err:
                return self._ending_opr_err_msgs(err)
        return None
    async def _skip_proof(self) -> None:
        await self._state_after_beginning().sorry_end_all(None, self.resulting_state())
    async def _refresh_all_children_after(self, after: 'Node | Literal["end"]', can_continue_i: bool) -> None:
        can_continue: bool | None = None
        failed_child: Node | None = None
        if after == "end":
            can_continue = True
        else:
            for child in self.sub_nodes:
                if can_continue is None:
                    if child is after:
                        can_continue = can_continue_i
                        if not can_continue_i:
                            failed_child = child
                else:
                    if can_continue:
                        # replace-aware: see NonLeaf_Node._refresh_all_children_after.
                        child = await _refresh_child_replace_aware(child, True)
                        if not _status_can_continue(child.status.status):
                            can_continue = False
                            failed_child = child
                    else:
                        await child._cancel(failed_child.id if failed_child else None)
        if can_continue is None:
            raise InternalError("Cannot find the target to refresh in my children")
        footer_reason: FailureReason | None = None
        if can_continue:
            footer_reason = await self._refresh_footer()
            if footer_reason is not None:
                can_continue = False
        if self.status.status != EvaluationStatus.Status.FAILURE:
            if can_continue:
                self._body_subnodes_succeeded = True
                self.status = EvaluationStatus.Success(0)
            else:
                self._body_subnodes_succeeded = False
                if failed_child is not None:
                    await failed_child.ml_state.clone(self._state_before_ending_)
                    reason = self._child_refresh_failure_err_msgs(failed_child)
                else:
                    reason = footer_reason
                self.status = EvaluationStatus.Success(0, reason)
        if can_continue and self._body_affects_siblings:
            if self.parent is not None:
                await self.parent._refresh_all_children_after(self, can_continue)
    async def _refresh_me_alone(self, auto_intro: bool):
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            await self.ml_state.clone(self.resulting_state())
            await self._state_before_ending_.reset()
            self.age = the_session().age
            return
        begin_opr = self.beginning_opr()
        now = time()
        reason: FailureReason | None = None
        head_succeeded = True
        can_continue: bool = True
        if isinstance(begin_opr, FailureReason):
            head_succeeded = False
            can_continue = False
            reason = begin_opr
        elif begin_opr is not None:
            reason = await self._refresh_the_beginning_opr()
            if reason is not None:
                head_succeeded = False
                can_continue = False
        else:
            await self.ml_state.clone(self._state_after_beginning())
        await super()._refresh_me_alone(auto_intro)
        failed_child: Node | None = None
        cancel_by: str | None = self.id if not can_continue else None
        for child in self.sub_nodes:
            if can_continue:
                # replace-aware: a fresh-fill InferenceRule child failing its first
                # execution during whole-container re-refresh may self-convert.
                child = await _refresh_child_replace_aware(child, True)
                if child.status.status != EvaluationStatus.Status.COMMENTED:
                    can_continue = child.status.status == EvaluationStatus.Status.SUCCESS
                    if not can_continue:
                        reason = self._child_refresh_failure_err_msgs(child)
                        failed_child = child
                        cancel_by = child.id
            else:
                await child._cancel(cancel_by)
        if can_continue:
            reason = await self._refresh_footer()
            if reason is not None:
                can_continue = False
        if can_continue:
            self._body_subnodes_succeeded = True
            self.status = EvaluationStatus.Success(time() - now)
        elif head_succeeded:
            self._body_subnodes_succeeded = False
            if failed_child is not None:
                await failed_child.ml_state.clone(self._state_before_ending_)
            await self._skip_proof()
            self.status = EvaluationStatus.Success(time() - now, reason)
        else:
            self._body_subnodes_succeeded = False
            assert reason is not None
            self.status = EvaluationStatus.Failure(time() - now, reason)
        if auto_intro and not self._has_considered_auto_intro and self.status.status == EvaluationStatus.Status.SUCCESS:
            self._has_considered_auto_intro = True
            await self._auto_intro_after_me()
    def _ctxt_of_filling(self) -> Context:
        vars = self._all_fixed_vars_before_me({})
        tvars = self._all_fixed_tvars_before_me({})
        hyps = self._all_fixed_facts_before_me({})
        self._fixed_vars_at_me(vars)
        self._fixed_tvars_at_me(tvars)
        self._fixed_facts_at_me(hyps)
        for child in self.sub_nodes:
            if child.status.status != EvaluationStatus.Status.COMMENTED:
                child._fixed_vars_after_me(vars)
                child._fixed_tvars_after_me(tvars)
                child._fixed_facts_after_me(hyps)
        return Context(vars, tvars, hyps)
    @abstractmethod
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False) -> None:
        ...
    def has_pending_goal(self) -> bool:
        """Whether this goal node still has unproven proof obligations.
        Returns False when state is uninitialized, has no goals,
        or only has the 'True' artifact from conjunction splitting."""
        s = self._state_before_ending_
        if not s.initialized():
            return False
        lg = s.leading_goal
        return lg is not None and lg.conclusion != "True"
    def should_I_show_pending_goal(self) -> tuple[Goal, step] | None:
        if not self.has_pending_goal():
            return None
        to_fill = self._id_of_openning_prf_to_fill()
        if to_fill is None:
            return None
        s = self._state_before_ending_
        if s.display_goals_count > 1 and not self._allow_multi_goal:
            raise InternalError("The open goals of StdBlock should not exceed one. "
            "To express multiple goals, you should use a StdBlock whose children are GoalNodes. See Rule as an example.")
        return (cast(Goal, s.leading_goal), to_fill)
    def _should_print_footer_pending_goal(self) -> bool:
        return True
    def _print_footer(self, indent: int, file: MyIO, show_warnings: bool = False) -> None:
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.FOOTER])
        if self.opening():
            if not self._state_before_ending_.initialized():
                print_indent(indent, file)
                file.write("Error: Evaluation cancelled due to failures above\n")
            else:
                result = self.should_I_show_pending_goal()
                if result is not None:
                    goal, to_fill = result
                    replace_existing = any(child.id == to_fill for child in self.sub_nodes)
                    self.open_pending_proof_line =\
                        print_pending_goal(goal, to_fill, indent, file, self._ctxt_of_filling(),
                                           show_goal=self._should_print_footer_pending_goal(),
                                           replace_existing=replace_existing)
                else:
                    self.open_pending_proof_line = None
    def is_proof_finished(self) -> bool:
        unfinished_nodes = set()
        self.unfinished_nodes(unfinished_nodes)
        return len(unfinished_nodes) == 0
    def _subtree_stats_live(self) -> 'tuple[int, int]':
        total, proved = super()._subtree_stats_live()
        # A completed block covers its whole subtree as proved work.
        if self.is_proof_finished():
            proved = total
        return (total, proved)
    def unfinished_nodes(self, ret: set['Node']) -> None:
        super().unfinished_nodes(ret)
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return
        if self.opening():
            if not self._state_before_ending_.initialized() or self.has_pending_goal():
                ret.add(self)
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ("proof", indent+1)
    def _id_of_openning_prf_to_fill(self) -> step | None:
        if not self.opening():
            return None
        # If the tail of sub_nodes is a run of non-successful Obvious nodes,
        # return the id of the earliest (leftmost) one so the agent can replace
        # it rather than append after it. See Node.fill for the matching
        # replacement logic.
        i = len(self.sub_nodes)
        while i > 0:
            child = self.sub_nodes[i - 1]
            if isinstance(child, Obvious) and not _status_can_continue(child.status.status):
                i -= 1
            else:
                break
        if i < len(self.sub_nodes):
            return self.sub_nodes[i].id
        if self.id:
            return f"{self.id}.{self._local_step_of_next_proof_step()}"
        else:
            return self._local_step_of_next_proof_step()
    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False):
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_header(indent, file, show_warnings=show_warnings)
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return indent
        self._print_suspended_worker_hint(indent, file)
        title, child_indent = self._title_of_children(indent)
        if title is None:
            for step in self.sub_nodes:
                step.print(child_indent, file, update_line, show_warnings=show_warnings)
        else:
            if self.sub_nodes:
                print_indent(indent, file)
                file.write(title)
                file.write(":\n")
                for step in self.sub_nodes:
                    step.print(child_indent, file, update_line, show_warnings=show_warnings)
            else:
                print_indent(indent, file)
                file.write(title)
                file.write(": empty\n")
        self._print_footer(indent, file, show_warnings=show_warnings)
        return indent
    def _print_suspended_worker_hint(self, indent: int, file: MyIO) -> None:
        """When a sub-agent is parked on this node, tell the agent that dispatched
        it how to resume or terminate it. Shown only to that sub-agent's *direct*
        dispatcher — ``worker_handle.session`` is the dispatching session — so an
        agent sees markers for its own immediate sub-agents but never for nested
        grandchildren (whose handle.session is the intermediate worker)."""
        if (self.worker_handle is not None
                and self.worker_handle.session is _session_var.get(None)):
            print_indent(indent, file)
            sid = the_session()._display_id(self.id)
            s = the_session()
            file.write(f"A sub-agent is suspended on this step. Call `{s.tool_name(TOOL_SUBAGENT)}` with step {sid} to resume it, or `{s.tool_name(TOOL_CLOSE_SUBAGENT)}` with step {sid} to cancel and remove it.\n")
    def does_quickview_need_detail(self) -> bool:
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return self.changed
        if super().does_quickview_need_detail():
            return True
        if self.opening():
            if not self._state_before_ending_.initialized() or self.should_I_show_pending_goal() is not None:
                return True
        return False
    def _quickview_pending_footer(self, indent: int, file: MyIO) -> None:
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return
        if self.opening():
            if not self._state_before_ending_.initialized():
                print_indent(indent, file)
                file.write("Evaluation pending\n")
                self._prev_pending_goal = None
            elif (goal_and_step := self.should_I_show_pending_goal()) is not None:
                goal, step_to_fill = goal_and_step
                print_indent(indent, file)
                line_hint = f" (line {self.open_pending_proof_line})" if self.open_pending_proof_line is not None and the_session().quickview_line_numbers else ""
                shown_fill = the_session()._display_id(step_to_fill)
                if the_session().showed_fill_hint:
                    file.write(f"Unfinished Proof{line_hint}. Fill step `{shown_fill}`\n")
                else:
                    file.write(f"Unfinished Proof{line_hint}. Call command `edit` with action `fill` and target step `{shown_fill}`\n")
                    the_session().showed_fill_hint = True
                suppressed = self._ctxt_of_filling()
                visible = goal.visible(suppressed)
                already_printed = None
                for child in reversed(self.sub_nodes):
                    if child._the_single_printed_goal is not None:
                        already_printed = child
                        break
                if already_printed is not None \
                        and already_printed._the_single_printed_goal is not None \
                        and already_printed._the_single_printed_goal.conclusion == goal.conclusion:
                    self._prev_pending_goal = visible
                elif visible != self._prev_pending_goal:
                    print_goal(goal, indent, True, file, suppressed)
                    self._prev_pending_goal = visible
            else:
                self._prev_pending_goal = None
        else:
            self._prev_pending_goal = None
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        self._quickview_pending_footer(indent, file)
        return indent
    def quickview_string(self, indent: int) -> str:
        buffer = StringIO()
        self.quickview(indent, MyIO(buffer))
        return buffer.getvalue()
    async def _attach_proof(self, auto_intro: bool) -> 'FailureReason | None':
        """Consume ``self._proof`` (a pre-parsed list[Parsed_Opr]) at first
        refresh and attach each as a direct child of this block.

        If ``auto_intro`` is True (only Have today) and the provided body's
        first Parsed_Opr is NOT an ``Intro``, an auto-Intro is injected before
        the provided list when the current goal state calls for one
        (``need_intro(False)``).

        If any children were inherited via ``_amend_from`` (previous
        block's sub_nodes) and a provided list is given, Q6 redirects them
        into the LAST provided node's body when that node is a StdBlock
        that can host children; otherwise they are emitted as a
        ``_warn_discarded_nodes`` entry and dropped.

        Returns ``FailureReason`` only on bugs during construction;
        returns ``None`` on success.  The appended children are not
        refreshed here — the outer ``StdBlock._refresh_me_alone`` loop
        does that."""
        if self._proof is not None:
            inherited = list(self.sub_nodes)
            # Preserve the post-beginning state: when sub_nodes is non-empty
            # (inherited via _amend_from), the super()._refresh_the_beginning_opr
            # call just wrote the post-beginning state into sub_nodes[0].ml_state
            # (because `_state_after_beginning()` returned that pointer).  After
            # we wipe sub_nodes below, `_state_after_beginning()` would fall
            # back to `_state_before_ending_`, which still holds the STALE
            # pre-beginning state.  Sync it here so newly-attached children
            # clone a valid post-beginning state.
            if inherited:
                await inherited[0].ml_state.clone(self._state_before_ending_)
            self.sub_nodes = []
            gns = list(self._proof)
            self._proof = None
            if auto_intro and await self._should_inject_leading_intro(
                    self._state_after_beginning(), gns):
                local_step = self._local_step_of_next_proof_step()
                ml_state = await self._state_after_beginning().clone(None)
                config = NodeConfig(local_step, ml_state, self)
                try:
                    intro = Intro(config, "", None, _auto_injected=True)
                except ProofTreeTooDeep:
                    pass
                else:
                    self.sub_nodes.append(intro)
                    the_session().auto_intro_nodes.append(intro)
            for gn in gns:
                local_step = self._local_step_of_next_proof_step()
                ml_state = await self._state_after_beginning().clone(None)
                sub_config = NodeConfig(local_step, ml_state, self)
                try:
                    new_child = gn.factory(sub_config)
                except ProofTreeTooDeep:
                    the_session()._depth_limit_exceeded = True
                    return FailureReason("Proof tree depth exceeds the limit")
                except GoalIsNontrivial:
                    return FailureReason(
                        "Nested proof contains Obvious on a goal that is not "
                        "trivially provable")
                self.sub_nodes.append(new_child)
            if inherited:
                last = self.sub_nodes[-1] if self.sub_nodes else None
                if isinstance(last, StdBlock) and last._can_host_inherited_children:
                    for child in inherited:
                        child.parent = last
                    last.sub_nodes.extend(inherited)
                else:
                    self._warn_discarded_nodes(
                        inherited,
                        Warning.Position.FOOTER)
                    # No host for the inherited children — they leave the tree;
                    # close their sub-agents.
                    for d in inherited:
                        await d.aclose_all_subagents()
            return None
        if (auto_intro
                and not self.sub_nodes
                and await self._state_after_beginning().need_intro(False)):
            local_step = self._local_step_of_next_proof_step()
            ml_state = await self._state_after_beginning().clone(None)
            config = NodeConfig(local_step, ml_state, self)
            try:
                intro = Intro(config, "", None, _auto_injected=True)
            except ProofTreeTooDeep:
                pass
            else:
                self.sub_nodes.append(intro)
                the_session().auto_intro_nodes.append(intro)
        return None
    async def _should_inject_leading_intro(
            self, state: 'Minilang_State', gns: 'list[Parsed_Opr]') -> bool:
        """Decide whether to auto-inject an Intro before the body `gns`,
        evaluated against `state` (the body's pre-state).

        Mirrors the historical gate — inject when the goal needs intro and the
        body does not already lead with structured introduction — with ONE
        loosening: a body whose FIRST step is an Induction whose target hits a
        not-yet-introduced leading ∀/⋀ binder still gets the Intro. (The agent
        wrote `[Induction]` where it should have written `[Intro, Induction]`;
        inducting on a still-bound variable is ill-typed otherwise.)"""
        if not await state.need_intro(False):
            return False
        if not any(gn.cls is Intro or gn.cls is Induction for gn in gns):
            return True
        first = gns[0]
        if first.cls is Induction:
            tgt = first.raw.get("target_isabelle_term")
            return bool(tgt) and await state.induction_target_hits_leading_binder(tgt)
        return False
    async def append(
        self, gns: 'list[Parsed_Opr]',
        op: 'EditOperation' = EditOperation.FILL,
    ) -> 'EditOutcome':
        """Append `gns` as children, in order.  For each: build, attach,
        refresh, cascade.  Catches Group-B construction failures
        (`CannotEdit_BlockClosed`, `GoalIsNontrivial`) into
        `EditOutcome.failure` and stops the batch.  After each commit,
        if the node's refresh resolves to FAILURE, invokes
        `_on_edit_failure`; the returned `EditFailureBehavior` decides
        whether the batch continues, stops, or stops-and-reverts.

        Auto-Intro injection is delegated to the ``_auto_intro_after_me``
        mechanism inside ``_refresh_me_alone`` (via ``auto_intro=True``).
        When the user's next item is already an Intro, ``auto_intro`` is
        set to False to suppress auto-injection."""
        outcome = EditOutcome(operation=op, request=gns)
        def _block_closed(unapplied: 'list[Parsed_Opr]',
                          failed_index: int) -> CannotEdit_BlockClosed:
            closer = self.sub_nodes[-1] if self.sub_nodes else None
            return CannotEdit_BlockClosed(
                closer.id if (closer is not None and closer._closes_my_parent()) else None,
                self.id,
                operation=op, unapplied_oprs=unapplied,
                is_error=len(outcome.committed) == 0,
                failed_opr=gns[failed_index] if failed_index < len(gns) else None,
                failed_index=failed_index)
        if not self.opening():
            outcome.failure = _block_closed(list(gns), 0)
            return outcome
        if not gns:
            return outcome
        for i, gn in enumerate(gns):
            if not self.opening():
                outcome.failure = _block_closed(list(gns[i:]), i)
                return outcome
            child_err = self._validate_child_class(gn.cls)
            if child_err is not None:
                child_err.operation = op
                child_err.unapplied_oprs = list(gns[i:])
                child_err.is_error = len(outcome.committed) == 0
                child_err.failed_opr = gn
                child_err.failed_index = i
                outcome.failure = child_err
                return outcome
            local_step = self._local_step_of_next_proof_step()
            ml_state = await self._state_before_ending_.clone(None)
            config = NodeConfig(local_step, ml_state, self)
            try:
                node = gn.factory(config)
            except (GoalIsNontrivial, ProofTreeTooDeep) as e:
                if isinstance(e, ProofTreeTooDeep):
                    the_session()._depth_limit_exceeded = True
                e.operation = op
                e.unapplied_oprs = list(gns[i:])
                e.is_error = len(outcome.committed) == 0
                e.failed_opr = gn
                e.failed_index = i
                outcome.failure = e
                return outcome
            if node is None:
                # Factory refused (rare); skip this gn.
                continue
            self.sub_nodes.append(node)
            self._is_trivial = None
            has_later_intro_or_induction = any(
                gn.cls is Intro or gn.cls is Induction
                for gn in gns[i + 1:])
            behavior, cancelled = await outcome.commit_and_hook(
                self._can_continue_before_child(node), node,
                auto_intro=not has_later_intro_or_induction)
            if behavior is not EditFailureBehavior.CONTINUE:
                return outcome
        return outcome


class GoalContainer(NonLeaf_Node):
    def _nearest_goal_for_subagent(self) -> 'Node | None':
        return None  # a container of goals, not itself a delegatable goal
    def _child_has_ending_opr(self, child : Node) -> bool:
        # Non-last children emit NEXT to advance to the next sibling
        # subgoal; the last child emits nothing. If the container as
        # a whole needs a trailing END (e.g. Root, Define's deferred
        # path), the container itself emits it via its own
        # has_ending_opr / ending_opr.
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                return i < len(self.sub_nodes) - 1
        raise InternalError("The given argument is not a child of this node")
    def _case_vars_of_child(self, child_ind: int) -> list[varname_spec] | None:
        return None
    def _ending_opr_of_child(self, child : Node) -> Minilang_Operation | None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i < len(self.sub_nodes) - 1:
                    return Minilang_Operation.NEXT(self._case_vars_of_child(i+1))
                else:
                    return None
        raise InternalError("The given argument is not a child of this node")
    async def _skip_child_proof(self, child : 'GoalNode') -> None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i < len(self.sub_nodes) - 1:
                    await child._state_after_beginning().sorry_next(self._case_vars_of_child(i+1), child.resulting_state())
                else:
                    # Last child: cheat one subgoal in place (no NEXT/END)
                    # so that child.resulting_state() (= parent._state_before_ending_)
                    # gets a valid post-sorry prooftree.
                    await child._state_after_beginning().sorry_only(child.resulting_state())
                return None
        raise InternalError("The given argument is not a child of this node")
    async def _refresh_all_children_after(self, after: 'Node | Literal["end"]', can_continue_i: bool) -> None:
        # Each subgoal in AoA is independent, so we don't need to refresh the children after the current node.
        return None

class GoalNode(StdBlock):
    """
    GoalNode is a container that stores the proofs of a single goal.
    When executing a Node produces multiple subgoals, each child of that Node
    is a GoalNode corresponding to one of the subgoals, and the children of each
    GoalNode are the proof steps for its corresponding subgoal.
    """
    _changes_pending_goal = False
    case_vars: list[Var] | None
    case_hyps: list[Hyp] | None
    case_tvars: list[tuple[varname, typ]] | None

    def _nearest_goal_for_subagent(self) -> 'Node | None':
        # A2: a GoalNode (a case GoalNode from CaseSplit/Induction/Branch, or a
        # Define's obligation GoalNode) is NOT a self-contained delegation unit —
        # it carries local context (case hyps / IH). Redirect UP to the enclosing
        # named block (Have/Obtain/Suffices/SetupRewriting) or Define, mirroring
        # the SubgoalMaker base. Delegatable set = {Have, Obtain, Suffices,
        # SetupRewriting, Define}.
        return self.parent._nearest_goal_for_subagent() if self.parent is not None else None
    def __init__(self, config: NodeConfig, is_single_goal: bool, show_goal: bool,
                 pending_proof: 'proof | None' = None):
        super().__init__(config, "", [])
        self.is_single_goal = is_single_goal
        self.show_goal = show_goal
        self._allow_multi_goal = True
        self._kind = "goal"
        self.case_vars = None
        self.case_hyps = None
        self.case_tvars = None
        self._prev_quickview_context: tuple[Vars, TVars, Hyps] | None = None
        self._prev_quickview_conclusion: term | None = None
        self._pending_proof: 'proof | None' = pending_proof
    @property
    def titled_id(self) -> str:
        shown = the_session()._display_id(self.id)
        if shown.startswith("goal"):
            return shown
        return f"goal {shown}"
    def goal(self) -> Goal | None:
        return self.ml_state.leading_goal
    def id_of_goal(self) -> step | None:
        if self.is_single_goal:
            if self.parent is not None:
                return self.parent.id_of_goal()
            else:
                return None
        else:
            return self.id
    def _should_print_footer_pending_goal(self) -> bool:
        return not all(isinstance(c, (Have, Obtain)) for c in self.sub_nodes)
    def beginning_opr(self) -> 'Minilang_Operation | None':
        return None
    def ending_opr(self) -> Minilang_Operation | None:
        if not isinstance(self.parent, GoalContainer):
            raise InternalError("The parent of a GoalNode is not a GoalContainer")
        return self.parent._ending_opr_of_child(self)
    def _has_ending_opr(self) -> bool:
        if not isinstance(self.parent, GoalContainer):
            raise InternalError("The parent of a GoalNode is not a GoalContainer")
        return self.parent._child_has_ending_opr(self)
    async def _skip_proof(self) -> None:
        if not isinstance(self.parent, GoalContainer):
            raise InternalError("The parent of a GoalNode is not a GoalContainer")
        return await self.parent._skip_child_proof(self)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A GoalNode doesn't have a beginning operation")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason("Fail to prove the goal because one of the following proof steps fails.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        if self.sub_nodes:
            return FailureReason("The goal is nontrivial. A step-by-step proof is required.")
        else:
            return FailureReason("Each of the following proof steps above is valid, but the goal doesn't trivially follow from these steps. Please provide more detailed proof steps.")
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        if self.show_goal:
            goal = self.goal()
            if goal is None:
                print_indent(indent, file)
                file.write("goal: unknown, evaluation pending\n")
            else:
                if self.case_vars or self.case_hyps:
                    merged_vars = {v[0]: v[1] for v in (self.case_vars or [])} | goal.context.vars
                    merged_hyps = {h[0]: h[1] for h in (self.case_hyps or [])} | goal.context.hyps
                    merged_tvars = {t[0]: t[1] for t in (self.case_tvars or [])} | goal.context.tvars
                    goal = Goal(Context(merged_vars, merged_tvars, merged_hyps), goal.conclusion)
                print_goal(goal, indent, True, file, self._ctxt_before_me())
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def _print_step_id(self, indent: int, file: MyIO, update_line: bool = False) -> int:
        if update_line:
            self.line = file.current_line()
        if self.is_single_goal:
            return indent
        else:
            return super()._print_step_id(indent, file, update_line)
    async def _refresh_me_alone(self, auto_intro: bool):
        is_init = self._first_time
        old_case = (self.case_vars, self.case_tvars, self.case_hyps)
        consider_case_msgs = [m for m in self.ml_state.messages if isinstance(m, Consider_Case_Msg)]
        match consider_case_msgs:
            case []:
                pass
            case [consider_case_msg]:
                self._reset_local_step(consider_case_msg.case)
                self.case_vars = consider_case_msg.vars
                self.case_tvars = consider_case_msg.tvars
                self.case_hyps = consider_case_msg.hyps
            case _:
                raise InternalError(f"Expected exactly one Consider_Case_Msg in Case's messages, got {len(consider_case_msgs)}")
        if not is_init and (self.case_vars, self.case_tvars, self.case_hyps) != old_case:
            self.changed = True
        # `_pending_proof` may have been populated by the parent
        # Install `_pending_proof` (set by SubgoalMaker orchestration)
        # as sub_nodes, with auto-Intro injection if needed.
        if self._pending_proof is not None and not self.sub_nodes:
            gns = self._pending_proof
            self._pending_proof = None
            if await self._should_inject_leading_intro(self.ml_state, gns):
                local_step = self._local_step_of_next_proof_step()
                ml_state = await self.ml_state.clone(None)
                config = NodeConfig(local_step, ml_state, self)
                try:
                    intro = Intro(config, "", None, _auto_injected=True)
                except ProofTreeTooDeep:
                    pass
                else:
                    self.sub_nodes.append(intro)
                    the_session().auto_intro_nodes.append(intro)
            for gn in gns:
                local_step = self._local_step_of_next_proof_step()
                ml_state = await self.ml_state.clone(None)
                sub_config = NodeConfig(local_step, ml_state, self)
                try:
                    self.sub_nodes.append(gn.factory(sub_config))
                except (GoalIsNontrivial, ProofTreeTooDeep) as e:
                    if isinstance(e, ProofTreeTooDeep):
                        the_session()._depth_limit_exceeded = True
                    break
        elif is_init and not self.sub_nodes and await self.ml_state.need_intro(False):
            local_step = self._local_step_of_next_proof_step()
            ml_state = await self.ml_state.clone(None)
            config = NodeConfig(local_step, ml_state, self)
            try:
                intro = Intro(config, "", None, _auto_injected=True)
            except ProofTreeTooDeep:
                pass
            else:
                self.sub_nodes.append(intro)
                the_session().auto_intro_nodes.append(intro)
        return await super()._refresh_me_alone(auto_intro)
    async def _auto_intro_after_me(self) -> None:
        pass
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        goal = self.goal()
        if goal is not None:
            ret.update(goal.context.vars)
        return ret
    def _fixed_tvars_at_me(self, ret: TVars) -> TVars:
        goal = self.goal()
        if goal is not None:
            ret.update(goal.context.tvars)
        return ret
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        goal = self.goal()
        if goal is not None:
            ret.update(goal.context.hyps)
        return ret
    def quickview_header(self, indent: int, file: MyIO) -> int:
        if self.is_single_goal:
            if self._should_print_done():
                print_indent(indent, file)
                file.write(f"{self._done_label}\n")
            return indent
        else:
            done_mark = f"{self._done_label}, " if self._should_print_done() else ""
            line_mark = f"line {self.line}, " if the_session().quickview_line_numbers else ""
            marks = f"{done_mark}{line_mark}".rstrip(", ")
            suffix = f" ({marks})" if marks else ""
            print_indent(indent, file)
            file.write(f"- {the_session()._display_id(self.id)}{suffix}\n")
            child_indent = indent + 1
            if self.show_goal:
                goal = self.goal()
                if goal is not None:
                    suppressed = self._ctxt_before_me()
                    if self.case_vars or self.case_hyps:
                        merged_vars = {v[0]: v[1] for v in (self.case_vars or [])} | goal.context.vars
                        merged_hyps = {h[0]: h[1] for h in (self.case_hyps or [])} | goal.context.hyps
                        merged_tvars = {t[0]: t[1] for t in (self.case_tvars or [])} | goal.context.tvars
                    else:
                        merged_vars = goal.context.vars
                        merged_hyps = goal.context.hyps
                        merged_tvars = goal.context.tvars
                    visible_vars = {k: v for k, v in merged_vars.items() if k not in suppressed.vars}
                    visible_hyps = {k: v for k, v in merged_hyps.items() if k not in suppressed.hyps}
                    visible_tvars = {k: v for k, v in merged_tvars.items() if k not in suppressed.tvars}
                    visible = (visible_vars, visible_tvars, visible_hyps)
                    if visible != self._prev_quickview_context and self.does_quickview_need_detail():
                        print_vars(merged_vars.items(), child_indent, file, suppressed.vars)
                        print_type_vars(merged_tvars.items(), child_indent, file, suppressed.tvars)
                        print_hyps(merged_hyps.items(), child_indent, file, suppressed.hyps)
                        self._prev_quickview_context = visible
                    conclusion = goal.conclusion
                    pending = self.should_I_show_pending_goal()
                    if self.does_quickview_need_detail() and (pending is None or pending[0].conclusion != conclusion):
                        if conclusion != self._prev_quickview_conclusion:
                            conclusion_str = conclusion.unicode
                            if len(conclusion_str) > AGENT_GOAL_CHAR_LIMIT:
                                conclusion_str = _trunc_expr_base(conclusion_str, AGENT_GOAL_CHAR_LIMIT)
                            print_indent(child_indent, file)
                            file.write(f"goal: {conclusion_str}\n")
                            self._prev_quickview_conclusion = conclusion
            return child_indent

class _OpenSubgoalBlock(Enum):
    """Result of `SubgoalMaker._should_open_proof_block` — unifies the former
    two methods `_should_open_proof_block` (open-or-not) and
    `_block_closes_parent` (close-or-not-when-open).

    - ``NO``: no subgoal block opens this refresh (e.g. Intro on a goal that
      no longer has meta-quantifiers, or Define when it didn't enter the
      deferred-block path).
    - ``YES``: a subgoal block opens but the enclosing parent proof-line
      is NOT closed — this is `Define`'s deferred block, bracketed by an
      explicit END opcode so the parent's proof line continues past it.
    - ``YES_AND_CLOSE_PARENT_BLOCK``: a subgoal block opens AND the parent's
      proof line is truncated via `_close_by` — any siblings after this
      node become meaningless and are moved to a FOOTER warning.

    Invariant: the closing info is only meaningful when a block opens, which
    is why these three values are exhaustive (there is no
    "no-open-but-close-parent" case)."""
    NO = 0
    YES = 1
    YES_AND_CLOSE_PARENT_BLOCK = 2

PREFIX_NEW = "new-"
PREFIX_OLD = "old-"
CASE_EXISTING = "the-existing-proof"


# Operations whose result may carry residual schematic variables that the
# post-rule instantiation probe must eliminate.
_POST_INST_COMMANDS = frozenset({"RULE", "CASE_SPLIT", "INDUCT"})
# Backstop on the post-instantiation fixpoint loop (real need is 1-3 rounds;
# generous so cross-round type dependencies converge, not a shrink measure).
_MAX_POST_INST_ROUNDS = 16

class SubgoalMaker(GoalContainer, StdBlock):
    _can_host_inherited_children = False
    def _nearest_goal_for_subagent(self) -> 'Node | None':
        # A subgoal-maker's subgoals aren't independently delegatable; redirect up
        # to the enclosing goal (overriding GoalContainer's None).
        return self.parent._nearest_goal_for_subagent() if self.parent is not None else None
    def _should_print_done(self) -> bool:
        return bool(self.sub_nodes) and super()._should_print_done()
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._initial_goal_index : int = 1
        # Latched parent-closing decision, set in `_refresh_the_beginning_opr` on
        # EVERY refresh branch (incl. the reuse `pass`) so `opening()` can derive
        # my parent's closed-ness from me without a stored `_closed_by`.
        # `_opened_count` = number of subgoals I opened; `_closes_my_parent`
        # requires my live case children to still equal it (the delete-case fix).
        self._opened_closing_block: bool = False
        self._opened_count: int = 0
        self._supplied_proofs: 'dict[str, proof_with_case_vars] | None' = None
        # Post-rule schematic instantiation (RULE/CaseSplit/Induction only).
        # `None` = not yet probed; otherwise the ordered list of instantiation
        # rounds (each a list of (var-name, value) pairs) baked into the op so
        # it produces a schematic-free state and replays from cache. Reset on
        # upstream change (see _on_upstream_change). For non-rule subgoal makers
        # it stays None and is never read.
        self._post_insts: 'list[list[tuple[str, xterm | xtyp]]] | None' = None

    def _on_upstream_change(self) -> None:
        super()._on_upstream_change()
        # The state flowing in changed → any recorded instantiations were
        # computed against a stale goal; re-probe from scratch next refresh.
        self._post_insts = None

    def _beginning_opr_with_insts(
            self, rounds: 'list[list[tuple[str, xterm | xtyp]]]') -> 'Minilang_Operation | FailureReason | None':
        """Rebuild this node's beginning op with `rounds` baked in, without
        disturbing `self._post_insts` — used by the probe to re-execute the op
        with the rounds accumulated so far on a throwaway scratch state."""
        saved = self._post_insts
        self._post_insts = rounds
        try:
            return self.beginning_opr()
        finally:
            self._post_insts = saved

    async def _execute_opr(self, from_state: 'Minilang_State',
                           opr: 'Minilang_Operation',
                           dest: 'Minilang_State | None') -> None:
        if opr.command in _POST_INST_COMMANDS and self._post_insts is None:
            rounds: 'list[list[tuple[str, xterm | xtyp]]]' = []
            for _ in range(_MAX_POST_INST_ROUNDS):
                scratch_op = self._beginning_opr_with_insts(rounds)
                if not isinstance(scratch_op, Minilang_Operation):
                    break  # beginning_opr degraded (e.g. FailureReason); let the real execute handle it
                try:
                    # STATE-level execute (no recursion); throwaway scratch, not logged.
                    scratch = await from_state.execute(scratch_op, None, log=False)
                except (IsabelleError, InternalError):
                    break  # the base op itself failed — let the real execute below surface it
                try:
                    term_vars, type_vars = await scratch.schematic_variables_of(whole=True)
                    if not term_vars and not type_vars:
                        self._post_insts = rounds
                        break
                    # Term-first: a term value pins most type vars via infer_instantiate,
                    # so ask for types only once no term vars remain.
                    if term_vars:
                        offered, kind = term_vars, "term"
                    else:
                        offered, kind = type_vars, "type"
                    schematic_vars = [(name.unicode, ty.unicode) for name, ty in offered.items()]
                    rnd = await the_session().launch_interaction(
                        Interaction_InstantiatePostSchematics(scratch, schematic_vars, kind))
                    rounds = rounds + [rnd]
                finally:
                    if scratch._initialized:
                        await scratch.reset()
            else:
                raise IsabelleError(
                    [f"Could not eliminate the residual schematic variables of this "
                     f"{opr.command} operation within {_MAX_POST_INST_ROUNDS} rounds of "
                     f"instantiation."], None)
            opr = cast(Minilang_Operation, self.beginning_opr())
        await super()._execute_opr(from_state, opr, dest)

    def _all_fixed_facts_before_a_child(self, child: 'Node', ret: Hyps) -> Hyps:
        super()._all_fixed_facts_before_a_child(child, ret)
        # A case's own freshly-introduced hypotheses must be shown even when
        # they shadow an ancestor's same-named hyp: an induction/case-split
        # specialises a carried premise per case (e.g. `premise0: k ≤ n` becomes
        # `premise0: n ≤ 0` in the base case). Drop the case's own hyp names
        # from the child's suppression context so the specialised version shows.
        for name, _ in (getattr(child, "case_hyps", None) or []):
            ret.pop(name, None)
        return ret
    def _all_fixed_vars_before_a_child(self, child: 'Node', ret: Vars) -> Vars:
        super()._all_fixed_vars_before_a_child(child, ret)
        # Likewise a case's own fresh variables (e.g. a generalized var whose
        # smart-rename reused the consumed induction target's name).
        for name, _ in (getattr(child, "case_vars", None) or []):
            ret.pop(name, None)
        return ret

    @staticmethod
    def _node_to_parsed_opr(node: 'Node') -> Parsed_Opr:
        def factory(config: NodeConfig) -> 'Node':
            node.parent = config.parent
            node.ml_state = config.ml_state
            node.local_step = config.local_step
            node._recompute_id()
            node.warnings = []
            node._first_time = True
            node._has_considered_auto_intro = False
            return node
        return Parsed_Opr(cls=type(node), factory=factory, raw={})

    async def _amend_from(self, old: 'Node') -> None:
        await Node._amend_from(self, old)
        if isinstance(old, type(self)) and isinstance(old, NonLeaf_Node):
            if self._supplied_proofs is None:
                self._supplied_proofs = {}
            for gn in old.sub_nodes:
                if isinstance(gn, GoalNode) and gn.sub_nodes:
                    self._supplied_proofs[f"{PREFIX_OLD}{gn.local_step}"] = (
                        None, [self._node_to_parsed_opr(n) for n in gn.sub_nodes])
            if not self._supplied_proofs:
                self._supplied_proofs = None
            # The old case GoalNode objects leave the tree (only their proof
            # *bodies* are salvaged into `_supplied_proofs`, as parsed oprs). Close
            # any sub-agent parked inside them before they go, or it orphans. This
            # branch warns nowhere, so it is the only teardown for these nodes.
            for d in old.sub_nodes:
                await d.aclose_all_subagents()
            old.sub_nodes.clear()
        elif isinstance(old, NonLeaf_Node) and old.sub_nodes:
            self._warn_discarded_nodes(
                list(old.sub_nodes),
                Warning.Position.HEADER,
            )
            for d in old.sub_nodes:
                await d.aclose_all_subagents()
            old.sub_nodes.clear()

    @classmethod
    def gen_single(cls, arg: Any, path: str = "<direct>") -> Parsed_Opr:
        """Break the `StdBlock.gen_single` chain.  SubgoalMakers inherit
        from `StdBlock` for runtime utilities but don't carry a `proof`
        field on their ToolArg — Define inherits this default factory
        directly; InferenceRule / Intro / Branch / CaseSplit / Induction
        override with their own nested-proof parsing.  Without this
        override, SubgoalMaker subclasses would pick up
        `StdBlock.gen_single`'s `cls(cfg, arg, parsed_proof)` factory
        which doesn't match their `__init__` signatures."""
        return Parsed_Opr(cls=cls, factory=lambda cfg: cls(cfg, arg), raw=arg)

    @abstractmethod
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason':
        ...
    def has_ending_opr(self) -> bool:
        # By default the operation (RULE/BRANCH/INDUCT/CASE_SPLIT/
        # INTRO) transforms the current top goal in place — no new
        # block is pushed onto the minilang stack, so no trailing
        # END is needed. Subclasses whose operation DOES push a new
        # block (e.g. Define's deferred termination path) override
        # this to return True and also override ending_opr to emit
        # the closing END.
        return False
    def ending_opr(self) -> Minilang_Operation | None:
        # Must match has_ending_opr's default above. `_refresh_footer`
        # uses `ending_opr()` (not `has_ending_opr()`) to decide
        # whether to run a closing opr, so both must agree.
        return None
    def _new_goal_node(self, goal_index: int, ml_state: Minilang_State) -> GoalNode:
        return GoalNode(NodeConfig(str(goal_index+self._initial_goal_index), ml_state, self), False, True, None)

    # --- Proof orchestration hooks -----------------------------------------
    # Subclasses override these to customize matching strategy and mismatch
    # handling.  The orchestration skeleton `_orchestrate_proofs` calls them
    # in order: _pre_match → _chk → _rematch loop → apply/splice.

    def _pre_match_proofs(self) -> None:
        """Match `_supplied_proofs` entries to GoalNodes by `local_step`.
        Pops consumed entries.  Default: exact key match.
        CaseSplit_Like adds a fuzzy suffix pass."""
        assert self._supplied_proofs is not None
        for gn in self.sub_nodes:
            if not isinstance(gn, GoalNode):
                continue
            key = gn.local_step
            if key is not None and key in self._supplied_proofs:
                gn.sub_nodes.clear()
                agent_cv, body = self._supplied_proofs.pop(key)
                if agent_cv is not None and gn.case_vars is None:
                    gn.case_vars = [(v, IsaTerm.from_agent("")) for v in agent_cv]
                gn._pending_proof = body

    async def _chk_subgoal_proofs(self) -> bool:
        """Whether (sub_nodes, supplied proofs) pairing is coherent.
        Default: count match.  CaseSplit_Like additionally checks that
        every GN has either a matching key or a `_pending_proof`."""
        s0 = self._state_after_beginning()
        expected = s0.new_subgoals_count or 0
        return expected == len(self.sub_nodes)

    async def _rematch(self,
        goal: 'Goal',
        case_id: str,
        candidates: 'list[case_name]',
    ) -> 'str | None':
        """Per-goal rematch.  Called once per unmatched goal with the
        remaining pickable candidates.  Returns the picked key, or None
        to drop.  Default: drop.  CaseSplit_Like fires MapCase."""
        return None

    def _splice_goal(self) -> 'tuple[str, Goal] | None':
        """Key + goal for the single goal in the N<=1 splice path.
        Returns None when there is no actionable goal.
        Default: `str(_initial_goal_index)` + leading_goal.
        CaseSplit_Like: reads `Consider_Case_Msg.case`."""
        s0 = self._state_after_beginning()
        g = s0.leading_goal
        if g is None:
            return None
        return (str(self._initial_goal_index), g)

    def _unconsumed_proof_warning(self) -> str | None:
        """Warning message for proofs remaining in `_supplied_proofs`
        after orchestration.  None = no warning.  Called from the
        generic `_refresh_footer`."""
        if not self._supplied_proofs:
            return None
        keys = ", ".join(f"`{n}`" for n in self._supplied_proofs)
        plural = len(self._supplied_proofs) > 1
        s = "s" if plural else ""
        verb = "were" if plural else "was"
        return (f"The supplied proof{s} for subgoal{s} {keys} "
                f"{verb} not used (no matching runtime subgoal).")

    async def _truncate_siblings_for_splice(self) -> None:
        parent = self.parent
        if parent is None:
            return
        idx = next(i for i, c in enumerate(parent.sub_nodes) if c is self)
        discarded = parent.sub_nodes[idx + 1:]
        del parent.sub_nodes[idx + 1:]
        if discarded:
            parent._warn_discarded_nodes(
                discarded,
                Warning.Position.FOOTER)
        # The truncated siblings leave the tree; close their sub-agents.
        for d in discarded:
            await d.aclose_all_subagents()

    async def _splice_body(self, body: 'proof', my_idx: int) -> None:
        """Insert each op in `body` as a parent-sibling right after self."""
        parent = self.parent
        if parent is None or not body:
            return
        # CAUTION: mutating `parent.sub_nodes` while parent's StdBlock
        # for-loop iterates it.  Python list iteration picks up items
        # inserted past the current index — LOAD-BEARING.
        if my_idx + 1 < len(parent.sub_nodes):
            before = parent.sub_nodes[my_idx + 1]
            await parent._insert_before_child(before, body)
        else:
            assert isinstance(parent, StdBlock)
            for parsed_op in body:
                local_step = parent._local_step_of_next_proof_step()
                ml_state = await parent._state_before_ending_.clone(None)
                config = NodeConfig(local_step, ml_state, parent)
                try:
                    new_node = parsed_op.factory(config)
                except ProofTreeTooDeep:
                    the_session()._depth_limit_exceeded = True
                    break
                parent.sub_nodes.append(new_node)

    def _cleanup_inherited_proofs(self) -> None:
        if self._supplied_proofs:
            for k in [k for k in self._supplied_proofs if k.startswith(PREFIX_OLD)]:
                del self._supplied_proofs[k]

    async def _orchestrate_proofs(self) -> None:
        """Generic skeleton: match supplied proofs to runtime GoalNodes,
        fire rematch for mismatches, splice for N<=1."""
        assert self._supplied_proofs is not None
        if self.sub_nodes:
            # --- N>=2 path (block opened, GoalNodes exist) ---
            self._pre_match_proofs()
            if await self._chk_subgoal_proofs():
                self._cleanup_inherited_proofs()
                return
            unmatched = [gn for gn in self.sub_nodes
                         if isinstance(gn, GoalNode) and gn._pending_proof is None]
            if not unmatched:
                self._cleanup_inherited_proofs()
                return
            candidates: list[case_name] = [
                k if k.startswith(PREFIX_OLD) else f"{PREFIX_NEW}{k}"
                for k in self._supplied_proofs
            ]
            remaining = list(candidates)
            for gn in unmatched:
                g = gn.goal()
                if g is None:
                    continue
                case_id = gn.local_step
                own_old = f"{PREFIX_OLD}{case_id}"
                options = [k for k in remaining
                           if not k.startswith(PREFIX_OLD) or k == own_old]
                if not options:
                    gn.sub_nodes.clear()
                    continue
                picked = await self._rematch(g, case_id, options)
                if picked is None:
                    gn.sub_nodes.clear()
                elif picked.startswith(PREFIX_OLD):
                    entry = self._supplied_proofs.pop(picked, None)
                    if entry is not None:
                        gn.sub_nodes.clear()
                        agent_cv, body = entry
                        if agent_cv is not None and gn.case_vars is None:
                            gn.case_vars = [(v, IsaTerm.from_agent("")) for v in agent_cv]
                        gn._pending_proof = body
                elif picked.startswith(PREFIX_NEW):
                    new_name = picked[len(PREFIX_NEW):]
                    entry = self._supplied_proofs.pop(new_name, None)
                    if entry is not None:
                        gn.sub_nodes.clear()
                        agent_cv, body = entry
                        if agent_cv is not None and gn.case_vars is None:
                            gn.case_vars = [(v, IsaTerm.from_agent("")) for v in agent_cv]
                        gn._pending_proof = body
                    if picked in remaining:
                        remaining.remove(picked)
            self._cleanup_inherited_proofs()
        else:
            # --- N<=1 splice path (no block opened, no GoalNodes) ---
            parent = self.parent
            if parent is None:
                return
            splice = self._splice_goal()
            if splice is None:
                return
            goal_key, goal = splice
            my_idx = next(i for i, c in enumerate(parent.sub_nodes) if c is self)
            # Exact match shortcut
            if goal_key in self._supplied_proofs:
                (_, body) = self._supplied_proofs.pop(goal_key)
                await self._truncate_siblings_for_splice()
                await self._splice_body(body, my_idx)
                self._cleanup_inherited_proofs()
                return
            candidates: list[case_name] = list(self._supplied_proofs.keys())
            if my_idx + 1 < len(parent.sub_nodes):
                candidates.append(CASE_EXISTING)
            picked = await self._rematch(goal, goal_key, candidates)
            if picked == CASE_EXISTING:
                self._cleanup_inherited_proofs()
                return
            if picked is None:
                await self._truncate_siblings_for_splice()
                self._cleanup_inherited_proofs()
                return
            entry = self._supplied_proofs.pop(picked, None)
            if entry is not None:
                await self._truncate_siblings_for_splice()
                await self._splice_body(entry[1], my_idx)
            self._cleanup_inherited_proofs()

    async def _refresh_footer(self) -> 'FailureReason | None':
        fail = await super()._refresh_footer()
        msg = self._unconsumed_proof_warning()
        if msg:
            self.warnings.append(Warning(Warning.Position.FOOTER, msg))
        return fail

    def _on_regenerating_goals(self, count: int) -> None:
        pass
    def _should_open_proof_block(self, s0: Minilang_State) -> _OpenSubgoalBlock:
        """Decide whether this refresh opens a subgoal block, and if so
        whether the enclosing parent block is also closed via `_close_by`.

        Default (Intro/InferenceRule/Branch/CaseSplit/Induction): open a
        block iff the ML side reported that this operation opened more
        than one new subgoal (via the `Goals` reporter message, surfaced
        as `Minilang_State.new_subgoals_count`).  If so, also close the
        parent proof line (subgoals become its tail, siblings after this
        node become meaningless).

        `None` (operation emitted no `Goals`) is treated as "don't open a
        block" — applies to state-clone paths and operations that don't
        alter the goal stack structure.

        `Define` overrides this to base the decision on reporter messages
        indicating whether the deferred pat-completeness / termination
        block has been pushed onto the minilang stack; when it opens,
        it does NOT close the parent line (its block is internal and
        bracketed by an END opcode)."""
        n = s0.new_subgoals_count
        if n is not None and n > 1:
            return _OpenSubgoalBlock.YES_AND_CLOSE_PARENT_BLOCK
        return _OpenSubgoalBlock.NO
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        is_init = self._first_time
        old_n_subnodes = len(self.sub_nodes)
        fail = await super()._refresh_the_beginning_opr()
        if fail is not None:
            return fail
        s0 = self._state_after_beginning()
        if not s0.initialized():
            raise InternalError("The state after beginning is not initialized, meaning the node is not refreshed")
        decision = self._should_open_proof_block(s0)
        if decision != _OpenSubgoalBlock.NO:
            goals_count = s0.new_subgoals_count or 0
            # Latch the parent-closing decision on BOTH the reuse and regenerate
            # paths — this assignment MUST stay ABOVE the if/else: `opening()`
            # derives my parent's closed-ness from these fields, so the reuse
            # `pass` path must set them too, or a re-refresh (e.g. uncomment)
            # would wrongly leave the parent open. (canary: CaseSplit_AmendReconcile_ExactMatch)
            self._opened_closing_block = (decision == _OpenSubgoalBlock.YES_AND_CLOSE_PARENT_BLOCK)
            self._opened_count = goals_count if self._opened_closing_block else 0
            # TODO: try to reuse the existing subnodes instead of discarding them.
            if not self._first_time and goals_count == len(self.sub_nodes):
                pass
            else:
                self._on_regenerating_goals(goals_count)
                if (decision == _OpenSubgoalBlock.YES_AND_CLOSE_PARENT_BLOCK
                        and self.parent is not None):
                    await self.parent._truncate_siblings_after(self)
                if self.sub_nodes:
                    self._warn_discarded_nodes(
                        list(self.sub_nodes),
                        Warning.Position.FOOTER)
                    # The old subgoal nodes are being regenerated and leave the
                    # tree; close their sub-agents before dropping them.
                    for d in list(self.sub_nodes):
                        await d.aclose_all_subagents()
                self.sub_nodes = []
                ml_state = await s0.clone(None)
                for i in range(goals_count):
                    try:
                        new_node = self._new_goal_node(i, ml_state)
                    except ProofTreeTooDeep:
                        the_session()._depth_limit_exceeded = True
                        return FailureReason("Proof tree depth exceeds the limit")
                    self.sub_nodes.append(new_node)
                    if i < goals_count - 1:
                        ml_state = await ml_state.sorry_next(None, None)
        else:
            self._opened_closing_block = False
            self._opened_count = 0
            if self.sub_nodes:
                self._warn_discarded_nodes(
                    list(self.sub_nodes),
                    Warning.Position.FOOTER)
                # This refresh opens no block; the old subgoal nodes leave the
                # tree — close their sub-agents before dropping them.
                for d in list(self.sub_nodes):
                    await d.aclose_all_subagents()
                self.sub_nodes = []
            # opening() is derived from the live tail, so a no-block refresh
            # needs no explicit parent re-open: clearing _opened_closing_block
            # (above) makes my parent read open automatically.
        if not is_init and len(self.sub_nodes) != old_n_subnodes:
            self.changed = True
        if self._supplied_proofs:
            await self._orchestrate_proofs()
        return None
    def _id_of_openning_prf_to_fill(self) -> step | None:
        return None
    def opening(self) -> bool:
        # LOAD-BEARING override (do NOT remove): a SubgoalMaker must never
        # self-flag and must stay non-appendable, so the derived NonLeaf
        # opening() must NOT apply to it. Whether it closes its PARENT is a
        # separate question answered by `_closes_my_parent`.
        return False
    def _closes_my_parent(self) -> bool:
        # I close my parent's proof line iff I successfully opened a
        # parent-closing block AND still hold every case I opened. A
        # COMMENTED/CANCELLED/FAILED closer (status != SUCCESS) closes nothing,
        # so the parent re-opens and its leftover goal is flagged (DEFECT 1). A
        # deleted case makes live < _opened_count → not closing (DEFECT 2).
        if self.status.status != EvaluationStatus.Status.SUCCESS:
            return False
        if not self._opened_closing_block:
            return False
        live = sum(1 for c in self.sub_nodes if isinstance(c, GoalNode))
        return self._opened_count > 0 and live == self._opened_count


class CaseSplit_Like(SubgoalMaker):
    # Subclass-specific "kind" label — overridden on CaseSplit / Induction.
    # Used by `_rematch` when building `Interaction_MapCase`.  Named
    # `_case_kind` (not `_kind`) to avoid shadowing Node's instance-level
    # `_kind` attribute set in Node.__init__.
    _case_kind: ClassVar[Literal["case-split", "induction"]]

    case_vars: list[Var] | None
    case_tvars: list[tuple[varname, typ]] | None
    case_hyps: list[Hyp] | None
    case_name: str | None
    # Rule resolution cache. `_resolved_rule_str = None` means "no explicit
    # rule" (auto-pick on the ML side). Set once on the first refresh and
    # reused afterwards — re-amending the node is expected to replace the
    # whole instance, so no invalidation hook is needed.
    _resolved_rule_str: IsaTerm | None
    _rule_resolved: bool
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.case_vars = None
        self.case_tvars = None
        self.case_hyps = None
        self._resolved_rule_str = None
        self._rule_resolved = False
        # quickview dedup: remember what case_vars / case_hyps we last
        # printed so we don't repeat them on every re-render unless
        # they actually changed (mirrors Intro's `_prev_bindings`).
        self._prev_case_printed: tuple[list[Var] | None, list[tuple[varname, typ]] | None, list[Hyp] | None] | None = None

    @classmethod
    def gen_single(cls, arg: Any, path: str = "<direct>") -> Parsed_Opr:
        """Default for CaseSplit / Induction: parse per-case `proofs`
        into `dict[case_name, proof]` and hand to the ctor.  Both
        subclasses take the same `__init__` signature
        `(config, arg, proofs_by_case)`, so one implementation covers
        both.

        Rejects non-list `proofs`, bad entries, non-string `case_name`,
        non-list `body`, and duplicate `case_name`s — all with
        path-annotated errors."""
        raw = arg.get("proofs")
        if raw == "GivenLater":
            raw = None
        proofs_by_case: 'dict[str, proof_with_case_vars] | None' = None
        if raw is not None and raw != []:
            if not isinstance(raw, list):
                raise ArgumentError({},
                    f"{path}.proofs: expected an array, got {type(raw).__name__}")
            proofs_by_case = {}
            for pi, entry in enumerate(raw):
                entry_path = f"{path}.proofs[{pi}]"
                if not isinstance(entry, dict):
                    raise ArgumentError({},
                        f"{entry_path}: expected an object with `case_name` "
                        f"and `body`, got {type(entry).__name__}")
                missing = [k for k in ("case_name", "body") if k not in entry]
                if missing:
                    raise ArgumentError_MissingRequiredKeys(entry, entry_path, missing)
                cn = entry["case_name"]
                if not isinstance(cn, str):
                    raise ArgumentError(entry,
                        f"{entry_path}.case_name: expected string, got "
                        f"{type(cn).__name__}")
                if cn == CASE_EXISTING or cn.startswith((PREFIX_NEW, PREFIX_OLD)):
                    raise ArgumentError(entry,
                        f"{entry_path}.case_name: `{cn}` is a reserved name "
                        f"(`{CASE_EXISTING}`, or any name starting with "
                        f"`{PREFIX_NEW}` or `{PREFIX_OLD}` is reserved by the "
                        f"rematch mechanism). Choose a different case_name.")
                if cn in proofs_by_case:
                    raise ArgumentError(entry,
                        f"{entry_path}.case_name: duplicate case_name `{cn}` "
                        f"— each case may appear at most once in `proofs`")
                body = entry["body"]
                if not isinstance(body, list):
                    raise ArgumentError(entry,
                        f"{entry_path}.body: expected an array of proof "
                        f"operations, got {type(body).__name__}")
                cv_names: list[name] | None = None
                cv = entry.get("case_variables")
                if cv is not None:
                    if not isinstance(cv, list) or not all(isinstance(v, str) for v in cv):
                        raise ArgumentError(entry,
                            f"{entry_path}.case_variables: expected string array")
                    cv_names = [IsaTerm.from_agent(v) for v in cv]
                proofs_by_case[cn] = (cv_names, Parse_Op_List(body, f"{entry_path}.body"))
        pbc = proofs_by_case
        return Parsed_Opr(
            cls=cls,
            factory=lambda cfg: cast(Any, cls)(cfg, arg, pbc),
            raw=arg)

    async def _resolve_rule(self,
                            rule_spec: 'Literal["default"] | FactByName | FactByDescription',
                            target: xterm,
                            arbitrary: list[xvarname],
                            kind: Literal["induction", "case-split"],
                           ) -> 'FailureReason | None':
        """Resolve `rule_spec` to a concrete Isabelle rule source string
        (possibly with a `[xwhere ?v = t]` attribute clause) and cache it
        in `self._resolved_rule_str`.

        Three stages:
          1. Map `rule_spec` → `rule_name: str | None`. `FactByDescription`
             forks an `Interaction_RetrieveForProof` (single_choice).
          2. Call the `IsaMini.analyze_induct` / `analyze_case_split`
             callback to discover any schematic variables appearing in
             the rule's consume premises.
          3. If schematic vars are present, fork an
             `Interaction_InstantiateSchematics` to collect instantiations,
             then assemble `rule_name[xwhere ?v1 = t1, ...]`.

        Returns None on success (result in `self._resolved_rule_str`),
        or a `FailureReason` if resolution failed (e.g. no matching rule,
        prove-in-time answer for a rule query, callback error)."""
        # 1. rule_spec → rule_name
        if rule_spec == "default":
            rule_name: str | None = None
        elif "name" in rule_spec:
            rule_name = rule_spec["name"]
        elif "english" in rule_spec:
            desc = rule_spec["english"]
            entity_kind = (EntityKind.INDUCTION_RULE if kind == "induction"
                           else EntityKind.CASE_SPLIT_RULE)
            retrieve = Interaction_RetrieveForProof(
                self.ml_state, desc, [entity_kind], single_choice=True)
            results = await the_session().launch_interaction(retrieve)
            if not results:
                return FailureReason(f"No rule matching `{desc}` was found.")
            r = results[0]
            if isinstance(r, IsabelleFact_Unfound):
                return FailureReason(f"No rule matching `{desc}` was found.")
            if isinstance(r, IsabelleFact_ProveInTime):
                return FailureReason(
                    f"Rule retrieval for {kind} does not support prove-in-time; "
                    "specify a named rule.")
            rule_name = r.full_name  # IsabelleEntity or IsabelleFact_Presented
        else:
            raise InternalError(f"Unexpected rule spec: {rule_spec}")
        # 2. analyze rule for schematic vars
        callback_name = ("IsaMini.analyze_induct" if kind == "induction"
                         else "IsaMini.analyze_case_split")
        state_id = self.ml_state.name
        target_ascii = ascii_of_unicode(target)
        arbitrary_ascii = [ascii_of_unicode(a) for a in arbitrary]
        callback_args: Any = (
            (state_id, target_ascii, [], arbitrary_ascii, rule_name)
            if kind == "induction"
            else (state_id, target_ascii, [], rule_name))
        try:
            dvars, candidates, analysis = await self.ml_state.connection.callback(
                callback_name, callback_args)
        except IsabelleError as err:
            return FailureReason(
                f"Pre-flight analysis of {kind} rule failed: "
                f"{''.join(err.errors)}")
        # Offer in-scope facts mentioning the relevant vars (`dvars` = induction
        # target frees ∪ generalized) for the agent to carry into the IH
        # (induction only; no-op for case-split, where `candidates` is empty).
        # Done BEFORE the rule-analysis check because `analysis` is None for
        # default inductions that don't pick a named rule — the common case —
        # yet the IH-fact offer must still fire. Runs once per object under this
        # `_rule_resolved` gate; amend rebuilds the node and re-prompts.
        await self._choose_ih_facts(candidates, dvars)
        # 3. instantiate schematic vars if any
        if analysis is not None:
            picked_name, _, consume_prems, _, schematic_vars = analysis
            # Decode agent-facing display strings at the boundary: the consume
            # premises and the schematic-var TYPES (the var names are data used
            # for validation, so left as-is).
            consume_prems = [pretty_unicode(p) for p in consume_prems]
            schematic_vars = [(n, pretty_unicode(t)) for n, t in schematic_vars]
            if schematic_vars:
                final_name = rule_name if rule_name is not None else picked_name
                if final_name is None:
                    return FailureReason(
                        f"The {kind} rule has schematic variables, but "
                        "Isabelle did not auto-pick a named rule. Specify "
                        "a rule explicitly.")
                instantiate = Interaction_InstantiateSchematics(
                    state=self.ml_state,
                    rule_name=IsaTerm.from_isabelle(final_name),
                    consume_premises=consume_prems,
                    schematic_vars=schematic_vars,
                    kind=kind)
                self._resolved_rule_str = \
                    await the_session().launch_interaction(instantiate)
                self._rule_resolved = True
                return None
        self._resolved_rule_str = (IsaTerm.from_isabelle(rule_name)
                                   if rule_name is not None else None)
        self._rule_resolved = True
        return None
    async def _choose_ih_facts(self, candidates: list[tuple[str, str]],
                               dvars: list[str]) -> None:
        """Hook called from `_resolve_rule` to let the agent pick which facts
        to carry into the induction hypothesis. No-op by default (case-split
        has no IH); overridden by `Induction`."""
        return None
    def _case_vars_of_child(self, child_ind: int) -> list[varname_spec] | None:
        if self.sub_nodes:
            node = self.sub_nodes[child_ind]
            if not isinstance(node, GoalNode):
                raise InternalError("The child of a CaseSplit_Like is not a GoalNode")
            return [v[0] for v in node.case_vars] if node.case_vars is not None else None
        else:
            if child_ind == 0:
                return [v[0] for v in self.case_vars] if self.case_vars is not None else None
            else:
                raise InternalError("The child index is out of range")
    def _new_goal_node(self, goal_index: int, ml_state: Minilang_State) -> GoalNode:
        # Read the GN's own `Consider_Case_Msg` and pass case_name directly
        # as the `local_step` of NodeConfig (codebase convention for
        # GoalNode children of a CaseSplit_Like).  Wiring it at construction
        # time makes it available to the orchestration in
        # `_refresh_the_beginning_opr` BEFORE the children for-loop runs.
        # `case_vars / case_hyps` on the GN are left for its own refresh
        # to set (display-compat; follow-up cleanup).
        msgs = [m for m in ml_state.messages if isinstance(m, Consider_Case_Msg)]
        if len(msgs) == 1:
            local_step: str = msgs[0].case
        elif len(msgs) == 0:
            local_step = str(goal_index + self._initial_goal_index)
        else:
            raise InternalError(
                f"Expected at most one Consider_Case_Msg in ml_state.messages "
                f"for GoalNode creation, got {len(msgs)}")
        return GoalNode(NodeConfig(local_step, ml_state, self), False, True)
    def _rename_var(self, old_name: varname, new_name: varname) -> 'Node | None':
        if self.sub_nodes:
            return super()._rename_var(old_name, new_name)
        else:
            if self.case_vars is not None:
                for i, v in enumerate(self.case_vars):
                    if v[0] == old_name:
                        self.case_vars[i] = (new_name, v[1])
                        return self
            return None
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if not self.sub_nodes:
            return (None, indent)
        return ('cases', indent+1)
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False) -> None:
        # Only the single-subgoal path ever populates `case_vars` /
        # `case_hyps` on `self` (multi-subgoal has them on each child
        # GoalNode). Guard defensively so a stale leftover would not
        # accidentally double-print with the child GoalNodes'
        # _print_header rendering.
        if self.sub_nodes:
            return
        if self.case_vars is not None:
            print_vars(self.case_vars, indent, file, {}, "fixing variables")
        if self.case_tvars is not None:
            print_type_vars(self.case_tvars, indent, file, {}, "type variables")
        if self.case_hyps is not None:
            print_hyps(self.case_hyps, indent, file, {}, "assuming premises")
    def quickview(self, indent: int, file: MyIO) -> int:
        # Single-subgoal path: this node owns the case's fresh
        # bindings (no child GoalNode was created). Announce them in
        # quickview mirroring the full-print `_print_header`. Use
        # `_prev_case_printed` to avoid re-emitting the section on
        # every re-render (mirrors Intro's `_prev_bindings` dedup).
        indent = super().quickview(indent, file)
        if not self.sub_nodes and (self.case_vars or self.case_hyps):
            current = (self.case_vars, self.case_tvars, self.case_hyps)
            if current != self._prev_case_printed:
                if self.case_vars:
                    print_vars(self.case_vars, indent, file, {}, "fixing variables")
                if self.case_tvars:
                    print_type_vars(self.case_tvars, indent, file, {}, "type variables")
                if self.case_hyps:
                    print_hyps(self.case_hyps, indent, file, {}, "assuming premises")
                self._prev_case_printed = current
        return indent
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        # Single-case path: this node owns `case_vars`. Expose them so
        # subsequent siblings' `_ctxt_before_me()` (via the parent's
        # walk over `_fixed_vars_after_me`) and the pending-goal
        # suppression see them as already-introduced. For multi-case
        # the per-child GoalNode propagates its own context instead.
        if not self.sub_nodes and self.case_vars:
            for name, ty in self.case_vars:
                ret[name] = ty
        return ret
    def _fixed_tvars_at_me(self, ret: TVars) -> TVars:
        if not self.sub_nodes and self.case_tvars:
            for name, sort in self.case_tvars:
                ret[name] = sort
        return ret
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        if not self.sub_nodes and self.case_hyps:
            for name, prop in self.case_hyps:
                ret[name] = prop
        return ret
    def _fixed_vars_after_me(self, ret: Vars) -> Vars:
        return self._fixed_vars_at_me(ret)
    def _fixed_tvars_after_me(self, ret: TVars) -> TVars:
        return self._fixed_tvars_at_me(ret)
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return self._fixed_facts_at_me(ret)
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        is_init = self._first_time
        old_case = (self.case_vars, self.case_tvars, self.case_hyps)
        fail = await super()._refresh_the_beginning_opr()
        if fail is not None:
            return fail
        if (self.sub_nodes
                and isinstance(self.sub_nodes[0], GoalNode)
                and self.sub_nodes[0].case_vars is not None):
            opr = self.beginning_opr()
            if isinstance(opr, Minilang_Operation):
                try:
                    await self._execute_opr(self.ml_state, opr, self._state_after_beginning())
                    await self._state_after_beginning().clone(self.sub_nodes[0].ml_state)
                except IsabelleError:
                    pass
        if not self.sub_nodes:
            s = self._state_after_beginning()
            msgs = [m for m in s.messages if isinstance(m, Consider_Case_Msg)]
            match msgs:
                case []:
                    pass
                case [m0]:
                    self.case_name = m0.case
                    self.case_vars = m0.vars
                    self.case_tvars = m0.tvars
                    self.case_hyps = m0.hyps
                case _:
                    raise InternalError(
                        f"Expected at most one Consider_Case_Msg in Case's "
                        f"messages, got {len(msgs)}")
        if not is_init and (self.case_vars, self.case_tvars, self.case_hyps) != old_case:
            self.changed = True
        return None

    # --- CaseSplit_Like overrides of SubgoalMaker proof hooks ---------------

    def _pre_match_proofs(self) -> None:
        super()._pre_match_proofs()
        assert self._supplied_proofs is not None
        for gn in self.sub_nodes:
            if not isinstance(gn, GoalNode):
                continue
            if gn._pending_proof is not None:
                continue
            # Fuzzy pass: handle Isabelle's case-name disambiguation suffix
            # (e.g. nested induction renames inner `Suc` to `Suc1`).
            case_name = gn.local_step
            stripped = case_name.rstrip("0123456789")
            if stripped == case_name or not stripped:
                continue
            if stripped in self._supplied_proofs:
                gn.sub_nodes.clear()
                agent_cv, body = self._supplied_proofs.pop(stripped)
                if agent_cv is not None and gn.case_vars is None:
                    gn.case_vars = [(v, IsaTerm.from_agent("")) for v in agent_cv]
                gn._pending_proof = body

    async def _chk_subgoal_proofs(self) -> bool:
        if not await super()._chk_subgoal_proofs():
            return False
        if self._supplied_proofs is None:
            return True
        for gn in self.sub_nodes:
            if not isinstance(gn, GoalNode):
                continue
            case_name = gn.local_step
            if case_name in self._supplied_proofs:
                continue
            if gn._pending_proof is not None:
                continue
            return False
        return True

    async def _rematch(self, goal: 'Goal', case_id: str,
                       candidates: 'list[case_name]') -> 'str | None':
        options = [k for k in candidates
                   if not k.startswith(PREFIX_OLD) or k == f"{PREFIX_OLD}{case_id}"]
        if not options:
            return None
        interaction = Interaction_MapCase(
            actual_case=case_id,
            supplied_options=options,
            kind=self._case_kind,
            goal=goal,
            ctxt_before=self._ctxt_before_me())
        return await the_session().launch_interaction(interaction)

    def _splice_goal(self) -> 'tuple[str, Goal] | None':
        s0 = self._state_after_beginning()
        g = s0.leading_goal
        msgs = [m for m in s0.messages if isinstance(m, Consider_Case_Msg)]
        if msgs:
            return (msgs[0].case, g) if g is not None else None
        if g is None:
            return None
        return ("<transformed goal>", g)

    def _unconsumed_proof_warning(self) -> str | None:
        if not self._supplied_proofs:
            return None
        cases_list = ", ".join(f"`{n}`" for n in self._supplied_proofs)
        kind = "induction" if isinstance(self, Induction) else "case-split"
        plural = len(self._supplied_proofs) > 1
        s = "s" if plural else ""
        verb = "are" if plural else "is"
        return (f"The case{s} {cases_list} {verb} not found in the "
                f"resulting cases of the {kind} and {verb} thus dropped.")

    def _on_regenerating_goals(self, count: int) -> None:
        self.case_name = None
        self.case_vars = None
        self.case_hyps = None
    

### Operation registry for tool calls

class OperationMeta(NamedTuple):
    toolarg_typed_dict: type[Any]
    cls: type[Any]  # the Node subclass — `.gen(arg, container, index, path)` dispatches here

OPERATION_REGISTRY: dict[str, OperationMeta] = {}
OPERATION_REGISTRY_BY_CLS: 'dict[type[Node], str]' = {}

def proof_operation(operation: str, toolarg_typed_dict: type[Any]):
    """Class decorator to register a Node subclass as a proof operation.

    The class must define a classmethod
    `gen(cls, arg, remaining, path) -> LinkedList[Parsed_Opr]` following the
    base `Node.gen` contract: validate the ToolArg, parse any nested
    proof fields via `Parse_Op_List`, call `super().gen(arg, remaining,
    path)` to obtain the parsed tail (linked list of gen_nodes), and
    return `Cons(my_gn, tail)` where `my_gn = Parsed_Opr(cls=..., factory=
    ..., raw=arg)`.  Classes that forbid a successor (e.g. `Obvious`)
    check `remaining is not None` themselves and raise.
    """
    def decorator(cls: type[Any]):
        OPERATION_REGISTRY[operation] = OperationMeta(toolarg_typed_dict, cls)
        OPERATION_REGISTRY_BY_CLS[cls] = operation
        return cls
    return decorator

class PremiseBinding(TypedDict):
    name: str
    term: xterm

class LongStatement(TypedDict):
    english: str
    for_any: NotRequired[list[Explicit_Var]]
    premises: NotRequired[list[PremiseBinding]]
    conclusion: xterm

# Characters that can never occur at top level of a fact reference — neither
# in a (possibly qualified) fact name, nor in a `(i)`/`(i-j)` selector, nor
# between `[...]` attribute groups.  Their presence proves the string is a
# proposition pasted where a fact NAME belongs.  Deliberately NOT listed:
# `.` `'` `_` (legal in names), `,` `-` (legal in selectors), `(` `)` `[` `]`
# `‹` `›` (handled structurally below).
_FACT_REF_BANNED_CHARS = frozenset(
    '\\"?=<>+*/|&%@!;:~^'
    '∀∃λ⟶⟹⟷↔→⇒↦∧∨¬≤≥≠∈∉⊆⊂⊇⊃∪∩⋀⋁⋂⋃≡−×÷±√∑∏')

def _fact_ref_is_proposition(s: str) -> bool:
    """High-precision test that `s` is a proposition pasted where a fact
    reference belongs.  Only top-level characters are inspected — content
    inside `‹...›` cartouches (literal facts, `where`-values), `[...]`
    attribute groups, and `(...)` selectors is legitimately arbitrary, so
    whitespace or a banned character there proves nothing.  Anything not
    clearly propositional (including empty or ill-nested strings) returns
    False and flows through to the ML-side fact parser unchanged: a false
    positive here would block a legal reference, a false negative merely
    costs one ML round-trip."""
    cart = brack = paren = 0
    for ch in s:
        if ch == '\N{SINGLE LEFT-POINTING ANGLE QUOTATION MARK}':
            cart += 1
        elif ch == '\N{SINGLE RIGHT-POINTING ANGLE QUOTATION MARK}':
            if cart == 0:
                return False
            cart -= 1
        elif cart > 0:
            continue
        elif ch == '[':
            brack += 1
        elif ch == ']':
            if brack == 0:
                return False
            brack -= 1
        elif brack > 0:
            continue
        elif ch == '(':
            paren += 1
        elif ch == ')':
            if paren == 0:
                return False
            paren -= 1
        elif paren == 0 and (ch.isspace() or ch in _FACT_REF_BANNED_CHARS):
            return True
    return False

@validator(FactByName)
def _validate_fact_by_name(data: Any, path: str) -> FactByName:
    was_bare_str = isinstance(data, str)
    if was_bare_str:
        data = {"name": data}
    data = _validate_typed_dict(FactByName, data, path)
    name = data.get("name")
    if isinstance(name, str) and _fact_ref_is_proposition(name):
        loc = path if was_bare_str else f"{path}.name"
        field = path.rsplit(".", 1)[-1]
        if field.startswith("discharg"):  # discharge / discharging_facts
            raise ArgumentError({},
                f'{loc}: "{name}" is a proposition, not a fact reference. '
                f'Each discharge entry must NAME an existing fact (a premise, '
                f'a proved step, or a library lemma), optionally with '
                f'[where ...]. To discharge a premise you have not proved '
                f'yet: state it first as a Have step and reference its name, '
                f'or pass null to leave that premise position open.')
        elif field.startswith("facts") or field.startswith("using"):
            # contexts whose schema offers FactByProposition as an alternative
            raise ArgumentError({},
                f'{loc}: "{name}" is a proposition, not a fact name. '
                f'Use {{"proposition": "..."}} instead to cite a proposition, '
                f'or NAME an existing fact (a premise, a proved step, or a '
                f'library lemma).')
        else:  # e.g. `rule`, `IH_facts` — no proposition alternative exists
            raise ArgumentError({},
                f'{loc}: "{name}" is a proposition, not a fact name. '
                f'NAME an existing fact (a premise, a proved step, or a '
                f'library lemma).')
    return data

@validator(LongStatement)
def _validate_long_statement(data: Any, path: str) -> LongStatement:
    if isinstance(data, str):
        data = {"english": "", "conclusion": data}
    if not isinstance(data, dict):
        raise ArgumentError({}, f"{path}: expected an object or string, got {type(data).__name__}")
    if "conclusion" not in data and "isabelle" in data:
        data["conclusion"] = data.pop("isabelle")
    return _validate_typed_dict(LongStatement, data, path)

Statement = LongStatement

class ShortStatement(TypedDict):
    english: str
    isabelle: xterm

@validator(ShortStatement)
def _validate_short_statement(data: Any, path: str) -> ShortStatement:
    if isinstance(data, str):
        data = {"english": "", "isabelle": data}
    if not isinstance(data, dict):
        raise ArgumentError({}, f"{path}: expected an object or string, got {type(data).__name__}")
    if "conclusion" in data and "isabelle" not in data:
        data["_long_form"] = True
        data["_for_any"] = data.pop("for_any", [])
        data["_premises"] = data.pop("premises", [])
        data["isabelle"] = data.pop("conclusion")
        data.setdefault("english", "")
    elif "isabelle" not in data and "conclusion" in data:
        data["isabelle"] = data.pop("conclusion")
    return _validate_typed_dict(ShortStatement, data, path)

NamedStatement = ShortStatement

class ConstraintBinding(TypedDict):
    name: xname
    statement: ShortStatement

@validator(ConstraintBinding)
def _validate_constraint_binding(data: Any, path: str) -> ConstraintBinding:
    if not isinstance(data, dict):
        raise ArgumentError({}, f"{path}: expected an object, got {type(data).__name__}")
    if "statement" not in data and "isabelle" in data:
        name = data.pop("name", None)
        stmt = {"english": data.pop("english", ""), "isabelle": data.pop("isabelle")}
        if name is None and "name" in stmt:
            name = stmt.pop("name")
        data["statement"] = stmt
        if name is not None:
            data["name"] = name
    return _validate_typed_dict(ConstraintBinding, data, path)

class SuggestedLemma(TypedDict):
    """One item of the `request` tool's `general_lemmas` list (a worker→dispatcher
    channel). `statement` reuses the `LongStatement` block
    (`{english, conclusion, for_any?, premises?}`) shared with `Have`/`edit`, so
    a worker can declare the lemma's universally-quantified variables (`for_any`)
    and premises — exactly the structure the auto-prove-general path needs to
    judge whether the lemma is general (every free variable declared in
    `for_any`, no schematic variable)."""
    name: str
    statement: LongStatement

@validator(SuggestedLemma)
def _validate_suggested_lemma(data: Any, path: str) -> SuggestedLemma:
    # `_validate_typed_dict` checks dict-ness + required keys, and recurses into
    # `statement` via the registered `LongStatement` validator (string-coercion,
    # nested premise/for_any checks). Only `name` needs the explicit guard: the
    # framework's plain-`str` validation is a no-op, and `str()`-coercing a
    # non-string name would silently fabricate a bogus fact binding.
    data = _validate_typed_dict(SuggestedLemma, data, path)
    if not isinstance(data["name"], str):
        raise ArgumentError(
            {}, f"{path}.name: expected a string, got {type(data['name']).__name__}")
    return data

class RequestConstraint(TypedDict):
    """One item of the `request` tool's `constraints` list (a worker→dispatcher
    channel). A worker reports a condition its sub-goal genuinely needs but was
    not given when it was dispatched (the dispatcher under-provisioned the
    sub-goal). `proposition` is a loose Isabelle term sketch; the dispatcher
    adjudicates and RE-STATES it precisely (`Interaction_ReviewConstraint`) —
    accept → added as a premise of the delegated block, or reject."""
    description: str
    proposition: xterm

@validator(RequestConstraint)
def _validate_request_constraint(data: Any, path: str) -> RequestConstraint:
    # Mirrors `_validate_suggested_lemma`: `_validate_typed_dict` checks dict-ness
    # + required keys + coerces `proposition` (an `xterm`); guard `description`
    # explicitly so a non-string can't be silently `str()`-fabricated.
    data = _validate_typed_dict(RequestConstraint, data, path)
    if not isinstance(data["description"], str):
        raise ArgumentError(
            {}, f"{path}.description: expected a string, got {type(data['description']).__name__}")
    return data

def print_statement(self: LongStatement, indent: int, file: MyIO):
    print_indent(indent, file)
    file.write(f"- english: {self["english"]}\n")
    print_indent(indent, file)
    file.write(f"  conclusion: {self["conclusion"]}\n")

### Concrete Models

def _print_raw_fact(fact: 'Fact', indent: int, file: MyIO) -> None:
    """Print a raw, unresolved fact reference. Used as a fallback when
    fact_refs is None (refresh not yet run or cancelled)."""
    print_indent(indent, file)
    match fact_kind(fact):
        case "name":
            file.write(f"- name: {cast(FactByName, fact)['name']} (pending)\n")
        case "proposition":
            file.write(f"- proposition: {cast(FactByProposition, fact)['proposition']} (pending)\n")
        case "description":
            file.write(f"- description: {cast(FactByDescription, fact)['english']} (pending)\n")

def _filter_unfound(facts: list[IsabelleFact]) -> tuple[list[IsabelleFact], list[str]]:
    """Filter out IsabelleFact_Unfound from a list.
    Returns (kept_facts, warning_strings)."""
    kept: list[IsabelleFact] = []
    warnings: list[str] = []
    for f in facts:
        if isinstance(f, IsabelleFact_Unfound):
            warnings.append(f"Fact \"{f.name().unicode}\" not found, skipped.")
        else:
            kept.append(f)
    return kept, warnings

async def _filter_unprovable(
    facts: list[IsabelleFact], ml_state: 'Minilang_State'
) -> tuple[list[IsabelleFact], list[str]]:
    """Filter out IsabelleFact_ProveInTime that cannot be proven automatically.
    Returns (kept_facts, warning_strings)."""
    pit_indices: list[int] = []
    pit_statements: list[str] = []
    for i, f in enumerate(facts):
        if isinstance(f, IsabelleFact_ProveInTime):
            pit_indices.append(i)
            pit_statements.append(f.statement.ascii)
    if not pit_statements:
        return facts, []
    results = await ml_state.validate_prove_in_time(pit_statements)
    drop: set[int] = set()
    warnings: list[str] = []
    for idx, result in zip(pit_indices, results):
        if result is not None:
            error_lines = result.splitlines()
            error_summary = "\n".join(error_lines[:10])
            if len(error_lines) > 10:
                error_summary += "\n..."
            prefix = "\n" if warnings else ""
            warnings.append(
                f'{prefix}Ignored "{facts[idx].name().unicode}" \u2014 not a known Isabelle theorem nor trivially provable. '
                f'Prove it manually using Have if needed.\n'
                f'Reason: {error_summary}')
            drop.add(idx)
    kept = [f for i, f in enumerate(facts) if i not in drop]
    return kept, warnings

def _split_fetched(fetched: 'list[IsabelleFact | Interaction_RetrieveForProof]'
    ) -> 'tuple[list[IsabelleFact], list[Interaction], list[int]]':
    """Split fetch_facts results into resolved facts, interactions, and placeholder indices.
    IsabelleFact (including Unfound) goes to resolved; Interaction goes to interactions."""
    resolved: list[IsabelleFact] = []
    interactions: list[Interaction] = []
    resolve_indices: list[int] = []
    for item in fetched:
        if isinstance(item, IsabelleFact):
            resolved.append(item)
        else:
            resolve_indices.append(len(resolved))
            resolved.append(None)  # type: ignore — placeholder for interaction result
            interactions.append(item)
    return resolved, interactions, resolve_indices


def _fetched_to_facts(fetched: 'list[IsabelleFact | Interaction_RetrieveForProof]') -> list[IsabelleFact]:
    """Convert fetch_facts results to a pure IsabelleFact list for callers
    that don't support interactive resolution (Obvious, Chaining, Derive,
    Rewrite).  Interaction_RetrieveForProof entries become IsabelleFact_Unfound
    so that downstream _filter_unfound handles them uniformly."""
    out: list[IsabelleFact] = []
    for item in fetched:
        if isinstance(item, IsabelleFact):
            out.append(item)
        else:
            out.append(IsabelleFact_Unfound(
                cast(Fact, {"english": item.query})))
    return out


#### Obvious

# Depth (count of enclosing Have/Obtain/Suffices blocks) at or beyond which a
# FAILED Obvious is rendered with a hint to delegate the goal via the `subagent`
# tool. Formerly the deep-Obvious auto-sorry threshold; now used only by the hint.
_SUBAGENT_HINT_DEPTH = 2

# Maximum worker-nesting depth: main -> worker (sub-agent) is layer 1, its worker
# (sub-sub-agent) is layer 2, and so on. A session already at this depth may not
# dispatch a further sub-worker — so delegation bottoms out at this many layers.
# Enforced two ways: the dispatch tools are not even advertised to a session at
# this depth (Session._can_offer_dispatch_tools, gating _tool_schemas_for /
# _role_allowed_tools), and a runtime backstop guard in _subagent_tool_logic
# rejects a too-deep dispatch even if a model calls the unadvertised tool.
SUBAGENT_NESTING_DEPTH = 3

class Obvious_ToolArg(TypedDict):
    # Validation accepts FactByDescription too (the schema the LLM sees, in
    # tools/cc_edit.jsonc, still advertises only FactByName | FactByProposition):
    # an LLM may violate the schema with a description fact, which fetch_facts
    # turns into an Interaction_RetrieveForProof that the Obvious path filters
    # out with a warning rather than crashing. Rejecting it at validation time
    # would defeat that graceful handling (see test ObviousDescriptionFact).
    facts: list[FactByName | FactByProposition | FactByDescription]

@proof_operation("Obvious", Obvious_ToolArg)
class Obvious(Leaf):
    def __init__(self, config: NodeConfig, arg: Obvious_ToolArg):
        if config.parent is not None and config.parent._is_trivial is False:
            raise GoalIsNontrivial(config.parent)
        super().__init__(config, "")
        self._raw_facts: list[FactByName | FactByProposition | FactByDescription] = [
            f for f in arg["facts"] if f is not None]
        self.fact_refs: list[IsabelleFact] | None = None
        self._found_tactic: str | None = None
        self._eval_time_ms: int | None = None

    def _subtree_stats_live(self) -> 'tuple[int, int]':
        # A SUCCESS Obvious is a goal closed by the hammer — proved work.
        proved = 1 if self.status.status == EvaluationStatus.Status.SUCCESS else 0
        return (1, proved)

    @classmethod
    def gen(cls, arg: Obvious_ToolArg, remaining: 'LinkedList[_RawOp]',
            path: str) -> 'LinkedList[Parsed_Opr]':
        # Obvious concludes the proof — forbid any sibling after it in
        # the same list.  If remaining is None we delegate to super()
        # (base Node.gen → Cons(gen_single, parse empty tail) = one-cell
        # list) which gets the default self gn via `Node.gen_single`.
        if remaining is not None:
            raise ArgumentError(arg,
                f"{remaining.head.path}: The Obvious operation at {path} "
                f"concludes the proof, so no further proof operations "
                f"may follow it.")
        return super().gen(arg, remaining, path)

    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        print_indent(indent, file)
        file.write(f"operation: Obvious\n")
        if self.fact_refs is not None:
            if self.fact_refs:
                print_indent(indent, file)
                file.write(f"with facts:\n")
                for ref in self.fact_refs:
                    ref.print(indent+1, file)
        elif self._raw_facts:
            print_indent(indent, file)
            file.write(f"with facts:\n")
            for ref in self._raw_facts:
                _print_raw_fact(ref, indent+1, file)
        self._print_evaluation_status(indent, file)
        self._print_subagent_hint(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        self._print_subagent_hint(indent, file)
        return indent
    def _print_subagent_hint(self, indent: int, file: MyIO) -> None:
        """A deeply-nested (>= _SUBAGENT_HINT_DEPTH) Obvious that FAILED: point the
        main agent at the `subagent` tool to delegate this sub-goal, naming the
        enclosing goal block (`_nearest_goal_for_subagent`) that `subagent` should
        target. Shown to any agent that can dispatch (main or worker). Depth is
        measured RELATIVE to the dispatcher's focus scope (`proof_scope_root`: a
        worker's `target`, else the global root) — like step ids, this rebasing
        lives only here at the agent boundary; the tree keeps absolute levels.

        One-shot per node id per session (`shown_subagent_hints`): marked only on
        the consuming inline-Outline surface (`_consuming_subagent_hints`, set by
        `quickview_proof_scope`), NOT on the non-consuming `proof.yaml` render, so
        the authoring turn shows it on both surfaces and neither repeats it after
        (mirrors the `_emit_pending_hint_notices` consume discipline)."""
        if not (_rendering_for_dispatcher()
                and self.status.status == EvaluationStatus.Status.FAILURE):
            return
        sess = the_session()
        if self._subgoal_level - sess.proof_scope_root._subgoal_level < _SUBAGENT_HINT_DEPTH:
            return
        if self.id in sess.shown_subagent_hints:
            return
        target = self._nearest_goal_for_subagent()
        if target is None:
            return
        if sess._consuming_subagent_hints:
            sess.shown_subagent_hints.add(self.id)
        print_indent(indent, file)
        file.write(f"This goal is deep. Consider calling `subagent` with step {sess._display_id(target.id)}\n")
    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        if self.fact_refs is None:
            if self._raw_facts:
                fetched = _fetched_to_facts(await self.ml_state.fetch_facts(self._raw_facts))
                facts, unfound_warnings = _filter_unfound(fetched)
            else:
                facts = []
                unfound_warnings = []
            self.fact_refs, pit_warnings = await _filter_unprovable(facts, self.ml_state)
            for w in unfound_warnings + pit_warnings:
                self.warnings.append(Warning(Warning.Position.FOOTER, w))
        elif self.ml_state.initialized():
            refreshed = await self.ml_state.refresh_facts(self.fact_refs)
            self.fact_refs, unfound_warnings = _filter_unfound(refreshed)
            for w in unfound_warnings:
                self.warnings.append(Warning(Warning.Position.FOOTER, w))
        await super()._refresh_me_alone(auto_intro)
        if self.parent is not None:
            if self.status.status == EvaluationStatus.Status.SUCCESS:
                self.parent._is_trivial = True
                for m in self.resulting_state().messages:
                    if isinstance(m, SH_PRF_Msg):
                        self._found_tactic = m.method
                        self._eval_time_ms = m.time_ms
                        break
            elif self.status.status == EvaluationStatus.Status.FAILURE:
                self.parent._is_trivial = False
    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        # Always run a real sledgehammer — deep Obvious no longer degrades to
        # sorry. Failures surface immediately at edit time, and the main agent
        # delegates hard sub-goals on demand via the `subagent` tool.
        facts = self.fact_refs if self.fact_refs is not None else []
        return Minilang_Operation.HAMMER(facts, 30)
    def assemble(self, output: 'list[Minilang_Operation] | None' = None) -> 'list[Minilang_Operation]':
        if output is None:
            output = []
        if self.status.status == EvaluationStatus.Status.COMMENTED:
            return output
        facts = self.fact_refs if self.fact_refs is not None else []
        cached: tuple[str, int] | None = None
        if self._found_tactic and self._found_tactic != "" and self._eval_time_ms is not None:
            cached = (self._found_tactic, self._eval_time_ms)
        output.append(Minilang_Operation.HAMMER(facts, 30, cached))
        return output
    def _on_edit_failure(self, outcome: 'EditOutcome') -> 'tuple[EditFailureBehavior, EditOutcome]':
        if self.status.status == EvaluationStatus.Status.FAILURE:
            # Multi-op batches skip auto-revert so the agent sees
            # the failing node and can amend it.
            if len(outcome.request) > 1:
                return super()._on_edit_failure(outcome)
            # Store the blob ABSOLUTE; its `step …` refs and the carried node id
            # are projected to the caller's namespace at render time (the single
            # id-translation boundary, CannotEdit.render). Relativizing here too
            # would double-project a worker's ids.
            file = MyIO(StringIO())
            if self.status.reason:
                file.write(self.status.reason.reason)
            if self.warnings:
                self._print_warnings(0, file, list(Warning.Position))
            outcome.failure = CannotEdit_EvaluationFailed(
                FailureReason(file.getvalue()),
                self.id,
                operation=outcome.operation,
                unapplied_oprs=[],
                is_error=True)
            return (EditFailureBehavior.TERMINATE_AND_REVERT, outcome)
        return super()._on_edit_failure(outcome)

class Chaining_ToolArg(TypedDict):
    thought: str
    name: NotRequired[str]
    facts: list[FactByName | FactByProposition]

@proof_operation("Chaining", Chaining_ToolArg)
class Chaining(Leaf):
    def __init__(self, config: NodeConfig, arg: Chaining_ToolArg):
        super().__init__(config, "")
        explicit_name = arg.get("name")
        if explicit_name:
            self.chain_name: str = explicit_name
        else:
            session = the_session()
            session.fact_name_counter += 1
            self.chain_name = f"chain{session.fact_name_counter}"
        self._raw_facts: list[FactByName | FactByProposition] = [
            f for f in arg["facts"] if f is not None]
        self.fact_refs: list[IsabelleFact] | None = None
        self.result_facts: list[tuple[varname, term]] | None = None
        """(fact_name, pretty_expression) pairs for facts derived by CHAINING,
        populated from Specialize_Result_Msg after successful execution."""
        self._prev_result_facts: list[tuple[varname, term]] | None = None

    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.result_facts is not None and self.result_facts != self._prev_result_facts:
            print_indent(indent, file)
            file.write("resulting:\n")
            for name, expr in self.result_facts:
                print_indent(indent + 1, file)
                file.write(f"{name.unicode}: {expr.unicode}\n")
            self._prev_result_facts = self.result_facts
        return indent

    def print(self, indent: int, file: MyIO, update_line: bool = False,
              show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        print_indent(indent, file)
        file.write("operation: Chaining\n")
        if self.fact_refs is not None:
            if self.fact_refs:
                print_indent(indent, file)
                file.write("from:\n")
                for ref in self.fact_refs:
                    ref.print(indent + 1, file)
        elif self._raw_facts:
            print_indent(indent, file)
            file.write("from:\n")
            for ref in self._raw_facts:
                _print_raw_fact(ref, indent + 1, file)
        if self.result_facts is not None:
            print_indent(indent, file)
            file.write("resulting:\n")
            for name, expr in self.result_facts:
                print_indent(indent + 1, file)
                file.write(f"{name.unicode}: {expr.unicode}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file,
                [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        if self.fact_refs is None:
            if self._raw_facts:
                fetched = _fetched_to_facts(await self.ml_state.fetch_facts(self._raw_facts))
                facts, unfound_warnings = _filter_unfound(fetched)
                self.fact_refs, pit_warnings = await _filter_unprovable(facts, self.ml_state)
                for w in unfound_warnings + pit_warnings:
                    self.warnings.append(Warning(Warning.Position.FOOTER, w))
            else:
                self.fact_refs = []  # the_operation will report "requires at least one fact"
        elif self.ml_state.initialized():
            refreshed = await self.ml_state.refresh_facts(self.fact_refs)
            self.fact_refs, unfound_warnings = _filter_unfound(refreshed)
            for w in unfound_warnings:
                self.warnings.append(Warning(Warning.Position.FOOTER, w))
        await super()._refresh_me_alone(auto_intro)
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            messages = self.resulting_state().messages
            for m in messages:
                if isinstance(m, Specialize_Result_Msg):
                    self.result_facts = m.facts
                    break

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        if not self._raw_facts:
            return FailureReason("Chaining requires at least one fact")
        facts = self.fact_refs if self.fact_refs is not None else []
        unfound = [f for f in facts if isinstance(f, IsabelleFact_Unfound)]
        if unfound:
            return FailureReason("\n".join(f"Fact \"{f.name().unicode}\" not found" for f in unfound))
        return Minilang_Operation.CHAINING(self.chain_name, facts)

    def _on_edit_failure(self, outcome: 'EditOutcome') -> 'tuple[EditFailureBehavior, EditOutcome]':
        if self.status.status == EvaluationStatus.Status.FAILURE:
            # Multi-op batches skip auto-revert so the agent sees
            # the failing node and can amend it.
            if len(outcome.request) > 1:
                return super()._on_edit_failure(outcome)
            # Store the blob ABSOLUTE; its `step …` refs and the carried node id
            # are projected to the caller's namespace at render time (the single
            # id-translation boundary, CannotEdit.render). Relativizing here too
            # would double-project a worker's ids.
            file = MyIO(StringIO())
            if self.status.reason:
                file.write(self.status.reason.reason)
            if self.warnings:
                self._print_warnings(0, file, list(Warning.Position))
            outcome.failure = CannotEdit_EvaluationFailed(
                FailureReason(file.getvalue()),
                self.id,
                operation=outcome.operation,
                unapplied_oprs=[],
                is_error=True)
            return (EditFailureBehavior.TERMINATE_AND_REVERT, outcome)
        return super()._on_edit_failure(outcome)

#### Compute

class Compute_ToolArg(TypedDict):
    thought: str
    term: xterm
    name: str

@proof_operation("Compute", Compute_ToolArg)
class Compute(Leaf):
    def __init__(self, config: NodeConfig, arg: Compute_ToolArg):
        super().__init__(config, arg["thought"])
        self.term_str: xterm = arg["term"]
        self.result_name: str = arg["name"]
        self.result_fact: tuple[varname, term] | None = None
        self._prev_result_fact: tuple[varname, term] | None = None

    def quickview_title(self) -> str:
        return f"Compute (resulting fact: {self.result_name})"

    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.result_fact is not None and self.result_fact != self._prev_result_fact:
            print_indent(indent, file)
            name, expr = self.result_fact
            file.write("results:\n")
            print_indent(indent + 1, file)
            file.write(f"{name.unicode}: {expr.unicode}\n")
            self._prev_result_fact = self.result_fact
        return indent

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        return Minilang_Operation.COMPUTE(self.result_name, self.term_str)

    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        await super()._refresh_me_alone(auto_intro)
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            for m in self.resulting_state().messages:
                if isinstance(m, Compute_Result_Msg):
                    self.result_fact = (m.name, m.result)
                    break

    def print(self, indent: int, file: MyIO, update_line: bool = False,
              show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Compute\n")
        print_indent(indent, file)
        file.write(f"term: {self.term_str}\n")
        print_indent(indent, file)
        file.write(f"name: {self.result_name}\n")
        if self.result_fact is not None:
            print_indent(indent, file)
            name, expr = self.result_fact
            file.write("results:\n")
            print_indent(indent + 1, file)
            file.write(f"{name.unicode}: {expr.unicode}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file,
                [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

#### Witness

class Witness_ToolArg(TypedDict):
    thought: str
    witnesses: list[xterm]

@validator(Witness_ToolArg)
def _validate_witness_tool_arg(data: Any, path: str) -> Witness_ToolArg:
    # Accept either a single term or a list of terms for `witnesses`,
    # normalizing the bare-string form to a one-element list.
    if isinstance(data, dict) and isinstance(data.get("witnesses"), str):
        data["witnesses"] = [data["witnesses"]]
    if (isinstance(data, dict) and isinstance(data.get("witnesses"), list)
            and len(data["witnesses"]) == 0):
        raise ArgumentError({}, f"{path}: No witness terms is provided")
    return _validate_typed_dict(Witness_ToolArg, data, path)

@proof_operation("Witness", Witness_ToolArg)
class Witness(Leaf):
    def __init__(self, config: NodeConfig, arg: Witness_ToolArg):
        super().__init__(config, arg["thought"])
        self.witnesses = list(arg["witnesses"])
    def quickview_title(self) -> str:
        # The witness terms can be long; the full list is shown in `print`.
        return "Witness"
    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Witness\n")
        if len(self.witnesses) == 1:
            print_indent(indent, file)
            file.write(f"witness: {self.witnesses[0]}\n")
        else:
            print_indent(indent, file)
            file.write("witnesses:\n")
            for w in self.witnesses:
                print_indent(indent + 1, file)
                file.write(f"- {w}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

    def the_operation(self) -> Minilang_Operation:
        return Minilang_Operation.WITNESS(self.witnesses)


#### Define

class Define_ToolArg(TypedDict):
    thought: str
    name: str
    type: NotRequired[xtyp]
    equations: list[xterm]
    metric: NotRequired[list[xterm]]

@proof_operation("Define", Define_ToolArg)
class Define(SubgoalMaker):
    _is_declarative = True
    _done_label = "done"
    """Define a (recursive) function proof-locally via minilang's FUN
    command. The Minilang.FUN'' ML API is invoked with
    `open_on_fail = true` so that if pat-completeness or termination
    cannot be discharged automatically, a deferred proof block is
    pushed onto the minilang stack for the agent to finish
    interactively.

    Two very different control-flow paths:

    - **Auto-prove path**: the default prover, BY_METRIC sledge, and
      the auto+termination_simp simplification pass close everything
      inside FUN. No block is pushed onto the minilang stack, no
      reporter signal is fired, and `Define` acts as a leaf-like
      node: zero sub_nodes, `has_ending_opr = False`, nothing
      emitted after the DEFINE opcode.

    - **Deferred path**: one of `Pat_Completeness_Proof_Opened_Msg`
      or `Termination_Proof_Opened_Msg` reporter messages arrives
      post-DEFINE, signalling that a deferred proof block has been
      pushed with residual subgoals still to discharge. Following
      the established framework convention (see the comment at
      `should_I_show_pending_goal` for why multi-goal states must
      be modelled as GoalNode children), `Define` creates one
      `GoalNode` child per residual subgoal, advancing the ml_state
      via `sorry` between siblings. `SubgoalMaker` makes non-last
      GoalNode children emit `NEXT` and the last emit `None`.
      Define then emits a single trailing `END` via
      `has_ending_opr = True` / `ending_opr = END` to close the
      deferred block — producing the sequence
      `DEFINE; <proof_1>; NEXT; <proof_2>; END` on the ML side.
    """

    def __init__(self, config: NodeConfig, arg: Define_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.name = arg["name"]
        self.type: str | None = arg.get("type") or None
        self.equations = list(arg["equations"])
        self.metric = list(arg.get("metric") or [])
        # Set by _refresh_the_beginning_opr based on reporter messages
        # the ML side emits when FUN pushes a deferred block. Controls
        # whether the block has GoalNode children / ending END.
        self._deferred_block_opened: bool = False

    def _nearest_goal_for_subagent(self) -> 'Node | None':
        # Change A: a Define IS a delegatable unit, overriding the base
        # SubgoalMaker redirect-up. The other SubgoalMakers
        # (CaseSplit/Induction/Branch) stay non-delegatable — their subgoals
        # carry local context. A deferred Define's obligations (pat-completeness
        # / termination) are self-contained — about the definition itself — so a
        # worker may be dispatched on the whole Define to discharge all of them.
        return self
    def quickview_title(self) -> str:
        return f"Define {self.name}"
    def _should_print_done(self) -> bool:
        if self._deferred_block_opened and self._body_subnodes_succeeded:
            return True
        return super()._should_print_done()

    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Define\n")
        print_indent(indent, file)
        file.write(f"name: {self.name}\n")
        if self.type is not None:
            print_indent(indent, file)
            file.write(f"type: {self.type}\n")
        print_indent(indent, file)
        file.write("equations:\n")
        for eq in self.equations:
            print_indent(indent + 1, file)
            file.write(f"- {eq}\n")
        if len(self.metric) == 1:
            print_indent(indent, file)
            file.write(f"metric: {self.metric[0]}\n")
        elif self.metric:
            print_indent(indent, file)
            file.write("metric:\n")
            for m in self.metric:
                print_indent(indent + 1, file)
                file.write(f"- {m}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file, [Warning.Position.HEADER])

    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ("proof of termination", indent + 1)

    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.DEFINE(
            self.name, self.type, self.equations, self.metric)

    def _should_open_proof_block(self, s0: Minilang_State) -> _OpenSubgoalBlock:
        # Unlike Intro/Branch/etc., the Define node decides whether a
        # proof block opens based on the reporter messages — not by
        # counting top goals (the outer lemma goal is at the top in
        # the auto-prove path, which would otherwise be misread as
        # "one residual" and reopen the parent). When the ML side
        # pushes a deferred pat-completeness / termination block, it
        # fires Pat_Completeness_Proof_Opened_Msg or
        # Termination_Proof_Opened_Msg via the minilang reporter, and
        # the Python side unpacks them into s0.messages.
        self._deferred_block_opened = any(
            isinstance(m, (Pat_Completeness_Proof_Opened_Msg,
                           Termination_Proof_Opened_Msg))
            for m in s0.messages)
        # Pick up the inferred type from Define_Result_Msg (covers the
        # case where the user omitted the type field).
        for m in s0.messages:
            if isinstance(m, Define_Result_Msg):
                self.type = m.type.unicode
                break
        # Define's deferred block is internal and bracketed by an explicit
        # END opcode — the enclosing proof line continues past Define with
        # more siblings (e.g. a subsequent Witness).  So when it opens, it
        # does NOT close the parent.
        if self._deferred_block_opened:
            return _OpenSubgoalBlock.YES
        return _OpenSubgoalBlock.NO

    def has_ending_opr(self) -> bool:
        # Deferred path: Define emits the single trailing END that
        # closes the minilang deferred block. (The last GoalNode
        # child emits None by SubgoalMaker's default.)
        # Auto-prove path: no block on the stack, no END to emit.
        return self._deferred_block_opened

    def ending_opr(self) -> Minilang_Operation | None:
        if self._deferred_block_opened:
            return Minilang_Operation.END()
        else:
            return None

    def _define_var(self, ret: Vars) -> Vars:
        ty = self.type if self.type is not None else "?"
        ret[IsaTerm.from_agent(self.name)] = IsaTerm.from_agent(ty)
        return ret

    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        # Variables visible to this node's *children* (the termination
        # subgoals reference the function being defined).
        return self._define_var(ret)

    def _fixed_vars_after_me(self, ret: Vars) -> Vars:
        # Variables visible to *subsequent siblings* (e.g. Witness
        # picking the function as a witness for the existential goal).
        return self._define_var(ret)

    def _beginning_opr_err_msgs(self, err: IsabelleError) -> FailureReason:
        return FailureReason(
            "Failed to define the function: " + "\n".join(err.errors))

    def _child_refresh_failure_err_msgs(self, child: Node) -> FailureReason:
        return FailureReason(
            "One of the proof steps for the function's pat-completeness "
            "or termination obligations failed.")

    def _ending_opr_err_msgs(self, err: IsabelleError) -> FailureReason:
        return FailureReason(
            "The proof body did not fully discharge the "
            "pat-completeness / termination residuals.")


#### Unfold

class Interaction_ChooseDef(Interaction):
    """Pick which definition(s) an ``Unfold`` should use when its target
    resolves to several candidate equations. Non-forking: the agent that
    issued the ``Unfold`` answers inline, mid-edit."""
    fork_allowed_tools = [TOOL_ANSWER_INDEXES_OR_NAME, TOOL_SEARCH]

    @property
    def is_non_forking(self) -> bool:
        return True

    def __init__(self, constants: list[str], candidate_defs: list[IsabelleFact_Presented],
                 state: 'Minilang_State | None' = None):
        self.constants = constants
        self.candidate_defs = candidate_defs
        self.state = state
    async def prompt(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        if len(self.constants) == 1:
            file.write(f"Multiple definitions found for {self.constants[0]}:\n")
        else:
            file.write(f"Multiple definitions found for constants {', '.join(self.constants)}:\n")
        for i, ref in enumerate(self.candidate_defs):
            print_indent(indent+1, file)
            file.write(f"{i}. {ref.full_name}: {', '.join(e.unicode for e in ref.expression)}\n")
        if len(self.candidate_defs) > 1:
            file.write(f"Select definitions to use in unfolding. Call `{tn(TOOL_ANSWER_INDEXES_OR_NAME)}` with `indexes`, or the `name` of a definition, or leave empty to skip.\n")
        else:
            file.write(f"Select this definition to use in unfolding. Call `{tn(TOOL_ANSWER_INDEXES_OR_NAME)}` with `indexes`, or the `name` of a definition, or leave empty to skip.\n")
    async def answer(self, answer: AnswerIndexesOrName) -> list[IsabelleFact]:
        if answer.name is not None:
            for d in self.candidate_defs:
                if d.short_name.unicode == answer.name or d.full_name == answer.name:
                    return [d]
            if self.state is not None:
                presented = await _try_resolve_as_named_fact(self.state, answer.name)
                if presented is not None:
                    return [presented]
            raise Interaction_BadAnswer(
                f"No accessible fact found with name '{answer.name}'. Select by index.")
        if not answer.indexes:
            return []
        for idx in answer.indexes:
            _check_index(idx, len(self.candidate_defs))
        return [self.candidate_defs[idx] for idx in answer.indexes]


class Unfold_ToolArg(TypedDict):
    thought: str
    targets: list[str]  # Isabelle/HOL terms to unfold


_COND_UNFOLD_NOTE = (
    "Note: unfolding a conditional definition may have no effect (it only rewrites "
    "when the premise is already discharged from the current goal). If needed, use "
    "Derive first to discharge the premise.")


@proof_operation("Unfold", Unfold_ToolArg)
class Unfold(Leaf):
    def __init__(self, config: NodeConfig, arg: Unfold_ToolArg):
        super().__init__(config, arg["thought"])
        self.targets: list[str] = arg["targets"]
        self.fact_refs: list[IsabelleFact] | None = None
    def quickview_title(self) -> str:
        return f"Unfold {', '.join(self.targets)}"
    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Unfold\n")
        if self.targets:
            print_indent(indent, file)
            file.write("targets:\n")
            for target in self.targets:
                print_indent(indent+1, file)
                file.write(f"- {target}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        if self.fact_refs is None:
            all_defs = await self.ml_state.potential_defs_of(
                [IsaTerm.from_agent(t) for t in self.targets])
            if len(all_defs) == 0:
                self.fact_refs = []  # the_operation will report "no definitions found"
            elif len(all_defs) == 1:
                self.fact_refs = [all_defs[0]]
            else:
                self.fact_refs = await the_session().launch_interaction(
                    Interaction_ChooseDef(self.targets, all_defs, state=self.ml_state))
        elif self.ml_state.initialized():
            self.fact_refs = await self.ml_state.refresh_facts(self.fact_refs)
        await super()._refresh_me_alone(auto_intro)

    def _synthetic_hint_notices(self) -> 'list[Hint_Notice_Msg]':
        # Warn once per context when a chosen definition carries a premise: the Unfold
        # backend (Local_Defs.unfold_goals) only fires a conditional rule when the
        # premise is dischargeable from the goal's own premises, else it silently
        # no-ops. Self-gated on SUCCESS (the render walk calls this on every node).
        if (self.status.status == EvaluationStatus.Status.SUCCESS
                and self.fact_refs
                and any(getattr(f, 'is_conditional', False) for f in self.fact_refs)):
            return [Hint_Notice_Msg("unfold:conditional-definition", _COND_UNFOLD_NOTE)]
        return []

    def _on_edit_failure(self, outcome: 'EditOutcome') -> 'tuple[EditFailureBehavior, EditOutcome]':
        if self.status.status == EvaluationStatus.Status.FAILURE:
            # Multi-op batches skip auto-revert so the agent sees
            # the failing node and can amend it.
            if len(outcome.request) > 1:
                return super()._on_edit_failure(outcome)
            # Store the blob ABSOLUTE; its `step …` refs and the carried node id
            # are projected to the caller's namespace at render time (the single
            # id-translation boundary, CannotEdit.render). Relativizing here too
            # would double-project a worker's ids.
            file = MyIO(StringIO())
            if self.status.reason:
                file.write(self.status.reason.reason)
            if self.warnings:
                self._print_warnings(0, file, list(Warning.Position))
            outcome.failure = CannotEdit_EvaluationFailed(
                FailureReason(file.getvalue()),
                self.id,
                operation=outcome.operation,
                unapplied_oprs=[],
                is_error=True)
            return (EditFailureBehavior.TERMINATE_AND_REVERT, outcome)
        return super()._on_edit_failure(outcome)

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        if not self.targets:
            return FailureReason("Unfold operation must specify at least one target.")
        if not self.fact_refs:
            return FailureReason(f"No definitions found for: {', '.join(self.targets)}")
        unfound = [f for f in self.fact_refs if isinstance(f, IsabelleFact_Unfound)]
        if unfound:
            return FailureReason("\n".join(f"Fact \"{f.name().unicode}\" not found" for f in unfound))
        return Minilang_Operation.UNFOLD(self.fact_refs)


#### Derive

class Derive_ToolArg(TypedDict):
    thought: str
    rule: FactByName                                          # The rule to specialize
    instantiations: NotRequired[list[Instantiation | None]]    # Variable instantiations (default: []); null entries are skipped
    discharging_facts: NotRequired[list[FactByName | None]]   # Facts to discharge premises (default: []); null entries skip a position
    result_name: str                                          # Name to bind the result under

@proof_operation("Derive", Derive_ToolArg)
class Derive(Leaf):
    def __init__(self, config: NodeConfig, arg: Derive_ToolArg):
        super().__init__(config, arg["thought"])
        self.rule: FactByName = arg["rule"]
        self.instantiations: list[Instantiation] = [
            x for x in (arg.get("instantiations") or []) if x is not None]
        self.discharging_facts: list[FactByName] = [
            f for f in (arg.get("discharging_facts") or []) if f is not None]
        self.result_name: str = arg["result_name"]
        self.rule_ref: IsabelleFact | None = None
        self.discharge_refs: list[IsabelleFact] | None = None
        self.result_facts: list[tuple[varname, term]] | None = None
        """(fact_name, pretty_expression) pairs for facts derived by SPECIALIZE,
        populated from Specialize_Result_Msg after successful execution."""
        self._prev_result_facts: list[tuple[varname, term]] | None = None

    def quickview_title(self) -> str:
        if isinstance(self.rule_ref, IsabelleFact_Presented):
            return f"Derive {self.rule_ref.short_name.unicode}"
        return f"Derive {self.rule['name']}"
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.result_facts is not None and self.result_facts != self._prev_result_facts:
            print_indent(indent, file)
            file.write("resulting facts:\n")
            for name, expr in self.result_facts:
                print_indent(indent + 1, file)
                file.write(f"- {name.unicode}: {expr.unicode}\n")
            self._prev_result_facts = self.result_facts
        return indent

    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        if self.rule_ref is None or self.discharge_refs is None:
            all_refs = [self.rule] + self.discharging_facts
            fetched = _fetched_to_facts(await self.ml_state.fetch_facts(all_refs))
            self.rule_ref = fetched[0]
            self.discharge_refs = fetched[1:]
        elif self.ml_state.initialized():
            refreshed = await self.ml_state.refresh_facts(
                [self.rule_ref, *self.discharge_refs])
            self.rule_ref = refreshed[0]
            self.discharge_refs = refreshed[1:]
        await super()._refresh_me_alone(auto_intro)
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            messages = self.resulting_state().messages
            for m in messages:
                if isinstance(m, Specialize_Result_Msg):
                    self.result_facts = m.facts
                    break

    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Derive\n")
        print_indent(indent, file)
        file.write("rule:\n")
        if self.rule_ref is not None:
            self.rule_ref.print(indent+1, file)
        else:
            _print_raw_fact(self.rule, indent+1, file)
        if self.instantiations:
            print_indent(indent, file)
            file.write("instantiations:\n")
            for inst in self.instantiations:
                print_indent(indent+1, file)
                file.write(f"- {inst['name']} = {inst['value']}\n")
        if self.discharge_refs is not None:
            if self.discharge_refs:
                print_indent(indent, file)
                file.write("discharging facts:\n")
                for ref in self.discharge_refs:
                    ref.print(indent+1, file)
        elif self.discharging_facts:
            print_indent(indent, file)
            file.write("discharging facts:\n")
            for ref in self.discharging_facts:
                _print_raw_fact(ref, indent+1, file)
        # if self.result_name:
        #     print_indent(indent, file)
        #     file.write(f"result name: {self.result_name}\n")
        if self.result_facts is not None:
            print_indent(indent, file)
            file.write("resulting facts:\n")
            for name, expr in self.result_facts:
                print_indent(indent + 1, file)
                file.write(f"- {name.unicode}: {expr.unicode}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

    def _on_edit_failure(self, outcome: 'EditOutcome') -> 'tuple[EditFailureBehavior, EditOutcome]':
        if self.status.status == EvaluationStatus.Status.FAILURE:
            # Multi-op batches skip auto-revert so the agent sees
            # the failing node and can amend it.
            if len(outcome.request) > 1:
                return super()._on_edit_failure(outcome)
            # Store the blob ABSOLUTE; its `step …` refs and the carried node id
            # are projected to the caller's namespace at render time (the single
            # id-translation boundary, CannotEdit.render). Relativizing here too
            # would double-project a worker's ids.
            file = MyIO(StringIO())
            if self.status.reason:
                file.write(self.status.reason.reason)
            if self.warnings:
                self._print_warnings(0, file, list(Warning.Position))
            outcome.failure = CannotEdit_EvaluationFailed(
                FailureReason(file.getvalue()),
                self.id,
                operation=outcome.operation,
                unapplied_oprs=[],
                is_error=True)
            return (EditFailureBehavior.TERMINATE_AND_REVERT, outcome)
        return super()._on_edit_failure(outcome)

    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        if self.result_facts is not None:
            for name, expr in self.result_facts:
                ret[name] = expr
        return ret

    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return self._fixed_facts_at_me(ret)

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        assert self.rule_ref is not None and self.discharge_refs is not None, \
            "Derive.the_operation called before first refresh resolved refs"
        if isinstance(self.rule_ref, IsabelleFact_Unfound):
            return FailureReason(f"Rule fact \"{self.rule_ref.name().unicode}\" not found")
        unfound = [f for f in self.discharge_refs if isinstance(f, IsabelleFact_Unfound)]
        if unfound:
            return FailureReason("\n".join(f"Fact \"{f.name().unicode}\" not found" for f in unfound))
        return Minilang_Operation.SPECIALIZE(
            self.result_name,
            self.rule_ref,
            [(i["name"], i["value"]) for i in self.instantiations],
            self.discharge_refs
        )


#### Rewrite

# (fact_index, rule_pretty, [(match_pretty, match_raw_term)])
LoopingRuleInfo = tuple[int, str, list[tuple[str, lambda_term]]]

class Interaction_SelectRewriteTargets(Interaction):
    """Interaction for selecting specific subterms to rewrite when a rule loops."""
    def __init__(self, looping_rules: list[LoopingRuleInfo],
                 fact_names: list[str]):
        self.looping_rules = looping_rules
        self.fact_names = fact_names
    async def prompt(self, indent: int, file: MyIO) -> None:
        for fact_idx, rule_pretty, matches in self.looping_rules:
            fact_name = self.fact_names[fact_idx] if fact_idx < len(self.fact_names) else f"rule {fact_idx}"
            print_indent(indent, file)
            file.write(f"Rule '{fact_name}' ({rule_pretty}) would cause infinite rewriting.\n")
            if matches:
                print_indent(indent, file)
                n = len(matches)
                noun = "subterm" if n == 1 else "subterms"
                file.write(f"To use this rule safely, select which specific {noun} to rewrite:\n")
                for i, (pretty, _raw) in enumerate(matches):
                    print_indent(indent + 1, file)
                    file.write(f"{i}. {pretty}\n")
            else:
                print_indent(indent, file)
                file.write("No matching subterms found in rewrite targets.\n")
            print_indent(indent, file)
            _atn = tn(TOOL_ANSWER_INDEXES)
            if matches and len(matches) == 1:
                file.write(f"Call `{_atn}` with the `indexes` of the subterm to rewrite, or with empty `indexes` to drop this rule.\n")
            else:
                file.write(f"Call `{_atn}` with the `indexes` of the subterms to rewrite, or with empty `indexes` to drop this rule.\n")
    fork_allowed_tools = [TOOL_ANSWER_INDEXES, TOOL_SEARCH]

    async def answer(self, answer: AnswerIndexes) -> list[tuple[int, list[lambda_term]]]:
        """Returns [(fact_index, [selected_raw_terms])] for each looping rule.
        Empty selection for a rule means drop it."""
        idxs = answer.indexes
        result: list[tuple[int, list[lambda_term]]] = []
        # answer is a list of indices — applied to all looping rules sequentially
        # For simplicity: if there's one looping rule, indices select its subterms;
        # if multiple, this needs a richer protocol. For now, support single-rule case.
        if len(self.looping_rules) == 1:
            fact_idx, _, matches = self.looping_rules[0]
            if not idxs:
                result.append((fact_idx, []))
            else:
                selected_terms: list[lambda_term] = []
                for idx in idxs:
                    _check_index(idx, len(matches))
                    selected_terms.append(matches[idx][1])
                result.append((fact_idx, selected_terms))
        else:
            # Multiple looping rules: treat answer as list of lists
            # For now, apply same indices to all rules (can be refined later)
            for fact_idx, _, matches in self.looping_rules:
                if not idxs:
                    result.append((fact_idx, []))
                else:
                    selected_terms = []
                    for idx in idxs:
                        if 0 <= idx < len(matches):
                            selected_terms.append(matches[idx][1])
                    result.append((fact_idx, selected_terms))
        return result

class Interaction_SelectIHFacts(Interaction):
    """Pre-flight selection of in-scope facts to carry into the induction
    hypothesis (alongside the `arbitrary:` generalization). Multi-select; the
    chosen fact names supplement the agent-supplied `IH_facts`. Non-forking:
    the agent that issued the ``Induction`` answers inline, mid-edit."""
    fork_allowed_tools = [TOOL_ANSWER_INDEXES, TOOL_SEARCH]

    @property
    def is_non_forking(self) -> bool:
        return True

    def __init__(self, candidates: list[tuple[str, IsaTerm]],
                 relevant_vars: list[str]):
        self.candidates = candidates
        self.relevant_vars = relevant_vars
    async def prompt(self, indent: int, file: MyIO) -> None:
        if not self.candidates:
            raise ImmediateAnswer([])
        vars_str = string_of_and_list(self.relevant_vars)
        print_indent(indent, file)
        file.write(
            f"These in-scope facts mention {vars_str}. Select the ones you will "
            f"need later in this induction proof. Facts you leave unselected "
            f"become unusable after the induction! But selecting ones you won't "
            f"need bloats the induction and makes it harder to work with. Call "
            f"`{tn(TOOL_ANSWER_INDEXES)}` with their indexes; empty = none.\n")
        for i, (name, prop) in enumerate(self.candidates):
            print_indent(indent + 1, file)
            file.write(f"{i}. {name}: {prop.unicode}\n")
    async def answer(self, answer: AnswerIndexes) -> list[str]:
        chosen: list[str] = []
        for idx in answer.indexes:
            _check_index(idx, len(self.candidates))
            chosen.append(self.candidates[idx][0])
        return chosen

class Interaction_ClassifyInductionVars(Interaction):
    """Pre-flight classification of in-scope variables the agent left
    unspecified in an Induction: each is either fixed (held constant across
    the induction hypotheses and cases) or generalized (universally
    quantified in the induction hypothesis). Multi-select; the chosen
    variables become `generalized`, the rest `fixed`. The answer is the list
    of variable names to generalize. Non-forking: the agent that issued the
    ``Induction`` answers inline, mid-edit."""
    fork_allowed_tools = [TOOL_ANSWER_INDEXES, TOOL_SEARCH]

    @property
    def is_non_forking(self) -> bool:
        return True

    def __init__(self, unclassified: list[tuple[str, str]]):
        # (name, type) of each in-scope variable left unclassified.
        self.unclassified = unclassified
    async def prompt(self, indent: int, file: MyIO) -> None:
        if not self.unclassified:
            raise ImmediateAnswer([])
        print_indent(indent, file)
        file.write(
            "Your Induction operation did not classify the following "
            "variables. Should each be treated as fixed (held constant "
            "across the induction hypotheses and cases), or generalized "
            "(universally quantified in the induction hypothesis)? Select "
            f"the indexes of all variables to generalize (call "
            f"`{tn(TOOL_ANSWER_INDEXES)}`; unselected ones stay fixed).\n")
        for i, (name, typ) in enumerate(self.unclassified):
            print_indent(indent + 1, file)
            file.write(f"{i}. {name} :: {typ}\n")
    async def answer(self, answer: AnswerIndexes) -> list[str]:
        chosen: list[str] = []
        for idx in answer.indexes:
            _check_index(idx, len(self.unclassified))
            chosen.append(self.unclassified[idx][0])
        return chosen

Rewrite_ToolArg = TypedDict('Rewrite_ToolArg', {
    'thought': str,
    'using': list[FactByName | FactByProposition],
    'use system simplifiers': bool,
    'rewrite goal': bool,
    'rewrite premises': list[str]
})

AUTOCONVERT_REWRITE_MSG = (
    "The rule does not apply as an inference rule, but it is a rewrite rule; "
    "applied it as a Rewrite instead.")

@proof_operation("Rewrite", Rewrite_ToolArg)
class Rewrite(Leaf):
    def __init__(self, config: NodeConfig, arg: Rewrite_ToolArg):
        super().__init__(config, arg["thought"])
        self.use_system_simplifiers: bool = arg["use system simplifiers"]
        self.rewrite_goal: bool = arg["rewrite goal"]
        self.rewrite_premises: list[str] = arg["rewrite premises"]
        self._raw_using: list[FactByName | FactByProposition] = [
            f for f in arg["using"] if f is not None]
        self.using: list[IsabelleFact] | None = None
        # Set by `InferenceRule._autoconvert_to_rewrite` when this Rewrite was
        # auto-synthesised from a failed InferenceRule. Live-only (not packed):
        # `_refresh_me_alone` re-emits the provenance HEADER notice from it on
        # every refresh (warnings are otherwise stripped each refresh).
        self._was_autoconverted: bool = False
        self.fact_targets: list[list[lambda_term] | None] | None = None
        self.bindings: Bindings | None = None
        self.running_time = 0
        self._prev_bindings: Bindings | None = None
        self._prev_result_goal: Goal | None | str = None
        """Tracks the post-rewrite goal for quickview change detection.
        None = not yet shown, 'solved' = goal was solved, Goal = goal changed to."""
        self._my_last_goal: Goal | None = None
        """Goal produced by the last successful execution, for changed detection.
        Unlike resulting_state().leading_goal, this is not affected by
        sibling deletion re-routing resulting_state()."""
    def quickview_title(self) -> str:
        targets: list[str] = []
        if self.rewrite_goal:
            targets.append("goal")
        targets.extend(self.rewrite_premises)
        return f"Rewrite {', '.join(targets)}"
    def does_quickview_need_detail(self) -> bool:
        # A fresh SUCCESS leaf is neither `changed` nor non-continuable, so the
        # base predicate suppresses warnings in the outline (quickview) — the
        # blind spot that hid the no-op notice (and would hide the fallback /
        # once-simproc / stale-target notices on first fill too). A Rewrite that
        # has something to say must always surface it.
        return super().does_quickview_need_detail() or bool(self.warnings)
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.bindings is not None and self.bindings != self._prev_bindings:
            print_var_bindings(self.bindings[0], indent, file, "fixing variables")
            print_fact_bindings(self.bindings[1], indent, file, "resulting premises")
            self._prev_bindings = self.bindings
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            result_goal = self.resulting_state().leading_goal
            if result_goal is None:
                cur: Goal | str = "solved"
            elif (prev_goal := self.ml_state.leading_goal) is not None \
                    and result_goal.conclusion != prev_goal.conclusion:
                cur = result_goal
            else:
                cur = None  # type: ignore[assignment]
            if cur is not None and cur != self._prev_result_goal:
                if cur == "solved":
                    print_indent(indent, file)
                    file.write("goal is solved.\n")
                else:
                    assert not isinstance(cur, str)
                    print_indent(indent, file)
                    file.write("goal changes into:\n")
                    print_goal(cur, indent+1, False, file, self._ctxt_at_me(),
                               truncate=True)
                self._prev_result_goal = cur
                if isinstance(cur, Goal):
                    self._the_single_printed_goal = cur
        return indent
    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Rewrite\n")
        has_facts = (self.using is not None and self.using) or self._raw_using
        if has_facts or self.use_system_simplifiers:
            print_indent(indent, file)
            file.write(f"using:\n")
            if self.using is not None:
                for ref in self.using:
                    ref.print(indent+1, file)
            elif self._raw_using:
                for ref in self._raw_using:
                    _print_raw_fact(ref, indent+1, file)
            if self.use_system_simplifiers:
                print_indent(indent+1, file)
                file.write("- system simplifiers\n")
        print_indent(indent, file)
        file.write("targets:\n")
        if self.rewrite_goal:
            print_indent(indent+1, file)
            file.write("- the goal\n")
        if self.rewrite_premises:
            for premise in self.rewrite_premises:
                print_indent(indent+1, file)
                file.write(f"- {premise}\n")
        if self.bindings is not None:
            print_var_bindings(self.bindings[0], indent, file, "fixing variables")
            print_fact_bindings(self.bindings[1], indent, file, "resulting premises")

        if self.status.status == EvaluationStatus.Status.SUCCESS:
            result_goal = self.resulting_state().leading_goal
            if result_goal is None:
                print_indent(indent, file)
                file.write("goal is solved.\n")
            elif (prev_goal := self.ml_state.leading_goal) is not None \
                    and result_goal.conclusion != prev_goal.conclusion:
                print_indent(indent, file)
                file.write("goal changes into:\n")
                print_goal(result_goal, indent+1, False, file, self._ctxt_at_me(),
                           truncate=True)

        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        if self.bindings is not None:
            for var in self.bindings[0]:
                ret[var.external_varname] = var.type
        return ret

    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        if self.bindings is not None:
            for fact in self.bindings[1]:
                ret[fact.name] = fact.pretty
        return ret

    def _fixed_vars_after_me(self, ret: Vars) -> Vars:
        return self._fixed_vars_at_me(ret)

    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return self._fixed_facts_at_me(ret)

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        if not self.rewrite_goal and not self.rewrite_premises:
            return FailureReason(
                "Rewrite operation must target at least one of: the goal or some premises. "
                "Set 'rewrite goal' to true or provide at least one premise name in 'rewrite premises'.")
        using = self.using if self.using is not None else []
        unfound = [f for f in using if isinstance(f, IsabelleFact_Unfound)]
        if unfound:
            return FailureReason("\n".join(f"Fact \"{f.name().unicode}\" not found" for f in unfound))
        bindings = None
        if self.bindings is not None:
            var_bindings = [(vb.internal_varname.ascii, vb.external_varname.ascii, vb.type.ascii) for vb in self.bindings[0]]
            fact_bindings = [(fb.expr, fb.name.ascii, fb.pretty.ascii) for fb in self.bindings[1]]
            bindings = (var_bindings, fact_bindings)
        # Build per-fact targets for the operation.
        # Filter out facts with empty target lists (user chose to drop them).
        facts_with_targets: list[tuple[IsabelleFact, list[lambda_term] | None]] = []
        for i, fact in enumerate(using):
            targets = self.fact_targets[i] if self.fact_targets and i < len(self.fact_targets) else None
            if targets is not None and len(targets) == 0:
                continue  # user chose to drop this rule
            facts_with_targets.append((fact, targets))
        return Minilang_Operation.SIMPLIFY(
            facts_with_targets,
            self.use_system_simplifiers,
            self.rewrite_premises,
            self.rewrite_goal,
            bindings
        )

    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        is_init = self._first_time
        if self.using is None:
            fetched = _fetched_to_facts(await self.ml_state.fetch_facts(self._raw_using))
            facts, unfound_warnings = _filter_unfound(fetched)
            self.using, pit_warnings = await _filter_unprovable(facts, self.ml_state)
            for w in unfound_warnings + pit_warnings:
                self.warnings.append(Warning(Warning.Position.FOOTER, w))
            # Check for looping rules and fork interaction if needed
            # Send full fact references (including [xwhere ...] attributes) so
            # the ML side resolves the same instantiated theorems that SIMPLIFY uses.
            fact_names = [f.pack()[0] for f in self.using
                          if isinstance(f, IsabelleFact_Presented)]
            if fact_names:
                looping_info = await self.ml_state.check_looping_rules(
                    fact_names, self.rewrite_goal, self.rewrite_premises)
                if looping_info:
                    selections: list[tuple[int, list[lambda_term]]] = \
                        await the_session().launch_interaction(
                            Interaction_SelectRewriteTargets(looping_info, fact_names))
                    fact_targets: list[list[lambda_term] | None] = [None] * len(self.using)
                    for fact_idx, selected_terms in selections:
                        if fact_idx < len(fact_targets):
                            fact_targets[fact_idx] = selected_terms
                    self.fact_targets = fact_targets
        elif self.ml_state.initialized():
            self.using = await self.ml_state.refresh_facts(self.using)
        # Idempotency: the HEADER notices below (no-op / system-simp fallback /
        # once-simproc / stale-target / missing-binding) are re-derived from
        # scratch on every refresh, but a node is re-refreshed several times per
        # edit (upstream-change cascades) while warnings are cleared only at
        # end-of-edit (`root.reset`). Drop stale HEADER notices now so a
        # re-refresh cannot accumulate duplicates. Keep FOOTER warnings
        # (unfound/unprovable facts): they are appended only on the first
        # refresh (the `using is None` branch above) and would otherwise be lost.
        self.warnings = [w for w in self.warnings if w.position is Warning.Position.FOOTER]
        # Re-derive the auto-conversion provenance notice each refresh (same
        # idempotency reason as the notices above): the strip just above would
        # otherwise wipe it after the first render, collapsing the node in the
        # compressed quickview.
        if self._was_autoconverted:
            self.warnings.append(
                Warning(Warning.Position.HEADER, AUTOCONVERT_REWRITE_MSG))
        old_bindings = self.bindings
        # Execute the operation via parent Leaf implementation
        await super()._refresh_me_alone(auto_intro)

        # If operation succeeded, extract bindings and track changes
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            self.running_time += 1
            messages = self.resulting_state().messages
            intro_bindings_msgs = [m for m in messages if isinstance(m, Intro_Bindings_Msg)]
            match intro_bindings_msgs:
                case [intro_bindings_msg]:
                    pass
                case _:
                    raise InternalError(
                        f"Expected exactly one Intro_Bindings_Msg in Rewrite's messages, got {len(intro_bindings_msgs)}"
                    )
            self.bindings = intro_bindings_msg.final

            # Only warn about changes on subsequent runs (not first time)
            if self.running_time >= 2:
                missing_vars, missing_facts = intro_bindings_msg.missing
                auto_vars, auto_facts = intro_bindings_msg.auto_introduced

                # Warn about missing variables
                if missing_vars:
                    varnames = [v.external_varname for v in missing_vars]
                    vstr = titled_string_of_and_list(varnames, "variable", "variables")
                    self.warnings.append(Warning(Warning.Position.HEADER,
                        f"The proof goal has changed. Tracking of the {vstr} has been lost."))

                # Warn about missing premises
                if missing_facts:
                    premises = [p.name for p in missing_facts]
                    pstr = titled_string_of_and_list(premises, "premise", "premises")
                    self.warnings.append(Warning(Warning.Position.HEADER,
                        f"The proof goal has changed. Tracking of the {pstr} has been lost."))

                # Warn about auto-introduced variables
                if auto_vars:
                    def print_var_warning(indent: int, file: MyIO) -> int:
                        print_indent(indent, file)
                        file.write(f"- The proof goal has changed and new variables occur:\n")
                        for binding in auto_vars:
                            print_indent(indent+1, file)
                            file.write(f"- {binding.external_varname.unicode}: {binding.type.unicode}\n")
                        return indent
                    self.warnings.append(Warning(Warning.Position.HEADER, print_var_warning))

                # Warn about auto-introduced premises
                if auto_facts:
                    def print_fact_warning(indent: int, file: MyIO) -> int:
                        print_indent(indent, file)
                        file.write(f"- The proof goal has changed and new premises occur:\n")
                        for binding in auto_facts:
                            print_indent(indent+1, file)
                            file.write(f"- {binding.name.unicode}\n")
                        return indent
                    self.warnings.append(Warning(Warning.Position.HEADER, print_fact_warning))

            # Check for simplify fallback (system simplifiers disabled due to timeout)
            fallback_msgs = [m for m in messages if isinstance(m, Simplify_Fallback_Nosys_Msg)]
            if fallback_msgs:
                self.use_system_simplifiers = False
                self.warnings.append(Warning(Warning.Position.HEADER,
                    "System simplifiers caused a timeout and were disabled for this step."))

            # Check for once-simproc fallback (rules limited to fire at most once)
            once_msgs = [m for m in messages if isinstance(m, Simplify_Fallback_Once_Simproc_Msg)]
            if once_msgs:
                self.warnings.append(Warning(Warning.Position.HEADER,
                    "Rewriting rules caused a loop; each rule was limited to fire at most once."))

            # Check for stale targets (selected targets no longer exist in goal)
            stale_msgs = [m for m in messages if isinstance(m, Simplify_Targets_Stale_Msg)]
            for msg in stale_msgs:
                names = ", ".join(msg.discarded_names)
                self.warnings.append(Warning(Warning.Position.HEADER,
                    f"Rewrite targets no longer exist in the current goal. Discarded rules: {names}."))

            # No-op notice: the operation committed (CHANGED_PROP is satisfied
            # whenever the *whole* proof state changes — and with system
            # simplifiers on the full simpset usually normalizes something, so
            # "no progress" is NOT raised) yet the agent's rules touched neither
            # the goal conclusion nor the targeted premises. Without this notice
            # the step renders as just its title and the agent gets no signal.
            # Suppress when stale-target discarding already explained the no-op.
            result_goal = self.resulting_state().leading_goal
            prev_goal = self.ml_state.leading_goal
            goal_unchanged = (result_goal is not None and prev_goal is not None
                              and result_goal.conclusion == prev_goal.conclusion)
            no_new_bindings = self.bindings is None or not (self.bindings[0] or self.bindings[1])
            if goal_unchanged and no_new_bindings and not stale_msgs:
                self.warnings.append(Warning(Warning.Position.HEADER,
                    "The rewrite changed nothing — none of the provided rules matched the "
                    "goal or the targeted premises. Check the rule's orientation and "
                    "instantiation; if you meant to flip an (in)equality, `flip: true` may help."))

        if not is_init:
            if self.bindings != old_bindings:
                self.changed = True
            if self.status.status == EvaluationStatus.Status.SUCCESS and self._my_last_goal is not None:
                new_goal = self.resulting_state().leading_goal
                if new_goal != self._my_last_goal:
                    self.changed = True
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            self._my_last_goal = self.resulting_state().leading_goal

    def _rename_var(self, old_name: varname, new_name: varname) -> 'Node | None':
        if self.bindings is not None:
            for i, var in enumerate(self.bindings[0]):
                if var.external_varname == old_name:
                    self.bindings[0][i] = VariableBinding(var.internal_varname, new_name, var.type)
                    return self
        return super()._rename_var(old_name, new_name)

    def _rename_fact(self, old_name: str, new_name: str) -> 'Node | None':
        if self.bindings is not None:
            for i, fact in enumerate(self.bindings[1]):
                if fact.name == old_name:
                    self.bindings[1][i] = FactBinding(fact.expr, IsaTerm.from_agent(new_name), fact.pretty)
                    return self
        return super()._rename_fact(old_name, new_name)

    def _on_edit_failure(self, outcome: 'EditOutcome') -> 'tuple[EditFailureBehavior, EditOutcome]':
        if self.status.status == EvaluationStatus.Status.FAILURE:
            # Multi-op batches skip auto-revert so the agent sees
            # the failing node and can amend it.
            if len(outcome.request) > 1:
                return super()._on_edit_failure(outcome)
            # Store the blob ABSOLUTE; its `step …` refs and the carried node id
            # are projected to the caller's namespace at render time (the single
            # id-translation boundary, CannotEdit.render). Relativizing here too
            # would double-project a worker's ids.
            file = MyIO(StringIO())
            if self.status.reason:
                file.write(self.status.reason.reason)
            if self.warnings:
                self._print_warnings(0, file, list(Warning.Position))
            outcome.failure = CannotEdit_EvaluationFailed(
                FailureReason(file.getvalue()),
                self.id,
                operation=outcome.operation,
                unapplied_oprs=[],
                is_error=True)
            return (EditFailureBehavior.TERMINATE_AND_REVERT, outcome)
        return super()._on_edit_failure(outcome)


#### Have

class Have_ToolArg(TypedDict):
    thought: str
    statement: Statement
    name: str
    proof: NotRequired[raw_proof | None]
    auto_apply: NotRequired[bool]

@proof_operation("Have", Have_ToolArg)
class Have(StdBlock):
    _is_declarative = True
    _changes_pending_goal = False
    def _nearest_goal_for_subagent(self) -> 'Node | None':
        return self
    def __init__(self, config: NodeConfig, arg : Have_ToolArg,
                 parsed_proof: 'proof | None' = None):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
        self.name = arg["name"]
        self.auto_apply = arg.get("auto_apply", False)
        self._subgoal_level = (0 if self.parent is None
                               else self.parent._subgoal_level + 1)
        self._input_for_any: list[Explicit_Var] = self.statement.get("for_any") or []
        self._input_premises: list[PremiseBinding] = self.statement.get("premises") or []
        # Merged for_any: user-specified + any additional implicit fixes from ML
        self.for_any: list[tuple[varname, typ]] = []
        # Pre-parsed subproof body (list[Parsed_Opr]); consumed by
        # _attach_proof on first refresh.
        self._proof: 'proof | None' = parsed_proof
        the_session().shown_HAVE_fact_names.setdefault(self.name, [])
    def quickview_title(self) -> str:
        return f"Have {self.name}"
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        session = the_session()
        shown = session.shown_HAVE_fact_names
        prev = shown.get(self.name)
        if prev is None:
            if self.for_any:
                names = [name.unicode for name, _ in self.for_any]
                if len(names) == 1:
                    names_str = names[0]
                elif len(names) == 2:
                    names_str = f"{names[0]} and {names[1]}"
                else:
                    names_str = ", ".join(names[:-1]) + f", and {names[-1]}"
                print_indent(indent, file)
                file.write(f"the statement is quantified over {names_str}\n")
            if self._input_premises:
                print_indent(indent, file)
                file.write("assuming:\n")
                for p in self._input_premises:
                    print_indent(indent + 1, file)
                    file.write(f"- {p['name']}: {p['term']}\n")
            print_indent(indent, file)
            file.write(f"proposition: {self.statement['conclusion']}\n")
            shown[self.name] = list(self.for_any)
        elif self.for_any and self.for_any != prev:
            names = [name.unicode for name, _ in self.for_any]
            if len(names) == 1:
                names_str = names[0]
            elif len(names) == 2:
                names_str = f"{names[0]} and {names[1]}"
            else:
                names_str = ", ".join(names[:-1]) + f", and {names[-1]}"
            print_indent(indent, file)
            file.write(f"the statement is quantified over {names_str}\n")
            shown[self.name] = list(self.for_any)
        return indent
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Have\n")
        print_indent(indent, file)
        file.write(f"statement:\n")
        print_indent(indent+1, file)
        file.write(f"english: {self.statement['english']}\n")
        if self.for_any:
            print_indent(indent+1, file)
            file.write("for_any:\n")
            for name, typ in self.for_any:
                print_indent(indent+2, file)
                file.write(f"{name.unicode}: {typ.unicode}\n")
        if self._input_premises:
            print_indent(indent+1, file)
            file.write("premises:\n")
            for p in self._input_premises:
                print_indent(indent+2, file)
                file.write(f"{p['name']}: {p['term']}\n")
        print_indent(indent+1, file)
        file.write(f"conclusion: {self.statement['conclusion']}\n")
        print_indent(indent, file)
        file.write(f"name: {self.name}\n")
        if self.auto_apply:
            print_indent(indent, file)
            file.write("auto_apply: true\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation | None:
        fixes = [(v["name"], v.get("type")) for v in self._input_for_any]
        assumes: list[tuple[str | None, str]] = [(p["name"], p["term"]) for p in self._input_premises]
        return Minilang_Operation.HAVE(
            self.name, fixes, assumes,
            self.statement['conclusion'], self.auto_apply)
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        fail = await super()._refresh_the_beginning_opr()
        if fail is not None:
            return fail
        user_for_any: list[tuple[varname, typ]] = [
            (IsaTerm.from_agent(v["name"]),
             IsaTerm.from_agent(v.get("type") or ""))
            for v in self._input_for_any]
        msgs = [m for m in self._state_after_beginning().messages
                if isinstance(m, Newly_Fixed_Vars_Msg)]
        implicit_for_any = msgs[0].vars if msgs else []
        user_names = {v["name"] for v in self._input_for_any}
        extra = [(n, t) for n, t in implicit_for_any if n.unicode not in user_names]
        self.for_any = user_for_any + extra
        return await self._attach_proof(auto_intro=True)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to claim the intermediate subgoal because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason("Fail to prove this statement because one of the following proof steps fails.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        if self.sub_nodes:
            return FailureReason("Each of the following proof steps above is valid, but the target statement doesn't trivially follow from these steps. Please provide more detailed proof steps.")
        else:
            return FailureReason("The statement is nontrivial. Detailed proofs are required to establish this statement.")
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        for name, typ in self.for_any:
            ret[name] = typ
        return ret
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        for p in self._input_premises:
            ret[IsaTerm.from_agent(p["name"])] = IsaTerm.from_agent(p["term"])
        return ret
    def conditional_fact_statement(self) -> str:
        """The fact this Have exposes to successors, as agent-facing unicode:
        ``(prem1) ⟹ … ⟹ conclusion`` when it carries premises, else the bare
        conclusion. The kernel binds the real conditional fact
        (``⋀fixes. assumes ⟹ shows``, via ``gen_HAVE``); this is its matching
        display form, so a successor (and a constraint-amended worker) sees the
        TRUE, now-conditional, statement rather than the bare conclusion."""
        concl = self.statement['conclusion']
        if not self._input_premises:
            return concl
        # Parenthesise each premise (a premise may itself be an implication, which
        # would otherwise mis-associate); the conclusion stays bare in the final,
        # lowest-precedence position. ⟹ is right-associative, matching Pure.
        parts = [f"({p['term']})" for p in self._input_premises]
        return " ⟹ ".join(parts) + " ⟹ " + concl
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        ret[IsaTerm.from_agent(self.name)] = IsaTerm.from_agent(
            self.conditional_fact_statement())
        return ret
    def can_add_constraints(self) -> bool:
        return True
    async def add_constraints(self, constraints: 'list[PremiseBinding]') -> 'str | None':
        """Append `constraints` as premises of this Have IN PLACE — the named fact
        becomes conditional on them — then re-refresh this node and the downstream
        cascade (`_refresh_all_after_me`, which re-runs downstream consumers of the
        now-conditional fact; a consumer FAILURE there is EXPECTED/intended — it
        surfaces that the consumer now needs the added condition, for the
        dispatcher to fix; NOT auto-repaired here). On a refresh FAILURE of THIS
        node (a bad premise the pre-validation missed), REVERT and return a
        rejection message; the worker survives (SAME object — no replacement, no
        ``aclose``)."""
        if not constraints:
            return None
        saved_input = self._input_premises
        saved_stmt_premises = self.statement.get("premises")
        new_premises = list(self._input_premises) + list(constraints)
        self._input_premises = new_premises
        self.statement["premises"] = new_premises  # keep the two views in sync
        await self._refresh_me_alone(auto_intro=True)
        if self.status.status == EvaluationStatus.Status.FAILURE:
            r = self.status.reason
            reason = r.reason if r is not None else ""
            self._input_premises = saved_input
            if saved_stmt_premises is None:
                self.statement.pop("premises", None)
            else:
                self.statement["premises"] = saved_stmt_premises
            await self._refresh_me_alone(auto_intro=True)
            await self._refresh_all_after_me()
            names = ", ".join(f"`{c['name']}`" for c in constraints)
            tail = f": {reason}" if reason else "."
            return (f"Adding the constraint(s) {names} made step "
                    f"`{the_session()._display_id(self.id)}` ill-formed{tail}")
        await self._refresh_all_after_me()
        return None

#### SetupRewriting

class SetupRewriting_ToolArg(TypedDict):
    thought: str
    for_any: NotRequired[list[Explicit_Var]]
    redex: xterm
    residue: xterm
    conditions: list[PremiseBinding]
    proof: NotRequired[raw_proof | None]

@proof_operation("SetupRewriting", SetupRewriting_ToolArg)
class SetupRewriting(StdBlock):
    _is_declarative = True
    _changes_pending_goal = False
    def _nearest_goal_for_subagent(self) -> 'Node | None':
        return self  # delegatable: a nontrivial rewriting equation has a provable body
    def __init__(self, config: NodeConfig, arg: SetupRewriting_ToolArg,
                 parsed_proof: 'proof | None' = None):
        super().__init__(config, arg["thought"], [])
        self.redex: xterm = arg["redex"]
        self.residue: xterm = arg["residue"]
        self._input_conditions: list[PremiseBinding] = arg.get("conditions") or []
        self._input_for_any: list[Explicit_Var] = arg.get("for_any") or []
        self.for_any: list[tuple[varname, typ]] = []
        self._prev_for_any: list[tuple[varname, typ]] = []
        self._proof: 'proof | None' = parsed_proof
        session = the_session()
        session.setup_rewriting_counter += 1
        self._internal_name = f"setup_rewriting__{session.setup_rewriting_counter}"
    def quickview_title(self) -> str:
        return "SetupRewriting"
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.for_any and self.for_any != self._prev_for_any:
            names = [name.unicode for name, _ in self.for_any]
            if len(names) == 1:
                names_str = names[0]
            elif len(names) == 2:
                names_str = f"{names[0]} and {names[1]}"
            else:
                names_str = ", ".join(names[:-1]) + f", and {names[-1]}"
            print_indent(indent, file)
            file.write(f"the rule is quantified over {names_str}\n")
            self._prev_for_any = self.for_any
        return indent
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: SetupRewriting\n")
        print_indent(indent, file)
        file.write(f"redex: {self.redex}\n")
        print_indent(indent, file)
        file.write(f"residue: {self.residue}\n")
        if self._input_conditions:
            print_indent(indent, file)
            file.write("conditions:\n")
            for p in self._input_conditions:
                print_indent(indent+1, file)
                file.write(f"{p['name']}: {p['term']}\n")
        else:
            print_indent(indent, file)
            file.write("conditions: []\n")
        if self.for_any:
            print_indent(indent, file)
            file.write("for_any:\n")
            for name, typ in self.for_any:
                print_indent(indent+1, file)
                file.write(f"{name.unicode}: {typ.unicode}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation | None:
        fixes = [(v["name"], v.get("type")) for v in self._input_for_any]
        conditions: list[tuple[str | None, str]] = [(p["name"], p["term"]) for p in self._input_conditions]
        return Minilang_Operation.SETUP_REWRITING(
            self._internal_name, fixes, conditions,
            self.redex, self.residue)
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        fail = await super()._refresh_the_beginning_opr()
        if fail is not None:
            return fail
        user_for_any: list[tuple[varname, typ]] = [
            (IsaTerm.from_agent(v["name"]),
             IsaTerm.from_agent(v.get("type") or ""))
            for v in self._input_for_any]
        msgs = [m for m in self._state_after_beginning().messages
                if isinstance(m, Newly_Fixed_Vars_Msg)]
        implicit_for_any = msgs[0].vars if msgs else []
        user_names = {v["name"] for v in self._input_for_any}
        extra = [(n, t) for n, t in implicit_for_any if n.unicode not in user_names]
        self.for_any = user_for_any + extra
        loop_msgs = [m for m in self._state_after_beginning().messages
                     if isinstance(m, SetupRewriting_MayLoop_Msg)]
        if loop_msgs:
            self.warnings.append(Warning(Warning.Position.HEADER,
                "This rewriting rule may cause infinite looping. "
                "Ensure the conditions are strong enough to prevent the rule from firing indefinitely."))
        return await self._attach_proof(auto_intro=True)
    def _beginning_opr_err_msgs(self, err: IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to claim the rewriting rule because: {chr(10).join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child: Node) -> FailureReason:
        return FailureReason("Fail to establish the rewriting rule because one of the following proof steps fails.")
    def _ending_opr_err_msgs(self, err: IsabelleError) -> FailureReason:
        if self.sub_nodes:
            return FailureReason("Each of the following proof steps above is valid, but the rewriting equation doesn't trivially follow from these steps. Please provide more detailed proof steps.")
        else:
            return FailureReason("The rewriting equation is nontrivial. Detailed proofs are required.")
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return ret
    def can_add_constraints(self) -> bool:
        return True
    async def add_constraints(self, constraints: 'list[PremiseBinding]') -> 'str | None':
        """Append `constraints` to this rewriting rule's `conditions` IN PLACE,
        then re-refresh this node and the downstream cascade. On a refresh
        FAILURE (a bad condition the pre-validation missed), REVERT and return a
        rejection message; the worker survives (SAME object). Mirrors
        ``Have.add_constraints`` (conditions ⇒ premises for a rewriting rule)."""
        if not constraints:
            return None
        saved = self._input_conditions
        self._input_conditions = list(self._input_conditions) + list(constraints)
        await self._refresh_me_alone(auto_intro=True)
        if self.status.status == EvaluationStatus.Status.FAILURE:
            r = self.status.reason
            reason = r.reason if r is not None else ""
            self._input_conditions = saved
            await self._refresh_me_alone(auto_intro=True)
            await self._refresh_all_after_me()
            names = ", ".join(f"`{c['name']}`" for c in constraints)
            tail = f": {reason}" if reason else "."
            return (f"Adding the condition(s) {names} made step "
                    f"`{the_session()._display_id(self.id)}` ill-formed{tail}")
        await self._refresh_all_after_me()
        return None

#### Suffices

class Suffices_ToolArg(TypedDict):
    thought: str
    statement: Statement
    proof: NotRequired[raw_proof | None]

@proof_operation("Suffices", Suffices_ToolArg)
class Suffices(StdBlock):
    def _nearest_goal_for_subagent(self) -> 'Node | None':
        return self
    def __init__(self, config: NodeConfig, arg : Suffices_ToolArg,
                 parsed_proof: 'proof | None' = None):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
        self._subgoal_level = (0 if self.parent is None
                               else self.parent._subgoal_level + 1)
        self._input_for_any: list[Explicit_Var] = self.statement.get("for_any") or []
        self._input_premises: list[PremiseBinding] = self.statement.get("premises") or []
        self.for_any: list[tuple[varname, typ]] = []
        self._proof: 'proof | None' = parsed_proof
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        fail = await super()._refresh_the_beginning_opr()
        if fail is not None:
            return fail
        user_for_any: list[tuple[varname, typ]] = [
            (IsaTerm.from_agent(v["name"]),
             IsaTerm.from_agent(v.get("type") or ""))
            for v in self._input_for_any]
        msgs = [m for m in self._state_after_beginning().messages
                if isinstance(m, Newly_Fixed_Vars_Msg)]
        implicit_for_any = msgs[0].vars if msgs else []
        user_names = {v["name"] for v in self._input_for_any}
        extra = [(n, t) for n, t in implicit_for_any if n.unicode not in user_names]
        self.for_any = user_for_any + extra
        return await self._attach_proof(auto_intro=False)
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if not self.sub_nodes and not the_session().showed_suffices_notice:
            print_indent(indent, file)
            file.write("notice: show the provided statement implies the goal\n")
            the_session().showed_suffices_notice = True
        return indent
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Suffices\n")
        print_indent(indent, file)
        file.write(f"statement:\n")
        print_indent(indent+1, file)
        file.write(f"english: {self.statement['english']}\n")
        if self.for_any:
            print_indent(indent+1, file)
            file.write("for_any:\n")
            for name, typ in self.for_any:
                print_indent(indent+2, file)
                file.write(f"{name.unicode}: {typ.unicode}\n")
        if self._input_premises:
            print_indent(indent+1, file)
            file.write("premises:\n")
            for p in self._input_premises:
                print_indent(indent+2, file)
                file.write(f"{p['name']}: {p['term']}\n")
        print_indent(indent+1, file)
        file.write(f"conclusion: {self.statement['conclusion']}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
        if not self.sub_nodes:
            print_indent(indent, file)
            file.write(f"notice: Need to show the provided statement implies the goal\n")
    def beginning_opr(self) -> Minilang_Operation | None:
        fixes = [(v["name"], v.get("type")) for v in self._input_for_any]
        assumes: list[tuple[str | None, str]] = [(p["name"], p["term"]) for p in self._input_premises]
        return Minilang_Operation.SUFFICES(fixes, assumes, self.statement['conclusion'])
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to apply 'it suffices to show' because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason("Fail to prove the implication (sufficient condition implies goal) because one of the following proof steps fails.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        if self.sub_nodes:
            return FailureReason("Each of the following proof steps above is valid, but the implication doesn't trivially follow from these steps. Please provide more detailed proof steps.")
        else:
            return FailureReason("The implication is nontrivial. Detailed proofs are required to establish that the sufficient condition implies the goal.")
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        for name, typ in self.for_any:
            ret[name] = typ
        return ret
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        for p in self._input_premises:
            ret[IsaTerm.from_agent(p["name"])] = IsaTerm.from_agent(p["term"])
        return ret

#### Obtain

class Obtain_ToolArg(TypedDict):
    thought: str
    variables: list[Explicit_Var]
    constraints: list[ConstraintBinding]
    proof: NotRequired[raw_proof | None]

@proof_operation("Obtain", Obtain_ToolArg)
class Obtain(StdBlock):
    _is_declarative = True
    _changes_pending_goal = False
    def _nearest_goal_for_subagent(self) -> 'Node | None':
        return self
    def __init__(self, config: NodeConfig, arg : Obtain_ToolArg,
                 parsed_proof: 'proof | None' = None):
        super().__init__(config, arg["thought"], [])
        self.variables = arg["variables"]
        self.constraints = arg["constraints"]
        self._subgoal_level = (0 if self.parent is None
                               else self.parent._subgoal_level + 1)
        self._proof: 'proof | None' = parsed_proof
        # Populated from `New_Item_Msg` after OBTAIN runs: the vars +
        # facts Isabelle actually fixed, with types inferred by the ML
        # side. Used by `_fixed_*_after_me` so subsequent siblings see
        # them and the parent's pending-goal suppression can hide them
        # rather than re-listing under the pending goal. Preferred over
        # walking `self.variables` / `self.constraints` because (a) the
        # agent may omit an explicit `type:` and ML inference fills it
        # in, and (b) IsaTerm conversion is already done here.
        self._introduced: Context = Context({}, {}, {})
        # Quickview dedup: only re-emit the obtained vars / constraints
        # block when `_introduced` actually changed (mirrors Intro's
        # `_prev_bindings`).
        self._prev_quickview_introduced: Context | None = None
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        for c in self.constraints:
            stmt = c["statement"]
            if stmt.get("_long_form"):
                fixes = [(v["name"], v.get("type") or "") for v in stmt.pop("_for_any", [])]  # type: ignore[misc]
                premises = [p["term"] for p in stmt.pop("_premises", [])]  # type: ignore[misc]
                stmt["isabelle"] = await self.ml_state.concat_statement(fixes, premises, stmt["isabelle"])
                del stmt["_long_form"]  # type: ignore[misc]
        fail = await super()._refresh_the_beginning_opr()
        if fail is not None:
            return fail
        return await self._attach_proof(auto_intro=False)
    async def _refresh_footer(self) -> 'FailureReason | None':
        # `New_Item_Msg` for OBTAIN fires inside CONSIDER'i's CB
        # continuation, which is triggered when the existential's
        # sub-proof completes and the block's END is executed (not
        # during the beginning OBTAIN call). So we read it AFTER the
        # footer has run, on `resulting_state()`.
        fail = await super()._refresh_footer()
        if fail is not None:
            return fail
        self._read_introduced()
        return None
    def _read_introduced(self) -> None:
        msgs = [m for m in self.resulting_state().messages
                if isinstance(m, New_Item_Msg)]
        if msgs:
            self._introduced = msgs[0].items
    async def _skip_proof(self) -> None:
        await super()._skip_proof()
        self._read_introduced()
    def _fixed_vars_after_me(self, ret: Vars) -> Vars:
        ret.update(self._introduced.vars)
        return ret
    def _fixed_tvars_after_me(self, ret: TVars) -> TVars:
        ret.update(self._introduced.tvars)
        return ret
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        ret.update(self._introduced.hyps)
        return ret
    def quickview(self, indent: int, file: MyIO) -> int:
        # After the obtain fires, announce the fresh vars + constraint
        # facts in quickview (mirrors `_print_header`'s full-print
        # listing). Deduped — same dedup idea as Intro's
        # `_prev_bindings`: only re-emit when `_introduced` actually
        # changed.
        indent = super().quickview(indent, file)
        if self._introduced != self._prev_quickview_introduced:
            if self._introduced.vars:
                print_vars(self._introduced.vars.items(), indent, file, {},
                           "obtained variables")
            if self._introduced.tvars:
                print_type_vars(self._introduced.tvars.items(), indent, file, {},
                                "type variables")
            if self._introduced.hyps:
                print_hyps(self._introduced.hyps.items(), indent, file, {},
                           "constraints")
            self._prev_quickview_introduced = self._introduced
        return indent
    def quickview_title(self) -> str:
        names = ", ".join(v["name"] for v in self.variables)
        return f"Obtain {names}"
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Obtain\n")
        print_indent(indent, file)
        file.write(f"variables:\n")
        for v in self.variables:
            print_indent(indent+1, file)
            typ = v.get('type')
            if typ is not None:
                file.write(f"- {v['name']}: {typ}\n")
            else:
                file.write(f"- {v['name']}\n")
        match self.constraints:
            case []:
                pass
            case [constraint]:
                print_indent(indent, file)
                file.write(f"constraint:\n")
                print_indent(indent+1, file)
                file.write(f"name: {constraint['name']}\n")
                print_indent(indent+1, file)
                file.write(f"english: {constraint['statement']['english']}\n")
                print_indent(indent+1, file)
                file.write(f"conclusion: {constraint['statement']['isabelle']}\n")
            case _:
                print_indent(indent, file)
                file.write(f"constraints:\n")
                for constraint in self.constraints:
                    print_indent(indent+1, file)
                    file.write(f"- name: {constraint['name']}\n")
                    print_indent(indent+1, file)
                    file.write(f"  english: {constraint['statement']['english']}\n")
                    print_indent(indent+1, file)
                    file.write(f"  conclusion: {constraint['statement']['isabelle']}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason | None':
        if not self.variables:
            return FailureReason("Must specify at least one variable to obtain.")
        return Minilang_Operation.OBTAIN(self.variables, [(c["name"], c["statement"]["isabelle"]) for c in self.constraints])
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to claim the existential subgoal because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason("Fail to prove the existence of such variables because one of the following proof steps fails.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        if self.sub_nodes:
            return FailureReason("The statement is nontrivial. Detailed proofs are required to establish this statement.")
        else:
            return FailureReason("Each of the following proof steps above is valid, but the target statement doesn't trivially follow from these steps. Please provide more detailed proof steps.")
#### INTRO

class Intro_ToolArg(TypedDict):
    thought: str
    variable_bindings: NotRequired[list[xvarname]]
    fact_bindings: NotRequired[list[xvarname]]

@proof_operation("Intro", Intro_ToolArg)
class Intro(Leaf):
    def __init__(self, config: NodeConfig, thought: str, bindings: Bindings | None = None,
                 _pending_bindings: tuple[list, list] | None = None,
                 _auto_injected: bool = False):
        super().__init__(config, thought)
        self.bindings = bindings
        self.running_time = 0
        self._pending_bindings = _pending_bindings
        self._prev_bindings: Bindings | None = None
        # Provenance: True iff this Intro node was auto-injected by the framework
        # (not written by the agent). Only an explicit Intro may use the silent
        # standard_tac fallback, so it is gated on `not _auto_injected`.
        self._auto_injected = _auto_injected
        # True iff the silent standard_tac fallback rewrote the goal on the last
        # successful refresh; drives the inline "the proof goal has changed to:".
        self._goal_rewritten = False
    @classmethod
    def gen_single(cls, arg: Intro_ToolArg,
                   path: str = "<direct>") -> Parsed_Opr:
        var_bindings = arg.get("variable_bindings") or []
        fact_bindings = arg.get("fact_bindings") or []
        pending = (var_bindings, fact_bindings) if var_bindings or fact_bindings else None
        thought = arg["thought"]
        factory = lambda cfg: Intro(cfg, thought, None, _pending_bindings=pending)
        return Parsed_Opr(cls=cls, factory=factory, raw=arg)

    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.bindings is not None and self.bindings != self._prev_bindings:
            print_var_bindings(self.bindings[0], indent, file, "fixing variables")
            print_fact_bindings(self.bindings[1], indent, file, "assuming premises")
            self._print_goal_rewritten(indent, file)
            self._prev_bindings = self.bindings
        return indent
    def _print_goal_rewritten(self, indent: int, file: MyIO) -> None:
        """When the silent standard_tac fallback rewrote the goal, show the
        resulting goal inline at the node (the rule application was not asked
        for by the agent, so make the new goal explicit)."""
        if not self._goal_rewritten:
            return
        goal = self.resulting_state().leading_goal
        if goal is None:
            return
        print_indent(indent, file)
        file.write("the proof goal has changed to:\n")
        print_indent(indent + 1, file)
        file.write(f"{goal.conclusion.unicode}\n")
    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Intro\n")
        if self.bindings is not None:
            print_var_bindings(self.bindings[0], indent, file, "fixing variables")
            print_fact_bindings(self.bindings[1], indent, file, "assuming premises")
        elif self._pending_bindings is not None:
            var_bindings, fact_bindings = self._pending_bindings
            if var_bindings:
                print_indent(indent, file)
                file.write("fixing variables:\n")
                for v in var_bindings:
                    print_indent(indent + 1, file)
                    file.write(f"- {v}\n")
            if fact_bindings:
                print_indent(indent, file)
                file.write("assuming premises:\n")
                for f in fact_bindings:
                    print_indent(indent + 1, file)
                    file.write(f"- {f}\n")
        self._print_goal_rewritten(indent, file)
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent
    def the_operation(self) -> Minilang_Operation:
        return Minilang_Operation.INTRO(self.bindings, not self._auto_injected)
    async def _refresh_me_alone(self, auto_intro: bool):
        is_init = self._first_time
        if self._pending_bindings is not None:
            var_bindings, fact_bindings = self._pending_bindings
            self.bindings = await self.ml_state.compute_bindings(
                [IsaTerm.from_agent(n) for n in var_bindings],
                [IsaTerm.from_agent(n) for n in fact_bindings])
            self._pending_bindings = None
        old_bindings = self.bindings
        await super()._refresh_me_alone(auto_intro)
        self._goal_rewritten = False
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            self.running_time += 1
            messages = self.resulting_state().messages
            self._goal_rewritten = any(isinstance(m, Intro_Standardized_Msg) for m in messages)
            intro_bindings_msgs = [m for m in messages if isinstance(m, Intro_Bindings_Msg)]
            match intro_bindings_msgs:
                case [intro_bindings_msg]:
                    pass
                case _:
                    raise InternalError(
                        f"Expected exactly one Intro_Bindings_Msg in Intro's messages, got {len(intro_bindings_msgs)}"
                    )
            self.bindings = intro_bindings_msg.final
            if self.running_time >= 2:
                if intro_bindings_msg.missing[0]:
                    varnames = [v.external_varname for v in intro_bindings_msg.missing[0]]
                    vstr = titled_string_of_and_list(varnames, "variable", "variables")
                    self.warnings.append(Warning(Warning.Position.HEADER,
                        f"The proof goal has changed. Tracking of the {vstr} has been lost."))
                # TODO: under partial Intro bindings, auto_introduced[0]/[1]
                # also includes trailing vars/prems the agent deliberately
                # left unbound. The "new ... occur" wording misleads on
                # goal-change re-refresh. Fix by diffing against the prior
                # refresh's quantifier count rather than matched-names set.
                if intro_bindings_msg.auto_introduced[0]:
                    def print(indent: int, file: MyIO) -> int:
                        print_indent(indent, file)
                        file.write(f"- The proof goal has changed and new universally quantified variables occur:\n")
                        for binding in intro_bindings_msg.auto_introduced[0]:
                            print_indent(indent+1, file)
                            if binding.external_varname == binding.internal_varname:
                                file.write(f"- {binding.external_varname.unicode}\n")
                            else:
                                file.write(f"- {binding.internal_varname.unicode}, renamed to {binding.external_varname.unicode} to prevent name conflicts\n")
                        return indent
                    self.warnings.append(Warning(Warning.Position.HEADER, print))
                if intro_bindings_msg.missing[1]:
                    premises = [v.name for v in intro_bindings_msg.missing[1]]
                    pstr = titled_string_of_and_list(premises, "premise", "premises")
                    self.warnings.append(Warning(Warning.Position.HEADER,
                        f"The proof goal has changed. Tracking of the {pstr} has been lost."))
                if intro_bindings_msg.auto_introduced[1]:
                    def print(indent: int, file: MyIO) -> int:
                        print_indent(indent, file)
                        file.write(f"- The proof goal has changed and new premises occur:\n")
                        for binding in intro_bindings_msg.auto_introduced[1]:
                            print_indent(indent+1, file)
                            file.write(f"- {binding.name.unicode}\n")
                        return indent
                    self.warnings.append(Warning(Warning.Position.HEADER, print))
        if not is_init:
            if self.bindings != old_bindings:
                self.changed = True
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        if self.bindings is not None:
            for var in self.bindings[0]:
                ret[var.external_varname] = var.type
        return ret
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        if self.bindings is not None:
            for fact in self.bindings[1]:
                ret[fact.name] = fact.pretty
        return ret
    def _fixed_vars_after_me(self, ret: Vars) -> Vars:
        return self._fixed_vars_at_me(ret)
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return self._fixed_facts_at_me(ret)
    def _rename_var(self, old_name: varname, new_name: varname) -> 'Node | None':
        if self.bindings is not None:
            for i, var in enumerate(self.bindings[0]):
                if var.external_varname == old_name:
                    self.bindings[0][i] = VariableBinding(var.internal_varname, new_name, var.type)
                    return self
        return super()._rename_var(old_name, new_name)
    def _rename_fact(self, old_name: str, new_name: str) -> 'Node | None':
        if self.bindings is not None:
            for i, fact in enumerate(self.bindings[1]):
                if fact.name == old_name:
                    self.bindings[1][i] = FactBinding(fact.expr, IsaTerm.from_agent(new_name), fact.pretty)
                    return self
        return super()._rename_fact(old_name, new_name)


#### SplitConjs

class SplitConjs_ToolArg(TypedDict):
    thought: str
    proofs: NotRequired[list[raw_proof] | None]

@proof_operation("SplitConjs", SplitConjs_ToolArg)
class SplitConjs(SubgoalMaker):
    def __init__(self, config: NodeConfig, thought: str,
                 parsed_proofs: 'list[proof] | None' = None):
        super().__init__(config, thought, [])
        if parsed_proofs is not None:
            self._supplied_proofs = {
                str(i + self._initial_goal_index): (None, p)
                for i, p in enumerate(parsed_proofs)
            }
    @classmethod
    def gen_single(cls, arg: SplitConjs_ToolArg,
                   path: str = "<direct>") -> Parsed_Opr:
        parsed_proofs = _parse_positional_proofs(
            arg.get("proofs"), f"{path}.proofs")
        thought = arg["thought"]
        return Parsed_Opr(
            cls=cls, factory=lambda cfg: cls(cfg, thought, parsed_proofs),
            raw=arg)
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: SplitConjs\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.SPLIT_CONJS()
    def _beginning_opr_err_msgs(self, err: IsabelleError) -> FailureReason:
        return FailureReason(f"Failed to split conjunctive goal: {'\n'.join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child: Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err: IsabelleError) -> FailureReason:
        raise InternalError("A SplitConjs doesn't have an ending operation")
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, indent-1)
        else:
            return ("goals", indent+1)
    def _all_fixed_facts_before_a_child(self, child: Node, ret: Hyps) -> Hyps:
        self._all_fixed_facts_before_me(ret)
        self._fixed_facts_at_me(ret)
        _COMMENTED = EvaluationStatus.Status.COMMENTED
        for c in self.sub_nodes:
            if c is child:
                return ret
            elif isinstance(c, GoalNode):
                for gc in c.sub_nodes:
                    if gc.status.status != _COMMENTED:
                        gc._fixed_facts_after_me(ret)
            elif c.status.status != _COMMENTED:
                c._fixed_facts_after_me(ret)
        raise InternalError("The target node is not my children")
    def _all_fixed_vars_before_a_child(self, child: Node, ret: Vars) -> Vars:
        self._all_fixed_vars_before_me(ret)
        self._fixed_vars_at_me(ret)
        _COMMENTED = EvaluationStatus.Status.COMMENTED
        for c in self.sub_nodes:
            if c is child:
                return ret
            elif isinstance(c, GoalNode):
                for gc in c.sub_nodes:
                    if gc.status.status != _COMMENTED:
                        gc._fixed_vars_after_me(ret)
            elif c.status.status != _COMMENTED:
                c._fixed_vars_after_me(ret)
        raise InternalError("The target node is not my children")
    def _all_fixed_tvars_before_a_child(self, child: Node, ret: TVars) -> TVars:
        self._all_fixed_tvars_before_me(ret)
        self._fixed_tvars_at_me(ret)
        _COMMENTED = EvaluationStatus.Status.COMMENTED
        for c in self.sub_nodes:
            if c is child:
                return ret
            elif isinstance(c, GoalNode):
                for gc in c.sub_nodes:
                    if gc.status.status != _COMMENTED:
                        gc._fixed_tvars_after_me(ret)
            elif c.status.status != _COMMENTED:
                c._fixed_tvars_after_me(ret)
        raise InternalError("The target node is not my children")


#### InferenceRule

class InferenceRule_ToolArg(TypedDict):
    thought: str
    rule: FactByName | FactByDescription | None
    proofs: NotRequired[list[raw_proof] | None]
    # TODO: write some skills telling the agent how to associate common operations (e.g., proof by contradiction, proof by cases, etc.) with the inference rules

@proof_operation("InferenceRule", InferenceRule_ToolArg)
class InferenceRule(SubgoalMaker):
    def __init__(self, config: NodeConfig, arg: InferenceRule_ToolArg,
                 parsed_proofs: 'list[proof] | None' = None):
        super().__init__(config, arg["thought"], [])
        self.rule: FactByName | FactByDescription | None = arg["rule"]
        self.rule_ref: IsabelleFact | None = None
        self._opening = False
        self._prev_quickview_derived_goal: term | None = None
        # Latches after one auto-convert probe so re-refreshes don't re-run it;
        # reset on upstream change (see _on_upstream_change).
        self._autoconvert_tried = False
        if parsed_proofs is not None:
            self._supplied_proofs = {
                str(i + self._initial_goal_index): (None, p)
                for i, p in enumerate(parsed_proofs)
            }

    @classmethod
    def gen_single(cls, arg: InferenceRule_ToolArg,
                   path: str = "<direct>") -> Parsed_Opr:
        """Non-splice path (positional `proofs`, or no `proofs`):
        parse `proofs` into `list[proof]` and hand to the ctor."""
        parsed_proofs = _parse_positional_proofs(
            arg.get("proofs"), f"{path}.proofs")
        return Parsed_Opr(
            cls=cls, factory=lambda cfg: cls(cfg, arg, parsed_proofs),
            raw=arg)

    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        if self.rule is not None and self.rule_ref is None:
            fetched = await self.ml_state.fetch_facts([self.rule])
            result = fetched[0]
            if isinstance(result, IsabelleFact):
                self.rule_ref = result
            else:
                # FactByDescription → delegate to a sub-agent
                selected = await the_session().launch_interaction(result)
                if selected:
                    self.rule_ref = selected[0]
                else:
                    self.rule_ref = IsabelleFact_Unfound(self.rule)
        elif not isinstance(self.rule_ref, (type(None), IsabelleFact_Unfound)) and self.ml_state.initialized():
            [self.rule_ref] = await self.ml_state.refresh_facts([self.rule_ref])
        await super()._refresh_me_alone(auto_intro)
        # Fresh-fill InferenceRule that failed its RULE op but whose rule works as
        # a goal rewrite → self-replace with a genuine Rewrite. Only when the parent
        # refresh is replace-aware (flag set by `_refresh_child_replace_aware`, the
        # same frame that catches NodeReplaced), so the raise never leaks.
        # `not sub_nodes` restricts to first-execution (never opened subgoals),
        # excluding the dangerous previously-succeeded re-refresh.
        if (self.status.status == EvaluationStatus.Status.FAILURE
                and not self.sub_nodes
                and not self._autoconvert_tried
                and isinstance(self.parent, NonLeaf_Node)
                and self.parent._child_replace_enabled):
            self._autoconvert_tried = True
            new = await self._autoconvert_to_rewrite()
            if new is not None:
                raise NodeReplaced(new)
    def _on_upstream_change(self) -> None:
        super()._on_upstream_change()
        # Upstream changed → a prior "not a rewrite" probe result is stale; allow
        # one fresh auto-convert attempt next time this node is refreshed.
        self._autoconvert_tried = False
    def _rule_name_str(self) -> str | None:
        if self.rule_ref is not None:
            return self.rule_ref.name().unicode
        if self.rule is not None and "name" in self.rule:
            return self.rule["name"]
        return None
    def _is_induction_rule(self) -> bool:
        name = self._rule_name_str()
        return name is not None and (name.endswith("_ind") or name.endswith("_induct"))
    def _print_induction_notice(self, indent: int, file: MyIO):
        if self._is_induction_rule():
            print_indent(indent, file)
            file.write(f"Notice: \"{self._rule_name_str()}\" is an induction rule. Use `Induction` operation with `rule: {self._rule_name_str()}` instead.\n")
    def quickview_title(self) -> str:
        if isinstance(self.rule_ref, IsabelleFact_Presented):
            return f"Inference Rule {self.rule_ref.short_name.unicode}"
        return "Inference Rule"
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        self._print_induction_notice(indent, file)
        if len(self.sub_nodes) <= 1:
            s0 = self._state_after_beginning()
            goal = s0.leading_goal
            if goal is not None:
                conclusion = goal.conclusion
                if conclusion != self._prev_quickview_derived_goal:
                    conclusion_str = conclusion.unicode
                    if len(conclusion_str) > AGENT_GOAL_CHAR_LIMIT:
                        conclusion_str = _trunc_expr_base(conclusion_str, AGENT_GOAL_CHAR_LIMIT)
                    print_indent(indent, file)
                    file.write(f"derived goal: {conclusion_str}\n")
                    self._prev_quickview_derived_goal = conclusion
        return indent
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Inference Rule\n")
        print_indent(indent, file)
        if self.rule_ref is not None:
            file.write("rule:\n")
            self.rule_ref.print(indent+1, file)
        elif self.rule is not None:
            file.write("rule:\n")
            _print_raw_fact(self.rule, indent+1, file)
        else:
            file.write("rule: default\n")
        self._print_induction_notice(indent, file)
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
        if len(self.sub_nodes) <= 1:
            s0 = self._state_after_beginning()
            goal = s0.leading_goal
            if goal is not None:
                print_indent(indent, file)
                file.write("derived goal:\n")
                print_goal(goal, indent+1, False, file, self._ctxt_before_me())
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason':
        if isinstance(self.rule_ref, IsabelleFact_Unfound):
            return FailureReason(f"Inference rule fact \"{self.rule_ref.name().unicode}\" not found")
        return Minilang_Operation.RULE(self.rule_ref, self._post_insts)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        # The ML RULE operator already emits its own "Fail to apply the rules."
        # header; only prepend our node-level one when it didn't, to avoid a
        # duplicated near-identical prefix line.
        if any(e.startswith("Fail to apply") for e in err.errors):
            parts = list(err.errors)
        else:
            parts = ["Fail to apply the inference rule.", *err.errors]
        goal = self.ml_state.leading_goal
        if goal is not None and not any("current proof goal" in e for e in err.errors):
            parts.append(f"The current proof goal is:\n  {goal.conclusion.unicode}")
        return FailureReason("\n".join(parts))
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("An InferenceRule doesn't have an ending operation")
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, indent-1)
        else:
            return ("derived subgoals", indent+1)
    async def _rewrite_trial(self) -> bool:
        """Probe whether `self.rule_ref` works as a goal-only rewrite: run a
        throwaway SIMPLIFY on a fresh scratch state and accept if the goal is
        solved or merely changed (its LHS matched). Only called for non-looping
        rules (a looping rule's SIMPLIFY could itself loop/error). `log=False`:
        the probe must leave no record in the live proof-op log."""
        assert isinstance(self.rule_ref, IsabelleFact_Presented)
        op = Minilang_Operation.SIMPLIFY([(self.rule_ref, None)], False, [], True, None)
        try:
            scratch = await self.ml_state.execute(op, None, log=False)
        # `execute` raises InternalError (not IsabelleError) on
        # beginning_state_not_found / >1 Goals_Msg by design (internal-invariant
        # guards, not transient faults); for the probe both equally mean "not a
        # usable rewrite", so catch alongside IsabelleError.
        except (IsabelleError, InternalError):
            return False
        try:
            g0 = self.ml_state.leading_goal
            return (scratch.leading_goal is None
                    or (g0 is not None
                        and scratch.leading_goal.conclusion != g0.conclusion))
        finally:
            if scratch._initialized:
                await scratch.reset()

    async def _autoconvert_to_rewrite(self) -> 'Node | None':
        """Caller guarantees `self` failed its RULE op. If `self` is fresh-fill
        (no opened subgoals) and its rule works as a goal rewrite, swap `self` in
        place for a genuine Rewrite node and return it; else return None.

        Swaps and refreshes ONLY the new node (no sibling cascade) — each caller
        drives its own single cascade afterwards, so converting never
        double-cascades siblings. Fresh-fill scope (RULE fails before opening
        subgoals → empty sub_nodes) sidesteps sub-agent/teardown hazards.
        See `_inference_rule_rewrite_fallback_plan.md`."""
        if self.sub_nodes:                  # only fresh-fill (no opened subgoals)
            return None
        if not isinstance(self.rule_ref, IsabelleFact_Presented):
            return None
        if self.parent is None:
            return None
        # Applicability. A self-looping rule IS a rewrite rule (the live Rewrite
        # will ask the agent to pick targets), so accept it without the probe —
        # whose SIMPLIFY could loop/error. Otherwise probe by running it once. Any
        # probe error leaves the original RULE failure intact, never crashing the edit.
        try:
            looping = await self.ml_state.check_looping_rules(
                [self.rule_ref.pack()[0]], True, [])
        except (IsabelleError, InternalError):
            return None
        if not looping and not await self._rewrite_trial():
            return None
        # Build a *genuine* Rewrite referencing the same theorem. Reuse the
        # agent's original FactByName when it had one (exact instantiations
        # preserved); else the resolved full name with baked attributes. `using`
        # stays None at construction so the node runs the normal resolve +
        # looping-target interaction path identically to a hand-authored Rewrite.
        rule = self.rule
        if rule is not None and "name" in rule:
            using_ref: 'FactByName' = cast('FactByName', rule)
        else:
            using_ref = FactByName(name=self.rule_ref.pack()[0])
        parent = self.parent
        idx = parent.sub_nodes.index(self)
        rw = Rewrite.gen_single({
            "thought": self.thought,
            "using": [using_ref],
            "use system simplifiers": False,
            "rewrite goal": True,
            "rewrite premises": [],
        })
        config = NodeConfig(self.local_step, await self.ml_state.clone(None), parent)
        new = rw.factory(config)
        new._was_autoconverted = True  # type: ignore[attr-defined]  — Rewrite; narrowing erased by @proof_operation
        parent.sub_nodes[idx] = new
        await new._refresh_me_alone(auto_intro=True)
        if new.status.status == EvaluationStatus.Status.FAILURE:
            # Live execution diverged from the probe — restore the original failure.
            parent.sub_nodes[idx] = self
            return None
        return new

### Contradiction

class Contradiction_ToolArg(TypedDict):
    hypothesis_name: str

@proof_operation("Contradiction", Contradiction_ToolArg)
class Contradiction(Leaf):
    def __init__(self, config: NodeConfig, arg: Contradiction_ToolArg):
        super().__init__(config, "")
        self.hypothesis_name: str = arg["hypothesis_name"]
        self.bindings: Bindings | None = None
        self._prev_bindings: Bindings | None = None

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        return Minilang_Operation.CONTRADICTION(self.hypothesis_name)

    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        await super()._refresh_me_alone(auto_intro)
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            intro_msgs = [m for m in self.resulting_state().messages
                          if isinstance(m, Intro_Bindings_Msg)]
            if intro_msgs:
                self.bindings = intro_msgs[0].final

    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        if self.bindings is not None:
            for fact in self.bindings[1]:
                ret[fact.name] = fact.pretty
        return ret

    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return self._fixed_facts_at_me(ret)

    def quickview_title(self) -> str:
        return f"Contradiction (hypothesis: {self.hypothesis_name})"

    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.bindings is not None and self.bindings != self._prev_bindings:
            print_fact_bindings(self.bindings[1], indent, file, "assuming hypothesis")
            self._prev_bindings = self.bindings
        return indent

    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        print_indent(indent, file)
        file.write("operation: Contradiction\n")
        print_indent(indent, file)
        file.write(f"hypothesis_name: {self.hypothesis_name}\n")
        if self.bindings is not None:
            print_fact_bindings(self.bindings[1], indent, file, "assuming hypothesis")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

### Branch

class Branch_Case_ToolArg(TypedDict):
    name: xname
    statement: ShortStatement
    proof: NotRequired[raw_proof | None]

@validator(Branch_Case_ToolArg)
def _validate_branch_case(data: Any, path: str) -> Branch_Case_ToolArg:
    if not isinstance(data, dict):
        raise ArgumentError({}, f"{path}: expected an object, got {type(data).__name__}")
    if "name" not in data and isinstance(data.get("statement"), dict) and "name" in data["statement"]:
        data["name"] = data["statement"].pop("name")
    return _validate_typed_dict(Branch_Case_ToolArg, data, path)
class Branch_ToolArg(TypedDict):
    thought: str
    cases: list[Branch_Case_ToolArg]
#class Branch_ToolArg(TypedDict):
#    thought: str
#    cases: list[NamedStatement]

@proof_operation("Branch", Branch_ToolArg)
class Branch(SubgoalMaker):
    def __init__(self, config: NodeConfig, arg: Branch_ToolArg,
                 parsed_cases: 'list[proof | None] | None' = None):
        super().__init__(config, arg["thought"], [])
        self.cases = arg["cases"]
        self._initial_goal_index = 0
        if parsed_cases is not None:
            self._supplied_proofs = {
                str(i + 1): (None, p) for i, p in enumerate(parsed_cases)
                if p is not None
            } or None
    @classmethod
    def gen_single(cls, arg: Branch_ToolArg,
                   path: str = "<direct>") -> Parsed_Opr:
        arg = cls._validate_arg(arg, path)
        cases = arg.get("cases")
        if not isinstance(cases, list):
            raise ArgumentError(arg,
                f"{path}.cases: expected an array, "
                f"got {type(cases).__name__}")
        parsed_cases: list[proof | None] = []
        for ci, case in enumerate(cases):
            case_path = f"{path}.cases[{ci}]"
            if not isinstance(case, dict):
                raise ArgumentError(arg,
                    f"{case_path}: expected an object, got "
                    f"{type(case).__name__}")
            parsed_cases.append(
                _parse_optional_raw_proof(case.get("proof"), f"{case_path}.proof"))
        return Parsed_Opr(
            cls=cls, factory=lambda cfg: cls(cfg, arg, parsed_cases),
            raw=arg)
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ('cases', indent+1)
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Branch\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason':
        if not self.cases:
            return FailureReason("Must specify at least one branching case.")
        return Minilang_Operation.BRANCH([(case["name"], case["statement"]["isabelle"]) for case in self.cases])
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to anlysis the proof goal by cases because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Branch doesn't have an ending operation")
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        for case in self.cases:
            stmt = case["statement"]
            if stmt.get("_long_form"):
                fixes = [(v["name"], v.get("type") or "") for v in stmt.pop("_for_any", [])]  # type: ignore[misc]
                premises = [p["term"] for p in stmt.pop("_premises", [])]  # type: ignore[misc]
                stmt["isabelle"] = await self.ml_state.concat_statement(fixes, premises, stmt["isabelle"])
                del stmt["_long_form"]  # type: ignore[misc]
        fail = await super()._refresh_the_beginning_opr()
        if fail is None:
            if not self.sub_nodes[0].thought:
                self.sub_nodes[0].thought = "We first show exhaustiveness of the case split"
        return fail

### CaseSplit

# Rule field on CaseSplit and Induction uses the same shape:
#   Literal["default"] | FactByName | FactByDescription
# "default" = let Isabelle auto-pick; FactByName = specific rule;
# FactByDescription = trigger a semantic retrieval interaction at refresh
# time (constrained to CASE_SPLIT_RULE / INDUCTION_RULE kind).

class Proof_PerCase(TypedDict):
    """One entry in the `proofs` list of CaseSplit / Induction.  `case_name`
    names one of the Isabelle cases produced by the rule (matched at runtime
    against `Consider_Case_Msg.case` / `GoalNode.local_step`); `body` is the
    ordered list of sub-operations applied to that case's GoalNode."""
    case_name: str
    body: raw_proof


class CaseSplit_ToolArg(TypedDict):
    thought: str
    target_isabelle_term: xterm
    rule: NotRequired[Literal["default"] | FactByName | FactByDescription]
    proofs: NotRequired[list[Proof_PerCase] | None]
    simplify: NotRequired[bool]

@proof_operation("CaseSplit", CaseSplit_ToolArg)
class CaseSplit(CaseSplit_Like):
    _case_kind = "case-split"

    def __init__(self, config: NodeConfig, arg: CaseSplit_ToolArg,
                 proofs_by_case: 'dict[str, proof_with_case_vars] | None' = None):
        super().__init__(config, arg["thought"], [])
        self.target_isabelle_term = arg["target_isabelle_term"]
        self.rule_spec: 'Literal["default"] | FactByName | FactByDescription' = \
            arg.get("rule", "default")
        self._supplied_proofs = proofs_by_case
        self.no_simp: bool = not arg.get("simplify", True)
    def quickview_title(self) -> str:
        return f"CaseSplit {self.target_isabelle_term}"
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: CaseSplit\n")
        print_indent(indent, file)
        file.write(f"target term: {self.target_isabelle_term}\n")
        super()._print_header(indent, file)
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.CASE_SPLIT(
            self.target_isabelle_term,
            cast(list[varname_spec] | None, self._case_vars_of_child(0)),
            self._resolved_rule_str,
            self.no_simp,
            self._post_insts)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Case analysis failed because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Branch doesn't have an ending operation")
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        if not self._rule_resolved:
            fail = await self._resolve_rule(
                self.rule_spec, self.target_isabelle_term, [], "case-split")
            if fail is not None:
                return fail
        return await super()._refresh_the_beginning_opr()

### Induction

class Induction_ToolArg_Variable(TypedDict):
    name: xvarname
    status: Literal["fixed", "generalized"]
class Induction_ToolArg(TypedDict):
    thought: str
    target_isabelle_term: xterm
    rule: NotRequired[Literal["default"] | FactByName | FactByDescription]
    variables: list[Induction_ToolArg_Variable]
    IH_facts: NotRequired[list[FactByName]]
    proofs: NotRequired[list[Proof_PerCase] | None]
    simplify: NotRequired[bool]

@proof_operation("Induction", Induction_ToolArg)
class Induction(CaseSplit_Like):
    _case_kind = "induction"

    def __init__(self, config: NodeConfig, arg: Induction_ToolArg,
                 proofs_by_case: 'dict[str, proof_with_case_vars] | None' = None):
        super().__init__(config, arg["thought"], [])
        self.arg = arg
        self.target_isabelle_term = arg["target_isabelle_term"]
        self.rule_spec: 'Literal["default"] | FactByName | FactByDescription' = \
            arg.get("rule", "default")
        self.variables = arg["variables"]
        # Agent-supplied local facts that should be generalized alongside
        # the `arbitrary` variables (routed into induct_facts.insertion on
        # the ML side). Raw list is kept so refresh can re-validate after
        # amend; resolved refs hold only the surviving local facts that
        # mention at least one generalized variable.
        self._raw_facts_to_generalize: list[FactByName] = [
            f for f in (arg.get("IH_facts") or []) if f is not None]
        self.fact_refs_to_generalize: list[IsabelleFact_Presented] = []
        self._supplied_proofs = proofs_by_case
        self.no_simp: bool = not arg.get("simplify", True)
        # internal (skolem) name -> external name, for each variable this
        # induction generalizes away. Re-derived each refresh from the
        # DISCARDED_VARS message; consulted by `_collect_discarded_vars` to
        # resolve `the out-of-scope variable <internal>` in later error messages.
        self._discarded_vars: dict[str, str] = {}
    def quickview_title(self) -> str:
        return f"Induction {self.target_isabelle_term}"
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        is_init = self._first_time
        old_variables = list(self.variables)
        old_gen_fact_names = [r.full_name for r in self.fact_refs_to_generalize]
        try:
            _, frees, _ = await self.ml_state.check_term(self.target_isabelle_term)
        except InternalError_UnparsedTerm as e:
            return FailureReason(
                f"Syntax error in induction target `{e.term}`: {e.reason}")
        # Free variables appearing in the induction target must not be
        # passed as `arbitrary:` to the ML induction tactic — this triggers
        # a degenerate HO-unification solution that yields an IH with
        # schematic variables disconnected from the induction case variable
        # (see Test/Induct_HO_Unif_Probe.thy and the Induction_AmendTargetFree
        # regression). The stripping is unconditional: the ML contract
        # forbids target-in-arbitrary on both fresh fill and amend.
        self.variables[:] = [var for var in self.variables if IsaTerm.from_agent(var["name"]) not in frees]
        if not self._rule_resolved:
            await self._classify_unclassified_vars(frees)
            arbitrary = [v["name"] for v in self.variables if v["status"] == "generalized"]
            fail = await self._resolve_rule(
                self.rule_spec, self.target_isabelle_term, arbitrary, "induction")
            if fail is not None:
                return fail
        await self._resolve_facts_to_generalize()
        fail = await super()._refresh_the_beginning_opr()
        if fail is None:
            self._discarded_vars = {
                internal: external
                for m in self._state_after_beginning().messages
                if isinstance(m, Discarded_Vars_Msg)
                for (internal, external) in m.pairs}
            for m in self._state_after_beginning().messages:
                if isinstance(m, Induction_Dropped_Facts_Msg):
                    def _strip_local(n: str) -> str:
                        return n.removeprefix("local.")
                    name_to_ref = {_strip_local(r.full_name): r
                                   for r in self.fact_refs_to_generalize}
                    for n in m.dropped_names:
                        ref = name_to_ref.get(n)
                        display = ref.short_name.unicode if ref is not None else n
                        self.warnings.append(Warning(
                            Warning.Position.HEADER,
                            f"Fact `{display}` in `IH_facts` does not mention any "
                            f"generalized variable; it would not be affected by induction — skipped."))
                    dropped_set = set(m.dropped_names)
                    self.fact_refs_to_generalize = [
                        r for r in self.fact_refs_to_generalize
                        if _strip_local(r.full_name) not in dropped_set]
            vars = self._all_fixed_vars_before_me({})
            _, frees, _ = await self.ml_state.check_term(self.target_isabelle_term)
            # Remove free variables appearing in target_isabelle_term from vars
            for v in frees:
                if v in vars:
                    del vars[v]
            var_names_as_isa = [IsaTerm.from_agent(var["name"]) for var in self.variables]
            # Unclassified in-scope vars are now resolved up front by the
            # pre-flight `_classify_unclassified_vars` Interaction (which asks
            # the agent which to generalize), so `new_var_names` is normally
            # empty here. The default-to-fixed below is kept purely as a
            # silent safety net for any var that escapes that classification;
            # no warning is emitted (the agent was already asked).
            new_var_names = [v for v in vars if v not in var_names_as_isa]
            not_used_vars = [var["name"] for var in self.variables if IsaTerm.from_agent(var["name"]) not in vars]
            if not_used_vars:
                msg = (
                    f"This induction operation specifies unused "
                    f"{titled_string_of_and_list(not_used_vars, 'variable', 'variables')} "
                    "; they are removed."
                )
                self.warnings.append(Warning(Warning.Position.HEADER, msg))
            if not_used_vars:
                self.variables[:] = [var for var in self.variables if var["name"] not in not_used_vars]
            if new_var_names:
                self.variables.extend({"name": v.unicode, "status": "fixed"} for v in new_var_names)
        if not is_init and self.variables != old_variables:
            self.changed = True
        new_gen_fact_names = [r.full_name for r in self.fact_refs_to_generalize]
        if not is_init and new_gen_fact_names != old_gen_fact_names:
            self.changed = True
        return fail
    async def _resolve_facts_to_generalize(self) -> None:
        """Fetch `facts_to_generalize` entries, filter unfound/global ones
        (with warnings), and pass all surviving local candidates through
        to INDUCT. The ML-side dirty-var filter (proof.ML) will drop
        irrelevant facts and report them via DROPPED_INSERTION_FACTS."""
        self.fact_refs_to_generalize = []
        if not self._raw_facts_to_generalize:
            return
        fetched = cast(list[IsabelleFact],
                       await self.ml_state.fetch_facts(self._raw_facts_to_generalize))
        for f in fetched:
            if isinstance(f, IsabelleFact_Unfound):
                self.warnings.append(Warning(
                    Warning.Position.HEADER,
                    f"Fact `{f.name().unicode}` in `IH_facts` was not found; skipped."))
            elif isinstance(f, IsabelleFact_Presented):
                if not f.is_local:
                    self.warnings.append(Warning(
                        Warning.Position.HEADER,
                        f"Fact `{f.short_name.unicode}` in `IH_facts` is a global "
                        f"theorem; only local proof-context facts can be carried through "
                        f"induction — skipped."))
                else:
                    self.fact_refs_to_generalize.append(f)
    async def _classify_unclassified_vars(self, frees: Vars) -> None:
        """Pre-flight: when the agent left in-scope variables unclassified
        (neither fixed nor generalized), ask which to generalize via
        `Interaction_ClassifyInductionVars`. Selected vars are appended as
        `generalized`, the rest as `fixed`. Runs BEFORE `arbitrary` is
        computed (under the `_rule_resolved` gate, so once per node;
        re-prompted on amend) so the choice flows into the induction tactic,
        rule analysis, and the IH-fact picker's `dvars`. Only variables that
        actually appear in the leading goal (premises ⟹ conclusion) are
        offered — fetched via the `IsaMini.goal_variables` callback — so the
        lemma's fixed signature and other in-scope-but-irrelevant variables are
        not surfaced. Target frees are excluded — they cannot be generalized as
        `arbitrary:`."""
        vars = self._all_fixed_vars_before_me({})
        for v in frees:
            if v in vars:
                del vars[v]
        listed = [IsaTerm.from_agent(var["name"]) for var in self.variables]
        goal_var_names = set(await self.ml_state.connection.callback(
            "IsaMini.goal_variables", self.ml_state.name))
        unclassified = [(name, typ) for name, typ in vars.items()
                        if name not in listed and name.unicode in goal_var_names]
        if not unclassified:
            return
        to_generalize = await the_session().launch_interaction(
            Interaction_ClassifyInductionVars(
                [(name.unicode, typ.unicode) for name, typ in unclassified]))
        gen_set = set(to_generalize)
        for name, _ in unclassified:
            status = "generalized" if name.unicode in gen_set else "fixed"
            self.variables.append({"name": name.unicode, "status": status})
    async def _choose_ih_facts(self, candidates: list[tuple[str, str]],
                               dvars: list[str]) -> None:
        """Pre-flight: offer the in-scope facts mentioning the relevant vars
        (`dvars` = induction target frees ∪ generalized) and let the agent pick
        which to carry into the induction hypothesis. Picks SUPPLEMENT the
        agent-supplied `facts_to_generalize` (unioned into
        `_raw_facts_to_generalize`, which `_resolve_facts_to_generalize` then
        resolves). Candidate names are the standard local-fact names (incl.
        indexed `h(i)` for a multi-thm fact); facts already supplied are not
        re-offered — and a bare supplied `h` subsumes every offered `h(i)`."""
        if not candidates:
            return
        def _norm(name: 'str | None') -> str:
            # Local-fact names arrive bare; agent-supplied ones may carry a
            # `local.` prefix — normalise both before comparing.
            return (name or "").removeprefix("local.")
        def _split(name: str) -> 'tuple[str, int | None]':
            # Standard indexed fact name `base(i)` (1-based); idx None if plain.
            m = re.fullmatch(r"(.+)\((\d+)\)", name)
            return (m.group(1), int(m.group(2))) if m else (name, None)
        supplied = [_norm(f.get("name")) for f in self._raw_facts_to_generalize]
        supplied_exact = set(supplied)
        # A bare supplied name `h` (no index) subsumes every `h(i)`.
        supplied_bare = {b for (b, i) in map(_split, supplied) if i is None}
        def _already(name: str) -> bool:
            n = _norm(name)
            return n in supplied_exact or _split(n)[0] in supplied_bare
        # Display the prop via IsaTerm so the picker renders unicode, not ascii.
        offered = [(n, IsaTerm.from_isabelle(p))
                   for (n, p) in candidates if not _already(n)]
        if not offered:
            return
        chosen = await the_session().launch_interaction(
            Interaction_SelectIHFacts(offered, dvars))
        for n in chosen:
            if not _already(n):
                self._raw_facts_to_generalize.append({"name": n})
                supplied_exact.add(_norm(n))
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Induction\n")
        print_indent(indent, file)
        file.write(f"target term: {self.target_isabelle_term}\n")
        # print_indent(indent, file)
        # file.write(f"rule: {self.rule}\n")
        if any(var["status"] == "generalized" for var in self.variables):
            print_indent(indent, file)
            file.write(f"generalized variables: {string_of_and_list([var["name"] for var in self.variables if var["status"] == "generalized"])}\n")
        if self.fact_refs_to_generalize:
            print_indent(indent, file)
            file.write(f"IH facts: {string_of_and_list([r.short_name.unicode for r in self.fact_refs_to_generalize])}\n")
        super()._print_header(indent, file)
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.INDUCT(
            self.target_isabelle_term,
            cast(list[varname_spec] | None, self._case_vars_of_child(0)),
            [var["name"] for var in self.variables if var["status"] == "generalized"],
            [r.full_name for r in self.fact_refs_to_generalize],
            self._resolved_rule_str,
            self.no_simp,
            self._post_insts)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Induction failed because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Branch doesn't have an ending operation")

### Top Root

class GlobalEnv(StdBlock):
    _body_affects_siblings = True
    def _nearest_goal_for_subagent(self) -> 'Node | None':
        return None  # the global-lemmas container, not a single delegatable goal
    def _validate_child_class(self, cls: 'type[Node]') -> 'CannotEdit | None':
        if not cls._is_declarative:
            op_name = OPERATION_REGISTRY_BY_CLS.get(cls, cls.__name__)
            return CannotEdit_NonDeclarative(op_name, target_step=self.id)
        return None
    def __init__(self, config: NodeConfig):
        if not isinstance(config.parent, Root):
            raise InternalError("The parent of a GlobalEnv must be a Root")
        super().__init__(config, "", [])
        self.id = "global"
    def _subtree_stats_live(self) -> 'tuple[int, int]':
        # GlobalEnv has no goal of its own, so StdBlock's finished-block
        # promotion would make an EMPTY environment read as proved work.
        # Count only the children (plain container recursion).
        return NonLeaf_Node._subtree_stats_live(self)
    async def _auto_intro_after_me(self) -> None:
        pass
    def id_of_goal(self) -> step | None:
        return None
    def beginning_opr(self) -> None:
        return None
    def ending_opr(self) -> Minilang_Operation | None:
        return None
    def has_ending_opr(self) -> bool:
        return False
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A GlobalEnv doesn't have a beginning operation")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason("") # This suppresses the error message printing on GlobalEnv
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("Internal Bug: Failed to apply INTRO on the proof goal")
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        pass
    def quickview_header(self, indent: int, file: MyIO) -> int:
        print_indent(indent, file)
        file.write("global declarations:\n")
        return indent + 1
    def does_quickview_need_detail(self) -> bool:
        return bool(self.sub_nodes)
    def should_I_show_pending_goal(self) -> tuple[Goal, step] | None:
        return None
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return (None, indent-1)
    def _print_step_id(self, indent: int, file: MyIO, update_line: bool = False) -> int:
        if update_line:
            self.line = file.current_line()
        return indent
    def _fixed_vars_after_me(self, ret: Vars) -> Vars:
        _COMMENTED = EvaluationStatus.Status.COMMENTED
        for child in self.sub_nodes:
            if child.status.status != _COMMENTED:
                child._fixed_vars_after_me(ret)
        return ret
    def _fixed_tvars_after_me(self, ret: TVars) -> TVars:
        _COMMENTED = EvaluationStatus.Status.COMMENTED
        for child in self.sub_nodes:
            if child.status.status != _COMMENTED:
                child._fixed_tvars_after_me(ret)
        return ret
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        _COMMENTED = EvaluationStatus.Status.COMMENTED
        for child in self.sub_nodes:
            if child.status.status != _COMMENTED:
                child._fixed_facts_after_me(ret)
        return ret
    def _print_footer(self, indent: int, file: MyIO, show_warnings: bool = False) -> None:
        print_indent(indent, file)
        sess = _session_var.get(None)
        # Real open slot — handles fractional global children a prior in-env
        # insert_before may have left (identical to `len+1` for dense children), so
        # the suggested `edit fill` target is one the agent can actually fill.
        # GlobalEnv never ends ⇒ always opening ⇒ never None.
        slot = self._id_of_openning_prf_to_fill()
        if (sess is not None and sess.is_major and not sess.is_worker
                and sess.gate_global_lemma_proofs):
            file.write(
                f"You can write global declarations by calling command `edit` with action `fill` "
                f"and target step `{slot}`. If the background theory is "
                f"missing any lemmas you need, declare them here and dispatch a sub-agent to prove each.\n")
        else:
            file.write(
                f"You can write global declarations by calling command `edit` with action `fill` "
                f"and target step `{slot}`. If you find the "
                f"background theory is missing any lemmas you need, formalize and prove them here.\n")
    def unfinished_nodes(self, ret: set['Node']) -> None:
        for child in self.sub_nodes:
            child.unfinished_nodes(ret)

class Root(GoalContainer, StdBlock):
    def __init__(self, context_and_flat_goal: tuple[Context, tuple['Goal | None', int]],
                 connection: Connection):
        (context, (leading_goal, goals_count)) = context_and_flat_goal
        ml_state0 = Minilang_State(connection, '$init')
        ml_state0.leading_goal = leading_goal
        ml_state0.display_goals_count = goals_count
        ml_state0._initialized = True
        super().__init__(NodeConfig("$root", ml_state0, None), "", [])
        self.context = context
        self.global_env = GlobalEnv(NodeConfig("global", Minilang_State.assign(ml_state0), self))
        self.sub_nodes.append(self.global_env)
        self.final_ml_state = Minilang_State.assign(ml_state0)
    @property
    def session(self) -> 'Session':
        return the_session()
    def opening(self) -> bool:
        # Root is a permanent container, never "open for appending". Replaces the
        # old `self._closed_by = self` sentinel now that opening() is derived —
        # without this, derived opening() would read True via Root's GoalNode tail
        # and Root would self-flag in StdBlock.unfinished_nodes on every proof.
        return False
    async def _refresh_me_alone(self, auto_intro: bool):
        if self._first_time:
            ml_state = await self.ml_state.skip(None)
            if not ml_state.initialized():
                raise ValueError("Root: ml_state not initialized after skip")
            self.num_goals = ml_state.display_goals_count
            is_single_goal = self.num_goals == 1
            for i in range(self.num_goals):
                if is_single_goal:
                    goal_id = ""
                else:
                    goal_id = f"goal{i+1}"
                goal_node = GoalNode(NodeConfig(goal_id, ml_state, self), is_single_goal, True, None)
                goal_node.id = goal_id
                self.sub_nodes.append(goal_node)
                if i < self.num_goals - 1:
                    ml_state = await ml_state.sorry_next(None, None)
            #self.final_ml_state = ml_state
        await super()._refresh_me_alone(auto_intro)
    async def _refresh_all_children_after(self, after: 'Node | Literal["end"]', can_continue_i: bool) -> None:
        # GoalContainer blocks cross-child propagation because each subgoal is
        # independent in AoA — that's correct for changes initiated *from* a
        # GoalNode (a change inside one goal must not ripple into siblings).
        # But GlobalEnv sits before all GoalNodes and its declarations affect
        # every goal, so a change *from* GlobalEnv must propagate forward to
        # all GoalNodes. Override to allow that one direction only.
        if after is self.global_env:
            for child in self.sub_nodes[1:]:
                await child._refresh_me_alone(auto_intro=True)
            # Root has no parent, no upward recursion.
            return None
        # Otherwise (after is a GoalNode or "end"): keep GoalContainer's
        # behavior — block propagation between independent subgoals.
        return None
    def id_of_goal(self) -> step | None:
        return None
    def resulting_state(self) -> Minilang_State:
        return self.final_ml_state
    def _print_step_id(self, indent: int, file: MyIO, update_line: bool = False) -> int:
        if update_line:
            self.line = file.current_line()
        return indent
    def beginning_opr(self) -> Minilang_Operation | None:
        return None
    def ending_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.END()
    def has_ending_opr(self) -> bool:
        return True
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Root doesn't have a beginning operation")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason("") # This suppresses the error message printing on Root
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason("Failed to close the top-level proof")
    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        print_vars(self.context.vars.items(), indent, file, {})
        print_type_vars(self.context.tvars.items(), indent, file, {})
        print_hyps(self.context.hyps.items(), indent, file, {})
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
        self.sub_nodes[0].print(indent, file, update_line, show_warnings=show_warnings)
        match self.num_goals:
            case 1:
                self.sub_nodes[1].print(indent, file, update_line, show_warnings=show_warnings)
            case _:
                file.write("proof goals:\n")
                for i in range(self.num_goals):
                    print_indent(indent+1, file)
                    file.write(f"- goal index: {i+1}\n")
                    self.sub_nodes[i+1].print(indent+2, file, update_line, show_warnings=show_warnings)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.FOOTER])
        return indent
    def quickview(self, indent: int, file: MyIO) -> int:
        if self.global_env.sub_nodes:
            self.global_env.quickview(indent, file)
        match self.num_goals:
            case 1:
                if self.global_env.sub_nodes:
                    print_indent(indent, file)
                    file.write("proof:\n")
                    self.sub_nodes[1].quickview(indent+1, file)
                else:
                    self.sub_nodes[1].quickview(indent, file)
            case _:
                print_indent(indent, file)
                file.write("goals:\n")
                for i in range(self.num_goals):
                    self.sub_nodes[i+1].quickview(indent+1, file)
        return indent

    def _locate_node(self, ids: Sequence[local_step], id: step, pos: int = 0) -> 'Node':
        if pos != 0:
            raise InternalError("pos should be 0 when locating a node in a Root")
        if not ids:
            if self.num_goals == 1:
                return self.sub_nodes[1]
            else:
                # Empty id path reaches here only via `ids[:-1]` slicing in
                # `fill` / `locate_node_or_slot` (a no-dot id with no locatable
                # parent block). Under multiple top-level goals that is simply an
                # unresolvable id — NodeNotFound (caught and reported gracefully),
                # not an internal invariant violation.
                raise NodeNotFound(id)
        if ids[0] == "global":
            return self.sub_nodes[0]._locate_node(ids, id, 1)
        else:
            if self.num_goals <= 1:
                return self.sub_nodes[1]._locate_node(ids, id, 0)
            else:
                for node in self.sub_nodes:
                    if node.local_step == ids[0]:
                        return node._locate_node(ids, id, 1)
                raise NodeNotFound(id)
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        ret.update(self.context.vars)
        return ret
    def _fixed_tvars_at_me(self, ret: TVars) -> TVars:
        ret.update(self.context.tvars)
        return ret
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        ret.update(self.context.hyps)
        return ret

    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        raise InternalError("Depreciated")

    async def comment(self, steps: list[step]) -> 'CommentOutcome':
        affected: list[step] = []
        not_found: list[step] = []
        warnings: list[str] = []
        for sid in steps:
            try:
                node = self.locate_node(sid)
            except NodeNotFound:
                not_found.append(sid)
                continue
            if isinstance(node, (Root, GlobalEnv, GoalNode)):
                raise AoA_Error(
                    f"Step {the_session()._display_id(sid)} is a structural container "
                    f"({type(node).__name__}) and cannot be commented out.")
            if node.status.status == EvaluationStatus.Status.COMMENTED:
                warnings.append(
                    f"Step {the_session()._display_id(sid)} is already commented out.")
                continue
            node.status = EVALUATION_COMMENTED
            # opening() is derived from the live tail (see NonLeaf_Node.opening),
            # so commenting the closer makes the parent read open automatically —
            # no _closed_by mutation needed here (DEFECT 1 fix is structural).
            await node._refresh_me_alone(auto_intro=False)
            await node._refresh_all_after_me()
            affected.append(sid)
        return CommentOutcome(affected, not_found, warnings)

    async def uncomment(self, steps: list[step]) -> 'CommentOutcome':
        affected: list[step] = []
        not_found: list[step] = []
        warnings: list[str] = []
        for sid in steps:
            try:
                node = self.locate_node(sid)
            except NodeNotFound:
                not_found.append(sid)
                continue
            if node.status.status != EvaluationStatus.Status.COMMENTED:
                warnings.append(
                    f"Step {the_session()._display_id(sid)} is not commented out.")
                continue
            node.status = EVALUATION_NOT_YET
            node._has_considered_auto_intro = False
            await node._refresh_me_alone(auto_intro=True)
            await node._refresh_all_after_me()
            affected.append(sid)
        return CommentOutcome(affected, not_found, warnings)

class CommentOutcome(NamedTuple):
    affected: list[step]
    not_found: list[step]
    warnings: list[str]

# class Hierarchy

# Root
#  0: GlobalEnv
#  1...n: GoalNode
#     proofs
#      0: Obtain
#         proofs...
#           Obvious
#      1. SIMP / REWRITE / RULE
#       P <--> Q
#          GoalNodes
#          1. GoalNode: P --> Q
#             proofs...
#          2. GoalNode: Q --> P

### Gen Node

def Parse_Nodes(
    remaining: 'LinkedList[_RawOp]',
) -> 'LinkedList[Parsed_Opr]':
    """Parse a linked list of raw ops into a linked list of gen_nodes.
    Empty `remaining` → `None`; otherwise pull the head, dispatch its
    class's `.gen(arg, tail, path)`, and return whatever linked list
    that produces (the subclass may itself prepend more cells before
    the tail, e.g. via singleton splice).

    Validation of the raw dict (is it a dict? does it have a known
    `operation`? does it satisfy the ToolArg's required keys?) lives
    here; validation of the ToolArg's semantic content and parsing of
    any nested `proof` / `proofs` / `cases[].proof` fields live inside
    `cls.gen(arg, remaining, path)`.
    """
    if remaining is None:
        return None
    cell = remaining.head
    data = cell.op
    path = cell.path
    if not isinstance(data, dict):
        raise ArgumentError({},
            f"{path}: expected a proof operation object, got {type(data).__name__}")
    operation = data.get("operation")
    if operation is None:
        raise ArgumentError_MissingRequiredKeys(data, path, ["operation"])
    meta = OPERATION_REGISTRY.get(operation)
    if meta is None:
        raise ArgumentError_UnknownProofOperation(data)
    op_path = f"{path} ({operation})"
    data = validate(meta.toolarg_typed_dict, data, op_path)
    return meta.cls.gen(cast(Any, data), remaining.tail, op_path)


def Parse_Op_List(ops: Any, container_path: str) -> list[Parsed_Opr]:
    """Entry point — parse an entire list of op dicts into a flat
    `list[Parsed_Opr]`.  Atomic: on any failure anywhere in the tree, raises
    before any mutation could have occurred.  Internally builds a linked
    list of `_RawOp(op, path)` cells and runs `Parse_Nodes`; materializes
    the resulting linked list of gen_nodes into a regular Python list for
    storage / downstream use."""
    if not isinstance(ops, list):
        raise ArgumentError({},
            f"{container_path}: expected an array of proof operations, "
            f"got {type(ops).__name__}")
    raw = from_iterable(
        _RawOp(op, f"{container_path}[{i}]") for i, op in enumerate(ops))
    return list(iterate(Parse_Nodes(raw)))


# --- shared helpers consumed by per-class `.gen` classmethods -----------

def _parse_optional_raw_proof(
    raw: 'raw_proof | None', path: str,
) -> 'proof | None':
    """Parse the optional `proof` body of Have / Suffices / Obtain /
    Branch-case.  `None` *and* an empty list `[]` both stay `None`; a
    non-empty list is recursively parsed into a flat `list[Parsed_Opr]`.

    Normalizing `[]` to `None` (mirroring `_parse_positional_proofs`)
    makes `proof: []` behave identically to an absent `proof` everywhere:
    on a fresh fill both leave an empty/auto-intro'd open block, and on
    `amend` both *preserve* an inherited body rather than wiping it."""
    if raw is None or raw == []:
        return None
    return Parse_Op_List(raw, path)


def _parse_positional_proofs(
    raw: Any, path: str,
) -> 'list[proof] | None':
    """Parse the positional per-subgoal `proofs: list[raw_proof]` field of
    InferenceRule / Intro (NON-singleton case — callers handle the len==1
    splice themselves).  Returns `None` if `raw is None` OR `raw == []`
    — an empty `proofs` list is normalized to 'no proofs provided' so
    `proofs: []` behaves identically to `proofs: None` downstream."""
    if raw is None or raw == [] or raw == "GivenLater":
        return None
    if not isinstance(raw, list):
        raise ArgumentError({},
            f"{path}: expected an array, got {type(raw).__name__}")
    out: list[proof] = []
    for pi, body in enumerate(raw):
        body_path = f"{path}[{pi}]"
        if body is None:
            out.append([])
            continue
        if not isinstance(body, list):
            raise ArgumentError({},
                f"{body_path}: expected an array of proof operations, "
                f"got {type(body).__name__}")
        out.append(Parse_Op_List(body, body_path))
    if all(p == [] for p in out):
        return None
    return out


## Session

import contextvars

_session_var: contextvars.ContextVar['Session'] = contextvars.ContextVar('_session_var')

def the_session() -> 'Session':
    return _session_var.get()

def _rendering_for_dispatcher() -> bool:
    """True when the current rendering session can dispatch sub-agents — the main
    agent OR a worker (both may call `subagent`). Excludes interaction forks; never
    crashes outside a session. Used for the "delegate this goal" hint."""
    sess = _session_var.get(None)
    return sess is not None and (sess.is_major or sess.is_worker)

def tn(t: tool) -> str:
    """Resolve abstract tool id to driver-specific name via the current session."""
    return the_session().tool_name(t)


# ---------------------------------------------------------------------------
# Worker-scoped relative step ids
# ---------------------------------------------------------------------------
# A worker renders and uses step ids RELATIVE to its proof scope (its target's
# absolute id prefix stripped), so it sees `step 2.1` instead of the global
# `step 1.1.1.1A.2.1`; non-workers are unchanged.  Translation lives entirely
# at the agent boundary (`Session._display_id` / `_resolve_display_id` /
# `_postprocess_outbound_text` / `_absolutize_text`); the tree and proof cache stay
# absolute.  See the design plan for the full rationale.

EXTERNAL_STEP = "<external>"   # marker shown for an out-of-scope id (placeholder wording)

def _relativize_id(abs_id: str, scope_prefix: str) -> 'str | None':
    """Strip `scope_prefix` from a descendant's absolute id.  Returns the
    relative suffix, "" for the scope root itself, or None when `abs_id` is not
    under `scope_prefix` (out of scope — caller masks it)."""
    if abs_id == scope_prefix:
        return ""
    if abs_id.startswith(scope_prefix + "."):
        return abs_id[len(scope_prefix) + 1:]
    return None

def _absolutize_id(rel: str, scope_prefix: str) -> str:
    """Inverse of `_relativize_id`: a worker-relative id back to absolute."""
    rel = rel.strip()
    return scope_prefix if rel == "" else f"{scope_prefix}.{rel}"

# Matches a step-id reference inside free text: a kind word + a dotted id, with
# an optional surrounding backtick or single-quote.  Kind words are a noun
# (`step`/`goal`/`subgoal`/`node`/`id`/`case`, case-insensitive + plural) or an
# id-verb (`fill`/`delete(d)`/`amend`/`prove`/`delegate`/`handle`).  The `\.`
# requirement filters bare English ("step 2" is never matched).  Capture groups:
# (1)=keyword (2)=ws+open-quote (3)=dotted id (4)=close-quote; all three
# use-sites rewrite only group 3 and copy 1/2/4 verbatim.
_ID_IN_TEXT_RE = re.compile(
    r'\b([Ss]teps?|[Gg]oals?|[Ss]ubgoals?|[Nn]odes?|[Ii][Dd]s?|[Cc]ases?'
    r'|[Ff]ill|[Dd]elete[d]?|[Aa]mend|prove|delegate|handle)'
    r"(\s+[`']?)(\w+(?:\.\w+)+)([`']?)")
# Matches `the out-of-scope variable <internal>` emitted by Unify_Diagnostic
# (the captured group is the raw internal/skolem name, e.g. `n__`).
_OUTSCOPE_VAR_RE = re.compile(r"the out-of-scope variable ([A-Za-z0-9_']+)")


# Custom string representer for literal block style on multiline strings
def _str_representer(dumper, data):
    """
    Custom YAML string representer that uses literal block style (|)
    for multiline strings and regular style for single-line strings.
    """
    if '\n' in data:
        return dumper.represent_scalar('tag:yaml.org,2002:str', data, style='|')
    return dumper.represent_scalar('tag:yaml.org,2002:str', data)

# Register the custom representer
yaml.add_representer(str, _str_representer)

#### Role ADT

@dataclass
class Role_Major:
    # The single continuous main (planner) agent. Stageless: it runs real proofs
    # throughout and delegates hard sub-goals on demand via the `subagent` tool.
    pass

@dataclass
class Role_Worker:
    target: 'NonLeaf_Node'
    suggestions: str = ""
    useful_lemmas: list[str] = field(default_factory=list)
    # The live ``WorkerHandle`` mediating
    # this worker's events (``WorkerHandle`` is defined below in this module).
    worker_handle: 'WorkerHandle | None' = None
    # True iff this worker was dispatched by the `request` auto-prove-general path
    # to prove an auto-declared global helper lemma, synchronously, on behalf of a
    # NON-adjudicating requester (the requesting worker is not a planner — it cannot
    # review a refutation or supply sub-lemmas). "Headless" = no supervising agent
    # above it to resolve a non-terminal park, so such a prover must yield ONLY
    # terminal outcomes: the struggle/difficulty checkpoint is disabled for it
    # (`_should_struggle_checkpoint`); its own `request` rejects non-general lemmas
    # (never parks) and resolves any constraint it raises IN-LOOP (never parks).
    # See `_run_worker_on`.
    headless: bool = False

@dataclass
class Role_Interaction:
    pending: Fork_Pending
    prompt: str
    resume_id: str | None
    mode: ForkingMode

Role = Role_Major | Role_Worker | Role_Interaction


class Runtime:
    """Global singleton shared across all Sessions operating on the same proof tree.
    Holds counters and limits that must be unique/shared."""
    def __init__(self):
        self.age: int = 0
        self.setup_rewriting_counter: int = 0
        self.fact_name_counter: int = 0
        self._pit_counter: int = 0
        self.quickview_line_numbers: bool = False
        self._depth_limit: int = 30
        self._depth_limit_exceeded: bool = False
        self.total_tool_calls: int = 0
        self._budget_start_time: float | None = None
        self.worker_max_tool_calls: int = 500
        self.deleted_archive: list[DeletedEntry] = []
        # Every missing-lemma item reported this invocation (survey answers +
        # worker request_lemmas mirrors), shared planner/workers/forks via the
        # runtime singleton. Rendered into later survey prompts so the model
        # stops re-reporting the same fact within one run.
        self.reported_missing_lemmas: list = []

    def next_pit_name(self) -> str:
        i = self._pit_counter
        self._pit_counter = i + 1
        return f"P__I__T__{i}"


# abstract base class for a session
class Session:
    root: Root
    runtime: Runtime
    logger: logging.Logger | None
    log_dir: Path | None
    interaction_log_path: Path | None
    proofs_log_path: Path | None
    proof_oprs_log_path: Path | None
    interaction_log_file: Any | None  # File handle for interaction.yaml
    proofs_log_file: Any | None       # File handle for proofs.yaml
    proof_oprs_log_file: Any | None   # File handle for proof_oprs.yaml
    meta_log_path: Path | None
    _meta_log_file: Any | None        # Raw file handle for meta.jsonl.zst
    _meta_log_writer: Any | None      # zstandard stream writer

    # class variables
    Driver: dict[str, 'SessionConstructor'] = {}
    _driver_name: ClassVar[str] = ""

    # Global-lemma delegation gate — each driver self-specifies via this class
    # attribute (base default OFF; the DeepSeek driver overrides to True). Consulted
    # only for a non-worker major (see `_edit_tool_logic` / `_global_lemma_gate`).
    gate_global_lemma_proofs: bool = False

    def __init__(self, logger: logging.Logger | None = None, log_dir: str | Path = "",
                 parent: 'Session | None' = None,
                 argument: str | None = None,
                 retrieval_forking_mode: ForkingMode = ForkingMode.FORKING_WITH_CTXT,
                 interactive_retrieval: InteractiveRetrievalMode = InteractiveRetrievalMode.YES,
                 timeout_seconds: float = 14400,
                 max_tool_calls: int = 10000,
                 max_retries: int = 5,
                 runtime: Runtime | None = None,
                 role: Role | None = None):
        """
        Args:
            logger: Python logger for runtime debug messages to the server log stream.
            log_dir: Directory for persistent session logs (interaction.yaml, proofs.yaml,
                proof_oprs.yaml). Empty string disables file logging.
            parent: Parent session for subsessions. None means this is a major session.
            retrieval_forking_mode: Forking strategy for interactive retrieval.
            interactive_retrieval: Whether to use fork-based interactive retrieval.
            timeout_seconds: Wall-clock time limit for the session.
            max_tool_calls: Maximum number of tool invocations.
            max_retries: Maximum number of conversation retry turns.
            runtime: Shared Runtime instance. If None, inherits from parent or creates new.
        """
        self.parent = parent
        if runtime is not None:
            self.runtime = runtime
        elif parent is not None:
            self.runtime = parent.runtime
        else:
            self.runtime = Runtime()
        _session_var.set(self)
        self.role: Role = role if role is not None else Role_Major()
        self.last_proof_op_time: float = time()
        self.logger = logger or (parent.logger if parent else None)
        # The NonLeaf_Node block the agent is currently working in — i.e. "where
        # in the proof tree the agent is now". `initialize` sets it to `root`;
        # each edit op then moves it (fill → the filled node; insert_before /
        # amend / delete → the target's parent). It drives `retrieval_state`, so
        # name lookups resolve in the current block's context. None until init.
        self.working_block: 'NonLeaf_Node | None' = None
        self.warnings: list[str] = []
        self.auto_intro_nodes: list['Intro'] = []
        self.total_cost_usd: float = 0.0
        self.total_input_tokens: int = 0
        self.total_output_tokens: int = 0
        self.total_cache_creation_input_tokens: int = 0
        self.total_cache_read_input_tokens: int = 0
        self.total_isabelle_time: float = 0.0
        self.total_model_time: float = 0.0
        self.total_quota_wait_time: float = 0.0
        self._total_calls_at_last_refresh: int = 0
        self._refresh_summary: str | None = None
        if parent is not None:
            self.timeout_seconds = parent.timeout_seconds
            self.max_tool_calls = parent.max_tool_calls
            self.max_retries = parent.max_retries
        else:
            self.timeout_seconds = timeout_seconds
            self.max_tool_calls = max_tool_calls
            self.max_retries = max_retries
        self._retry_count: int = 0
        self.quit_info: 'QuitInfo | None' = None
        self._session_edit_count: int = 0
        self._session_delete_count: int = 0
        _is_sub_subagent = (isinstance(self.role, Role_Worker)
                            and parent is not None
                            and isinstance(parent.role, Role_Worker))
        if _is_sub_subagent:
            self._struggle_edit_threshold: int = 20
            self._struggle_delete_threshold: int = 4
        else:
            self._struggle_edit_threshold: int = 30
            self._struggle_delete_threshold: int = 5
        self._struggle_checkpoint_count: int = 0
        # Missing-lemma survey (external import-expansion loop). Interval = how
        # many `query` tool calls between surveys; 0 disables. Read once from the
        # environment for the top-level session; forks/workers inherit the value
        # but keep their own per-session query counter.
        self._missing_lemma_survey_interval: int = (
            parent._missing_lemma_survey_interval if parent is not None
            else _missing_lemma_survey_interval_from_env())
        self._query_calls_since_survey: int = 0
        self.retrieval_forking_mode: ForkingMode = (
            parent.retrieval_forking_mode if parent is not None
            else retrieval_forking_mode)
        self.interactive_retrieval: InteractiveRetrievalMode = (
            parent.interactive_retrieval if parent is not None
            else interactive_retrieval)
        # A worker sub-agent is a fresh chat that never inherits the planner's
        # conversation, so it must NOT inherit the planner's view-dedup caches
        # either — otherwise entities / commands / abbreviations / the [manual]
        # note that the planner already saw (but the worker never did) would be
        # silently suppressed in the worker's prompts. Interactions keep
        # inheriting (they may resume the parent's context).
        # Only inherit the view caches from a non-worker parent; a worker gets a
        # fresh (empty) view, never copying the planner's.
        _view_parent = None if isinstance(self.role, Role_Worker) else parent
        self.seen_entities: 'set[short_name]' = (
            set(_view_parent.seen_entities) if _view_parent is not None else set())
        self.seen_commands: dict[IsabellePosition, str] = (
            dict(_view_parent.seen_commands) if _view_parent is not None else {})
        self.seen_manual_note: bool = (
            _view_parent.seen_manual_note if _view_parent is not None else False)
        # Number of per-query search summary lines emitted so far; the first few
        # use the verbose phrasing, the rest a terse one (see retrieval.py).
        self.search_summary_count: int = (
            _view_parent.search_summary_count if _view_parent is not None else 0)
        self.showed_suffices_notice: bool = False
        # Agent Hint Registry: names of constants/facts whose NOTICE hint has
        # already been surfaced this session (one-shot per name). Inherited by
        # view-forks so a notice isn't repeated across the same agent context.
        self.shown_hints: set[str] = (
            set(_view_parent.shown_hints) if _view_parent is not None else set())
        # Failed deep `Obvious` node ids whose `_print_subagent_hint` delegate
        # suggestion has already been surfaced this session (one-shot per node,
        # scope-relative depth). Mirrors `shown_hints`: workers get a fresh set
        # (their own focus scope), interaction view-forks inherit a copy.
        self.shown_subagent_hints: set[str] = (
            set(_view_parent.shown_subagent_hints) if _view_parent is not None else set())
        # Transient render flag: True only while the consuming inline-Outline
        # surface (`quickview_proof_scope`) renders, so an inline subagent hint
        # marks itself shown there but NOT in the non-consuming `proof.yaml`
        # render (mirrors the `_emit_pending_hint_notices` consume discipline).
        self._consuming_subagent_hints: bool = False
        self.seen_abbreviations: set[str] = (
            set(_view_parent.seen_abbreviations) if _view_parent is not None else set())
        self.showed_fill_hint: bool = False
        self.showed_cancelled_notice: bool = False
        self.shown_HAVE_fact_names: 'dict[str, list[tuple[varname, typ]]]' = {}
        # One-shot bypass of the suggestions external-step check, keyed by the
        # dispatched node's id: a rejected `subagent` call records the node here
        # so an immediate retry on the same node is let through (see
        # `_subagent_tool_logic`).
        self._subagent_extstep_bypass: 'set[str]' = set()
        self._nf_pending_interaction: 'Interaction | None' = None
        self._channel: 'InteractionChannel | None' = None
        # Background tasks owned by this session (e.g. a tool task suspended on
        # a non-forking interaction); still-pending ones are cancelled by
        # `close()` so they never outlive the session (see `adopt_task`).
        self._owned_tasks: 'set[asyncio.Task]' = set()
        # Worker-only: ascii fact name -> standard-printed proposition (IsaTerm),
        # prefetched once at init (see _prefetch_worker_premises).
        self._worker_premise_cache: 'dict[str, IsaTerm]' = {}
        # Worker-only: ascii fact name -> ascii of the proposition (the live
        # `_ctxt_before_me().hyps` raw term) last surfaced to this agent under that
        # name. Diffed on resume to report a before-target fact whose proposition is
        # NEW, or has CHANGED under the same name since last shown — an amended global
        # lemma, or a deleted-then-recycled name — so the worker always sees the LATEST
        # statement (a re-stated lemma is re-notified on purpose, to flag the update).
        # The change-detection identity is the live-hyps raw ascii, independent of
        # `_worker_premise_cache` freshness. Seeded/re-seeded from `_ctxt_before_me().hyps`
        # (see _seed_reported_scope_facts / consume_new_scope_facts_notice).
        self.reported_scope_facts: 'dict[str, str]' = {}
        # Memoized `initial_prompt()`: its content is fixed for the session's
        # lifetime, but computing it resolves worker-suggested lemmas via RPC, so
        # repeat callers (compaction / restart / `_find_recent_start`) reuse it.
        self._initial_prompt_cache: 'str | None' = None
        if parent is not None:
            # Subsessions share parent's log files
            self.log_dir = parent.log_dir
            self.interaction_log_path = parent.interaction_log_path
            self.proofs_log_path = parent.proofs_log_path
            self.proof_oprs_log_path = parent.proof_oprs_log_path
            self.retrieval_log_path = parent.retrieval_log_path
            self.missing_lemmas_log_path = parent.missing_lemmas_log_path
            self.interaction_log_file = parent.interaction_log_file
            self.proofs_log_file = parent.proofs_log_file
            self.proof_oprs_log_file = parent.proof_oprs_log_file
            self.retrieval_log_file = parent.retrieval_log_file
            self.missing_lemmas_log_file = parent.missing_lemmas_log_file
            # Forks share meta writer; asyncio-concurrent (single thread), no lock needed
            self.meta_log_path = parent.meta_log_path
            self._meta_log_file = parent._meta_log_file
            self._meta_log_writer = parent._meta_log_writer
        else:
            self.log_dir = None
            self.interaction_log_path = None
            self.proofs_log_path = None
            self.proof_oprs_log_path = None
            self.retrieval_log_path = None
            self.missing_lemmas_log_path = None
            self.interaction_log_file = None
            self.proofs_log_file = None
            self.proof_oprs_log_file = None
            self.retrieval_log_file = None
            self.missing_lemmas_log_file = None
            self.meta_log_path = None
            self._meta_log_file = None
            self._meta_log_writer = None
            if log_dir != "":
                self._setup_log_directory(log_dir)

    # --- Forwarding properties to Runtime ---
    @property
    def age(self) -> int:
        return self.runtime.age
    @age.setter
    def age(self, v: int):
        self.runtime.age = v
    @property
    def setup_rewriting_counter(self) -> int:
        return self.runtime.setup_rewriting_counter
    @setup_rewriting_counter.setter
    def setup_rewriting_counter(self, v: int):
        self.runtime.setup_rewriting_counter = v
    @property
    def fact_name_counter(self) -> int:
        return self.runtime.fact_name_counter
    @fact_name_counter.setter
    def fact_name_counter(self, v: int):
        self.runtime.fact_name_counter = v
    @property
    def _pit_counter(self) -> int:
        return self.runtime._pit_counter
    @_pit_counter.setter
    def _pit_counter(self, v: int):
        self.runtime._pit_counter = v
    @property
    def quickview_line_numbers(self) -> bool:
        return self.runtime.quickview_line_numbers
    @quickview_line_numbers.setter
    def quickview_line_numbers(self, v: bool):
        self.runtime.quickview_line_numbers = v
    @property
    def _depth_limit(self) -> int:
        return self.runtime._depth_limit
    @_depth_limit.setter
    def _depth_limit(self, v: int):
        self.runtime._depth_limit = v
    @property
    def _depth_limit_exceeded(self) -> bool:
        return self.runtime._depth_limit_exceeded
    @_depth_limit_exceeded.setter
    def _depth_limit_exceeded(self, v: bool):
        self.runtime._depth_limit_exceeded = v
    @property
    def total_tool_calls(self) -> int:
        return self.runtime.total_tool_calls
    @total_tool_calls.setter
    def total_tool_calls(self, v: int):
        self.runtime.total_tool_calls = v
    @property
    def _budget_start_time(self) -> float | None:
        return self.runtime._budget_start_time
    @_budget_start_time.setter
    def _budget_start_time(self, v: float | None):
        self.runtime._budget_start_time = v
    @property
    def worker_max_tool_calls(self) -> int:
        return self.runtime.worker_max_tool_calls
    @worker_max_tool_calls.setter
    def worker_max_tool_calls(self, v: int):
        self.runtime.worker_max_tool_calls = v
    def next_pit_name(self) -> str:
        return self.runtime.next_pit_name()

    @property
    def is_major(self) -> bool:
        # The top-level (main) session — no parent. This is the planner / main
        # agent; workers and interaction forks are sub-sessions. Owns log files
        # and working-dir cleanup, and gates the planner-only `subagent` tool.
        # Invariant: parent is None  <==>  role is Role_Major  (workers/forks
        # always have a parent and a non-major role); so is_major is the
        # canonical planner test.
        return self.parent is None

    @property
    def is_worker(self) -> bool:
        return isinstance(self.role, Role_Worker)
    @property
    def is_interaction(self) -> bool:
        return isinstance(self.role, Role_Interaction)

    @property
    def role_label(self) -> str:
        """Short semantic tag for this session's role, prefixed onto every log
        entry (a ``role`` field in YAML/meta, a ``[...]`` prefix in the debug
        stream) so each line is attributable to the planner / a worker / an
        interaction fork. Derived from ``self.role`` (always set), so it is safe
        on the base test session, not just live drivers."""
        match self.role:
            case Role_Worker(target=t):
                return f"worker:{t.id}"
            case Role_Interaction(pending=p):
                return "interaction:" + type(p.interaction).__name__.removeprefix("Interaction_")
            case _:  # Role_Major
                return "main"

    @property
    def fork_pending(self) -> 'Fork_Pending | None':
        if isinstance(self.role, Role_Interaction):
            return self.role.pending
        return None

    @property
    def pending_interaction(self) -> 'Interaction | None':
        """The active interaction, if any — forking or non-forking."""
        if isinstance(self.role, Role_Interaction):
            return self.role.pending.interaction
        return self._nf_pending_interaction

    def replace_pending_interaction(self, new_interaction: 'Interaction') -> None:
        """Swap the pending interaction of this fork for a different one, reusing
        the existing answer future (only one final answer is ever returned to the
        operation that called launch_interaction). The replacement must match this
        fork's forking mode (fixed at fork creation); a mismatch is a programming
        bug and raises InternalError."""
        role = self.role
        if not isinstance(role, Role_Interaction):
            raise InternalError("replace_pending_interaction on non-interaction session")
        if new_interaction.forking != role.mode:
            raise InternalError(
                f"Cannot replace interaction: new forking mode {new_interaction.forking} "
                f"is incompatible with this fork's mode {role.mode}")
        role.pending = Fork_Pending(new_interaction, role.pending.answer)

    @property
    def lemma_anchor(self) -> 'Have | None':  # type: ignore  — `Have`'s class identity is erased to type[Any] by @proof_operation, so it can't form a union annotation
        if isinstance(self.role, Role_Worker) and isinstance(self.role.target, Have):
            return self.role.target
        return None

    def __str__(self) -> str:
        return self._driver_name

    def _setup_log_directory(self, log_dir: str | Path):
        """
        Set up the log directory and create log files.

        Args:
            log_dir: Path to the logging directory

        Raises:
            InternalError: If directory cannot be created or is not writable
        """
        import os
        from datetime import datetime

        self.log_dir = Path(log_dir)

        # If directory exists and is non-empty, rename it before creating a new one
        if self.log_dir.exists() and any(self.log_dir.iterdir()):
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            old_dir_name = f"{self.log_dir.name}.old_{timestamp}"
            old_dir_path = self.log_dir.parent / old_dir_name
            try:
                self.log_dir.rename(old_dir_path)
                if self.logger:
                    self.logger.info(f"Renamed existing log directory to {old_dir_path}")
            except Exception as e:
                raise InternalError(f"Failed to rename existing log directory {self.log_dir}: {e}")

        # Create directory if it doesn't exist
        try:
            self.log_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            raise InternalError(f"Failed to create log directory {self.log_dir}: {e}")

        # Check read and write permissions
        if not os.access(self.log_dir, os.R_OK | os.W_OK):
            raise InternalError(f"Log directory {self.log_dir} is not readable and writable")

        # Set up log file paths and open files
        self.interaction_log_path = self.log_dir / "interaction.yaml"
        self.proofs_log_path = self.log_dir / "proofs.yaml"
        self.proof_oprs_log_path = self.log_dir / "proof_oprs.yaml"
        self.retrieval_log_path = self.log_dir / "retrieval.yaml"
        self.missing_lemmas_log_path = self.log_dir / "missing_lemmas.yaml"

        # Open log files in append mode, keep them open
        self.interaction_log_file = open(self.interaction_log_path, 'a', encoding='utf-8')
        self.proofs_log_file = open(self.proofs_log_path, 'a', encoding='utf-8')
        self.proof_oprs_log_file = open(self.proof_oprs_log_path, 'a', encoding='utf-8')
        self.retrieval_log_file = open(self.retrieval_log_path, 'a', encoding='utf-8')
        self.missing_lemmas_log_file = open(self.missing_lemmas_log_path, 'a', encoding='utf-8')

        # Open compressed meta log
        import zstandard
        self.meta_log_path = self.log_dir / "meta.jsonl.zst"
        self._meta_log_file = open(self.meta_log_path, 'ab')
        self._meta_log_writer = zstandard.ZstdCompressor(level=3).stream_writer(
            self._meta_log_file, closefd=False, write_return_read=False)

        import atexit
        self._atexit_registered = True
        atexit.register(self._atexit_close_meta)

        # Write initial session start markers
        session_start = {
            "event": "SESSION_START",
            "timestamp": datetime.now().isoformat(),
        }
        self._append_yaml(self.interaction_log_file, session_start)
        self._append_yaml(self.proofs_log_file, session_start)
        self._append_yaml(self.proof_oprs_log_file, session_start)
        self._append_yaml(self.retrieval_log_file, session_start)
        self._append_yaml(self.missing_lemmas_log_file, session_start)
        self._log_meta("SESSION_START")

    def _append_yaml(self, file_handle: Any, data: dict[str, Any]):
        """
        Append a YAML document to an open file using multi-document format.

        Args:
            file_handle: Open file handle
            data: Dictionary to append as a YAML document
        """
        # Get current position to check if file is empty
        current_pos = file_handle.tell()
        if current_pos > 0:
            file_handle.write('\n---\n')
        else:
            file_handle.write('---\n')
        yaml.dump(data, file_handle,
                  default_flow_style=False,
                  allow_unicode=True,
                  sort_keys=False,  # Preserve field insertion order
                  width=120,        # Wider lines for readability
                  indent=2)         # Standard indentation
        file_handle.flush()  # Ensure data is written immediately

    def _log_meta(self, event_type: str, **data):
        """Append one JSON line to meta.jsonl.zst and flush immediately."""
        if self._meta_log_writer is None:
            return
        import zstandard
        # ``role`` is stamped here (not at each call site) so EVERY meta entry —
        # including direct _log_meta callers (SESSION_START, SYS_PROMPT, USAGE,
        # COMPACTION, …) — is attributable. A caller-supplied role in **data wins.
        entry = {"event": event_type, "ts": datetime.now().isoformat(),
                 "role": self.role_label, **data}
        line = json.dumps(entry, ensure_ascii=False, default=str) + "\n"
        self._meta_log_writer.write(line.encode("utf-8"))
        self._meta_log_writer.flush(zstandard.FLUSH_FRAME)

    def _atexit_close_meta(self):
        """Safety net: close meta writer on interpreter exit."""
        try:
            if self._meta_log_writer is not None:
                self._meta_log_writer.close()
                self._meta_log_writer = None
            if self._meta_log_file is not None:
                self._meta_log_file.close()
                self._meta_log_file = None
        except Exception:
            pass

    async def __aenter__(self) -> 'Session':
        """Enter the runtime context for this session."""
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Exit the runtime context and clean up the session."""
        await self.close()
        return False

    def _lemma_guidance(self, under_global: bool) -> str:
        """The "if a needed lemma doesn't exist, ..." guidance clause, shared by
        ``system_prompt`` and ``_compute_initial_prompt`` so the two cannot drift.
        When the global-lemma gate is active for this non-worker major, steer to
        declare-then-delegate; a worker is steered to prove inline or `request`;
        otherwise keep the legacy "prove it" wording so flag-off planner output is
        byte-identical."""
        if self.is_major and not self.is_worker and self.gate_global_lemma_proofs:
            return ("if a needed lemma truly does not exist, declare it as a `Have` node "
                    "under `global`, then dispatch a sub-agent to prove it.\n")
        if self.is_worker:
            # A worker can prove a needed fact inline as a LOCAL `Have` (cheap), or
            # — for a general lemma it cannot prove inline — raise a `request` (the
            # worker→planner channel, which dispatches a prover sub-agent; the cost
            # caution lives on the `request` tool itself). The planner branch above
            # deliberately does NOT mention `request`: the planner is the RECIPIENT
            # of requests, not a caller.
            return ("if a needed lemma truly does not exist, prove it inline as a "
                    "`Have`, or raise a `request`.\n")
        suffix = " under `global`" if under_global else ""
        return f"if a needed lemma truly does not exist, prove it as a `Have` node{suffix}.\n"

    def system_prompt(self) -> str | None:
        """Return the system prompt, or None if the driver folds it into the initial message."""
        report_line = (
            "If the goal itself looks flawed or unprovable, or you have exhausted "
            f"your strategies — report it with `{self.tool_name(TOOL_REPORT)}`.\n"
            if self.is_worker else
            "A proof goal can be buggy and thus unprovable — "
            f"call `{self.tool_name(TOOL_REPORT)}` with your analysis if you believe so.\n"
        )
        report_line += (
            "Many Isabelle functions are partially specified (example: `x / 0`, "
            "`hd []`, `inverse 0`). If contextual premises cannot constrain operands "
            "into the domain, the goal is unprovable — refute it.\n"
        )
        # Declarative-style guidance, shared verbatim by the major (planner) and the
        # worker (prover) so the two cannot drift. Interaction forks (focused Q&A /
        # adjudication, not proof construction) do NOT receive it.
        declarative_style = (
            "Prove like a mathematician, not a machine:\n"
            "- Write the proof as you would on paper: use `Have` to state intermediate "
            "results, `Obtain` to introduce the objects you need, and `Suffices` or case "
            "splits to break the goal down.\n"
            "- Typically, decompose until each subgoal is simple enough for `Obvious` to close.\n"
            "- Some trivial facts (e.g. `prime 7`) may not be found by `query` — declare them "
            "with `Have` and prove them with `Obvious`.\n"
            "- Treat the low-level single-step ops (`Rewrite`, `Derive`) as an escape hatch, "
            "not the default — reach for them only on rare occasions when you genuinely need "
            "to spell out a fine-grained inference step.\n"
        )
        if self.is_major:
            # The main agent's job is to formalize a PLAN (BFS skeleton + delegate),
            # not to prove stepwise. The worker gets its own structured body (intro +
            # shared declarative-style guidance + points); interaction forks keep the
            # legacy body in the final `else`. Gate-aware lemma step: when
            # the global-lemma gate is on, steer to declare-then-delegate; otherwise
            # keep the legacy prove-under-global.
            lemma_step = ("declare it as a `Have` under `global`, then dispatch a "
                          "sub-agent to prove it"
                          if self.gate_global_lemma_proofs
                          else "prove it as a `Have` under `global`")
            body = (
                "You are a formal theorem-proving agent. Your first job is not to prove the "
                "goal step by step — it is to formalize a *plan* for the proof. The MCP tools "
                "below are the medium in which you write that plan; the goal and the current "
                "(incomplete) plan are in `./proof.yaml`.\n"
                "\n"
                "Work breadth-first:\n"
                "1. Formalize the top-level structure first — decompose the goal into a few "
                "subgoals / intermediate lemmas (`Have`, `Suffices`, case splits), leaving each "
                "proof as a hole. Don't dive into any single branch.\n"
                "2. Refine one layer at a time, leaving deeper holes as you go.\n"
                f"3. Delegate — call `{self.tool_name(TOOL_SUBAGENT)}` on each non-trivial "
                "subgoal or lemma instead of working it out yourself.\n"
                f"4. If you need a background lemma, `{self.tool_name(TOOL_SEARCH)}` for it "
                f"first; if it truly doesn't exist, {lemma_step}.\n"
                "\n"
                + declarative_style +
                "\n"
                "Holes are expected:\n"
                "- Declaring structure and leaving holes is good — move on, don't grind.\n"
                "- An unproved goal shows as `Unfinished Proof`, not an error — that's expected; "
                "don't rush to close holes depth-first.\n"
                "\n"
                "Also:\n"
                "- " + report_line +
                "- Be concise in text output.\n"
                "- Done when every hole is discharged (by you or your sub-agents) and no errors remain.\n"
            )
        elif self.is_worker:
            # The worker is handed one specific goal to prove (the planner already laid
            # out the surrounding skeleton). Structured as intro + the shared
            # declarative-style guidance + the remaining points concatenated directly.
            body = (
                "You are a formal theorem-proving agent. You have been handed a specific "
                "goal to prove; it and the current (incomplete) proof are in `./proof.yaml`.\n"
                "\n"
                + declarative_style +
                "\n"
                "If a sub-part would derail your main line of reasoning, hand it to a "
                f"sub-agent with `{self.tool_name(TOOL_SUBAGENT)}` rather than proving it inline.\n"
                "The goal may rely on background lemmas that are not yet available. "
                f"Search for them with `{self.tool_name(TOOL_SEARCH)}` first; "
                + self._lemma_guidance(self.is_major) +
                report_line +
                "Be concise in text output.\n"
                "Continue until the goal is fully proved and no errors remain.\n"
            )
        else:
            # Interaction forks (focused Q&A / adjudication, not proof construction)
            # keep the legacy body unchanged.
            body = (
                "You are a formal theorem proving agent.\n"
                "A proof goal and an incomplete proof are provided in `./proof.yaml` under the current directory.\n"
                "Analyze the proof goal, plan a proof, and complete it using the MCP proof tools.\n"
                "Continue until no errors remain.\n"
                + report_line +
                "The goal may rely on background lemmas that are not yet available. "
                f"Search for them with `{self.tool_name(TOOL_SEARCH)}` first; "
                + self._lemma_guidance(self.is_major) +
                "Be concise in text output.\n"
            )
        PROMPT = (
                body +
                "\n"
                "## Tools\n"
                f"- {self.tool_name(TOOL_EDIT)}: Fill, insert, or amend proof steps (your primary tool)\n"
                f"- {self.tool_name(TOOL_DELETE)}: Delete proof steps\n"
                f"- {self.tool_name(TOOL_COMMENT)}: Comment out or uncomment proof steps\n"
                f"- {self.tool_name(TOOL_SEARCH)}: Search for theorems, constants, types, and rules; help you understand unfamiliar terms\n"
                f"- {self.tool_name(TOOL_READ)}: Recall proof state from `proof.yaml`. Use only when you have lost track.\n"
                f"- {self.tool_name(TOOL_RECALL_REMOVED)}: Browse deleted proof steps that were archived before removal.\n"
                f"- {self.tool_name(TOOL_REQUEST_LEMMAS)}: {config.request_tool_description()}\n"
                f"- {self.tool_name(TOOL_REFRESH)}: Reset the conversation and start over (the proof tree is kept). "
                "Write a briefing for your future self in `briefing` — it becomes your only memory. "
                "Use when your edits keep failing.\n"
            )
        parts = [PROMPT]
        # report is shown to workers only.
        if self.is_worker:
            parts.append(
                f"- {self.tool_name(TOOL_REPORT)}: Report that the goal is unprovable (refute) or that you give up (surrender)\n"
            )
        # subagent/cancel_subagent are dispatch tools — shown to dispatchers (the main
        # agent AND workers, which may delegate nested sub-goals), not interaction forks.
        if self.is_major or self.is_worker:
            parts.append(
                f"- {self.tool_name(TOOL_SUBAGENT)}: Launch a sub-agent to prove a subgoal whose proof would derail your main line of reasoning.\n"
                f"- {self.tool_name(TOOL_CLOSE_SUBAGENT)}: Cancel and remove a sub-agent you dispatched (the sub-agent is terminated; to resume it instead, call `subagent` again).\n"
            )
        return "".join(parts)

    async def initial_prompt(self) -> str:
        """The initial user message to start the proof session, memoized.

        Cached because resolving worker-suggested lemma statements costs an RPC,
        and the content is fixed for the session's lifetime (header / suggestions
        / lemmas / boilerplate don't change — proof state is delivered via
        proof.yaml, not here). The cache lets repeat callers (context compaction,
        restart, `_find_recent_start`'s message count) reuse it for free."""
        if self._initial_prompt_cache is None:
            self._initial_prompt_cache = await self._compute_initial_prompt()
        return self._initial_prompt_cache

    async def _compute_initial_prompt(self) -> str:
        """Build the initial user message (uncached — call `initial_prompt`)."""
        # Render the proof scope for its side effect: ``update_line=True``
        # populates each node's ``.line`` (shown by drivers that enable
        # ``quickview_line_numbers``). The rendered text itself is unused — the
        # proof state is delivered to the agent via ``proof.yaml``. Because
        # ``initial_prompt`` memoizes, this runs once per session; on later
        # compaction/restart paths the drivers' ``refresh_YAML(update_line=True)``
        # keeps ``.line`` current before the cached prompt is reused.
        self.print_proof_scope(0, MyIO(StringIO()), update_line=True, show_warnings=True)

        if self.is_worker:
            target = self.role.target  # type: ignore[attr-defined]  — is_worker ⟹ role is Role_Worker
            if isinstance(target, Have):
                header = f"Prove the lemma `{target.name}`: {target.statement['english']}\n"  # type: ignore[attr-defined]  — isinstance(target, Have) narrowing is erased by @proof_operation's type[Any] return
            else:
                # The worker's whole target IS its scope, so it has no short id
                # to name (relativizing to itself is empty) — name it in prose.
                header = "Prove the following goal.\n"
            guidance = ""
            if isinstance(self.role, Role_Worker):
                g = []
                sugg = self.role.suggestions.strip()
                if sugg:
                    g.append(sugg)
                block = await self._render_useful_lemmas()
                if block:
                    g.append(block)
                if g:
                    guidance = "\n" + "\n\n".join(g) + "\n\n"
            if self.system_prompt() is not None:
                return (
                    header + guidance
                    + "Complete the proof using the MCP proof tools.\n"
                    "The proof state is in `proof.yaml` — read it to see the goal and current proof."
                )
            else:
                return (
                    header + guidance
                    + "The proof state is in `proof.yaml` — read it to see the goal and current proof.\n"
                    f"Analyze the proof goal, plan a proof, and complete it using tools `{self.tool_name(TOOL_EDIT)}` and `{self.tool_name(TOOL_DELETE)}`.\n"
                    "Continue building the proof until no error remains.\n"
                    "If the goal itself looks flawed or unprovable, or you want to "
                    f"give up — report it with `{self.tool_name(TOOL_REPORT)}`."
                )
        elif self.system_prompt() is not None:
            return (
                "Complete the proof using the MCP proof tools.\n"
                "The proof state is in `proof.yaml` — read it to see the goal and current proof."
            )
        else:
            # No system prompt (e.g. Codex driver): fold the planner-only hint
            # into the initial message, mirroring system_prompt()'s planner_hint.
            planner_hint = (
                "The goal may rely on background lemmas that are not yet available. "
                f"Search for them with `{self.tool_name(TOOL_SEARCH)}` first; "
                + self._lemma_guidance(True)
            ) if self.is_major else ""
            return (
                "An incomplete proof is provided in `proof.yaml` — read it to see the goal and current proof.\n"
                f"Analyze the proof goal, plan a proof, and complete it using tools `{self.tool_name(TOOL_EDIT)}` and `{self.tool_name(TOOL_DELETE)}`.\n"
                "Continue building the proof until no error remains.\n"
                f"{planner_hint}"
                "A proof goal can be buggy and thus unprovable — "
                f"call `{self.tool_name(TOOL_REPORT)}` with your analysis if you believe so."
            )

    def retry_prompt(self, unfinished_nodes: set['Node']) -> str:
        """Return the retry message when proof steps remain incomplete."""
        # `_display_id` returns "" for the worker's own scope root; drop those so
        # the list names only addressable descendants.
        step_ids = [s for s in (self._display_id(node.id) for node in unfinished_nodes if node.id) if s]
        if step_ids:
            steps_desc = f"Steps {', '.join(step_ids)} are incomplete. "
        else:
            steps_desc = "The proof is incomplete. "
        return (
            steps_desc
            + f"You must call the `{self.tool_name(TOOL_EDIT)}` tool to complete the steps. "
            + "Continue building the proof until `proof.yaml` contains no remaining errors."
        )

    def tool_name(self, t: tool) -> str:
        """Translate abstract tool id to the name the LLM sees.
        Base implementation returns identity; drivers override."""
        return t

    def transform_tool_schema(self, name: str, schema: dict) -> dict:
        """Per-driver rewrite of a tool's advertised JSON input schema.

        Base implementation returns it unchanged; drivers override to apply the
        schema passes their model/client needs (e.g. dereferencing ``$ref`` for a
        client that drops it). Applied by ``_tool_schemas_for`` to every advertised
        tool, so future passes compose here rather than scattering per call site.
        Mirrors ``tool_name``."""
        return schema

    def is_proof_tool(self, external_name: str) -> bool:
        """Check whether an external tool name corresponds to a proof tool."""
        return any(self.tool_name(t) == external_name for t in ALL_PROOF_TOOLS)

    def adopt_task(self, task: 'asyncio.Task') -> 'asyncio.Task':
        """Register a background task owned by this session. Still-pending
        tasks are cancelled and awaited by ``close()``. Completed tasks
        remove themselves via the done-callback."""
        self._owned_tasks.add(task)
        task.add_done_callback(self._owned_tasks.discard)
        return task

    async def close(self):
        """Clean up the session and release resources.
        Subsessions do not close shared log files — only major sessions do."""
        # Kill owned background tasks FIRST — and before the is_major early-out:
        # a tool task suspended on a non-forking interaction (e.g. the
        # large-delete gate) must not outlive its session, and such tasks
        # mostly belong to worker sub-sessions.
        pending = [t for t in self._owned_tasks if not t.done()]
        for t in pending:
            t.cancel()
        for t in pending:
            with contextlib.suppress(BaseException):
                await t
        if not self.is_major:
            return
        # Tear down any worker sub-agents still attached to the tree (running or
        # parked on a review/lemma future) so their asyncio tasks don't leak on
        # shutdown. `aclose` is idempotent and tolerates already-finished workers.
        if getattr(self, 'root', None) is not None:
            await self.root.aclose_all_subagents()
        # Major session: write end markers and close log files
        if self.log_dir is not None:
            session_end = {
                "event": "SESSION_END",
                "timestamp": datetime.now().isoformat(),
            }
            if self.interaction_log_file is not None:
                self._append_yaml(self.interaction_log_file, session_end)
                self.interaction_log_file.close()
                self.interaction_log_file = None
            if self.proofs_log_file is not None:
                self._append_yaml(self.proofs_log_file, session_end)
                self.proofs_log_file.close()
                self.proofs_log_file = None
            if self.proof_oprs_log_file is not None:
                self._append_yaml(self.proof_oprs_log_file, session_end)
                self.proof_oprs_log_file.close()
                self.proof_oprs_log_file = None
            if self.retrieval_log_file is not None:
                self._append_yaml(self.retrieval_log_file, session_end)
                self.retrieval_log_file.close()
                self.retrieval_log_file = None
            if self.missing_lemmas_log_file is not None:
                self._append_yaml(self.missing_lemmas_log_file, session_end)
                self.missing_lemmas_log_file.close()
                self.missing_lemmas_log_file = None
            if self._meta_log_writer is not None:
                self._log_meta("SESSION_END")
                self._meta_log_writer.close()
                self._meta_log_writer = None
            if self._meta_log_file is not None:
                self._meta_log_file.close()
                self._meta_log_file = None
            if getattr(self, '_atexit_registered', False):
                import atexit
                atexit.unregister(self._atexit_close_meta)
                self._atexit_registered = False

        # Clean up the context session reference
        try:
            if _session_var.get() is self:
                _session_var.set(None)  # type: ignore
        except LookupError:
            pass

    async def initialize(self, root: Root):
        match self.role:
            case Role_Major():
                if hasattr(self, 'root'):
                    raise InternalError("The session is already initialized.")
                self.root = root
                self.working_block = root
                await root._refresh_me_alone(auto_intro=True)
                sp = self.system_prompt()
                if sp is not None:
                    self._log_meta("SYS_PROMPT", text=sp)
                self.log_initial_prompt(await self.initial_prompt())
            case Role_Worker() | Role_Interaction():
                assert self.root is root
                self.working_block = (
                    self.role.target if isinstance(self.role, Role_Worker)
                    else root)
                await self._prefetch_worker_premises()
                # Baseline the resume-notice diff: everything in scope now counts as
                # already-shown (it is in the opening proof.yaml). No-op for non-workers.
                self._seed_reported_scope_facts()
                # A worker's opening message is `initial_prompt()` (sent by the
                # driver loop); interaction forks use their own prompts instead,
                # so only log here for genuine workers.
                if self.is_worker:
                    self.log_initial_prompt(await self.initial_prompt())

    def retrieval_state(self) -> Minilang_State:
        """The Isabelle proof state that name lookups / the `query` tool resolve
        against: the latest refreshed state of the block the agent is currently
        working in (`working_block`), so retrieval sees that block's local
        context (variables, local facts). Falls back to the root's state before
        `working_block` is set (e.g. the base/test session)."""
        if self.working_block is not None:
            return self.working_block.latest_refreshed_state()
        return self.root.ml_state

    def resolve_context_at(self, step_id: str) -> Minilang_State:
        """Resolve an agent-supplied step id to the proof state at that step,
        for use as the `query` tool's retrieval context.

        The id may name an existing node OR an unfilled proof slot (the same
        address space `fill`/`subagent` accept), so the agent can take the
        context at the very slot it is about to fill:

        - **open slot** `P.k` (no node yet): the state in effect at that slot,
          i.e. `P`'s state after all current children — `P._resulting_state_of_all_children()`
          (== the previous sibling's `resulting_state()`).
        - **existing node, evaluated successfully**: StdBlock → state after its
          beginning op; Leaf/other → its `resulting_state()`.
        - **existing node, failed/cancelled** (e.g. a trailing failed `Obvious`
          the agent means to replace): its `ml_state` — the state in effect just
          before it ran (the position the agent would re-fill).

        A position may, however, sit in a CANCELLED or head-FAILED region whose
        server-side proof state has been reset (`StdBlock._cancel` /
        `Node._cancel` reset the relevant `Minilang_State`) or was never
        initialized (a block whose beginning op failed). Such a state has no live
        server-side name, so feeding it to retrieval would surface an opaque
        `beginning_state_not_found` from ML. We detect it with `.initialized()`
        and raise a clear ValueError instead — no silent substitution.

        Raises ValueError on a genuinely nonexistent id, or when the resolved
        position has no usable (initialized) proof state."""
        abs_id = self._resolve_display_id(step_id)
        try:
            resolved = self.root.locate_node_or_slot(abs_id)
        except NodeNotFound:
            raise ValueError(f"Step {step_id} not found.")
        dead_region_msg = (
            f"Step {step_id} lies in a cancelled or failed region of the proof "
            "and has no usable proof state; cannot use it as query context.")
        if isinstance(resolved, Resolved_Slot):
            # A slot only ever belongs to a block (NonLeaf_Node) — Leaf nodes
            # expose no slot (`Node._id_of_openning_prf_to_fill` → None).
            assert isinstance(resolved.parent, NonLeaf_Node)
            st = resolved.parent._resulting_state_of_all_children()
            if not st.initialized():
                raise ValueError(dead_region_msg)
            return st
        node = resolved.node
        if not _status_can_continue(node.status.status):
            # Failed/cancelled node (e.g. a to-be-replaced trailing Obvious):
            # use its before-state — the context at the slot it occupies — but
            # only when that state is still live (the first failure after a run
            # of successes); a node in a deeper cancelled region had its
            # before-state reset and is rejected above.
            if not node.ml_state.initialized():
                raise ValueError(dead_region_msg)
            return node.ml_state
        if isinstance(node, StdBlock):
            return node._state_after_beginning()
        return node.resulting_state()

    def _log(self, log_file_handle: Any, event_type: str, debug_messages: Callable[[], list[str]] | None, **data):
        """
        Internal method to log events to YAML and debug logger.

        Args:
            log_file_handle: Open file handle for the log file
            event_type: Type of event (e.g., "MODEL_OUTPUT", "PROOF_OPERATION")
            debug_messages: Callable that returns list of debug messages (only called if logger is not None)
            **data: Additional data fields for the YAML log entry
        """
        role = self.role_label
        if log_file_handle is not None:
            log_entry = {
                "event": event_type,
                "timestamp": datetime.now().isoformat(),
                "role": role,
                **data
            }
            self._append_yaml(log_file_handle, log_entry)
        self._log_meta(event_type, **data)  # _log_meta stamps role itself
        if self.logger is not None and debug_messages is not None:
            for msg in debug_messages():
                self.logger.debug(f"[{role}] {msg}")
        self.on_log(event_type, data)

    # Model interaction logging methods
    def log_model_output(self, text: str):
        """Log model text output to interaction.yaml."""
        self._log(self.interaction_log_file, "MODEL_OUTPUT",
                  lambda: [f"[MODEL] {text}"], text=text)

    def log_model_thinking(self, thinking: str):
        """Log model thinking output to interaction.yaml."""
        self._log(self.interaction_log_file, "MODEL_THINKING",
                  lambda: [f"[THINKING] {thinking}"], thinking=thinking)

    def log_tool_call(self, tool_name: str, tool_input: dict[str, Any]):
        """Log tool call to interaction.yaml."""
        self._log(self.interaction_log_file, "TOOL_CALL",
                  lambda: [f"[TOOL_CALL] {tool_name}: {tool_input}"],
                  tool_name=tool_name, tool_input=tool_input)

    def log_tool_response(self, tool_name: str, response: str):
        """Log tool response to interaction.yaml."""
        self._log(self.interaction_log_file, "TOOL_RESPONSE",
                  lambda: [f"[TOOL_RESPONSE] {tool_name}: {response}"],
                  tool_name=tool_name, response=response)

    def log_AoA_opr(self, message: str):
        """Log an AoA operation message to interaction.yaml."""
        self._log(self.interaction_log_file, "AOA_OPR",
                  lambda: [f"[AOA] {message}"], message=message)

    def warn_AoA_opr(self, message: str):
        """Log an AoA warning to interaction.yaml and logger at WARNING level."""
        self._log(self.interaction_log_file, "AOA_WARNING", None, message=message)
        if self.logger is not None:
            self.logger.warning(f"[{self.role_label}] [AOA_WARN] {message}")

    def log_interaction(self, tool_name: str, prompt: str):
        """Log interaction prompt to interaction.yaml."""
        self._log(self.interaction_log_file, "INTERACTION",
                  lambda: [f"[INTERACTION] {tool_name}: {prompt}"],
                  tool_name=tool_name, prompt=prompt)

    def log_retrieval(self, query: str, results: list[str], *, quiet: bool = False):
        """Log a retrieval query and its results to retrieval.yaml.
        If quiet=True, skip logger output (useful when already logged as TOOL_RESPONSE)."""
        self._log(self.retrieval_log_file, "RETRIEVAL",
                  None if quiet else lambda: [f"[RETRIEVAL] {query!r}\n" + "\n".join(f"  {r}" for r in results)],
                  query=query, results=results)

    def log_missing_lemmas(self, trigger: str, lemmas: list):
        """Record a missing-lemma report to missing_lemmas.yaml — either a
        survey answer (trigger "query_interval" / "worker_end" / "session_end")
        or a worker's
        `request_lemmas` wish-list (trigger "request_lemmas"). ``lemmas`` is a
        list of plain dicts as reported; an empty list is still logged so the
        external watcher can tell "surveyed, nothing missing" from "no survey"."""
        self._log(self.missing_lemmas_log_file, "MISSING_LEMMAS",
                  lambda: [f"[MISSING_LEMMAS] {trigger}: {len(lemmas)} reported"],
                  trigger=trigger, lemmas=lemmas)
        # Within-run anti-repeat memory: this is the single funnel for both
        # survey answers and request_lemmas wish-lists, so extending here
        # covers everything later surveys must not re-report.
        self.runtime.reported_missing_lemmas.extend(
            l for l in lemmas if isinstance(l, dict))

    def log_initial_prompt(self, prompt: str):
        """Log the initial prompt (planner or worker) to interaction.yaml.

        The planner used to log this to ``meta`` only; workers logged it nowhere,
        so a sub-agent's opening message was invisible in the DEBUG stream. Route
        both through here (interaction.yaml + meta + debug) for symmetry."""
        self._log(self.interaction_log_file, "PROMPT",
                  lambda: [f"[PROMPT] Initial prompt:\n{prompt}"],
                  subtype="initial",
                  text=prompt)

    def log_retry(self, unfinished_nodes: set[Any], retry_prompt: str):
        """Log retry attempt to interaction.yaml."""
        node_ids = [str(node.id) for node in unfinished_nodes]
        self._log(self.interaction_log_file, "PROMPT",
                  lambda: [f"[PROMPT] Unfinished nodes: {[node.id for node in unfinished_nodes]}",
                           f"[PROMPT] {retry_prompt}"],
                  subtype="retry",
                  text=retry_prompt,
                  unfinished_nodes=node_ids)

    def log_budget_exhausted(self, reason: str):
        self._log(self.interaction_log_file, "BUDGET_EXHAUSTED",
                  lambda: [f"[BUDGET] {reason}"], reason=reason)

    def check_budget(self) -> bool:
        """Check budget limits. If exceeded, set quit_info and return True."""
        if self.quit_info is not None:
            return self.quit_info.is_terminal

        reason = None
        if self._budget_start_time is not None:
            elapsed = time() - self._budget_start_time
            if elapsed > self.timeout_seconds:
                reason = f"timeout ({elapsed:.0f}s > {self.timeout_seconds}s)"
        if reason is None and self.total_tool_calls >= self.max_tool_calls:
            reason = f"tool call limit ({self.total_tool_calls} >= {self.max_tool_calls})"
        if reason is None and self._retry_count >= self.max_retries:
            reason = f"retry limit ({self._retry_count} >= {self.max_retries})"

        if reason is not None:
            self.quit_info = ResourceExhausted(reason)
            self.log_budget_exhausted(reason)
            return True
        return False

    def _should_struggle_checkpoint(self) -> bool:
        """True when this worker's edit/delete counters hit the struggle
        thresholds.  Only fires for workers; planners and interaction forks
        are excluded.  Drivers may override."""
        if not self.is_worker:
            return False
        # A headless (auto-prove-general) prover must never park on a difficulty
        # checkpoint: its requester is not an adjudicating planner, so a difficulty
        # yield would surface on the requesting worker's channel with no one able to
        # resolve it. Disabling the checkpoint keeps the prover's outcomes terminal-only.
        if self.role.headless:  # type: ignore[union-attr]  — is_worker ⟹ Role_Worker
            return False
        return (self._session_delete_count >= self._struggle_delete_threshold
                and self._session_edit_count >= self._struggle_edit_threshold)

    def _reset_struggle_counters(self) -> None:
        """Zero the counters and lower thresholds for subsequent checkpoints.
        Drivers may override to change the escalation policy."""
        self._session_delete_count = 0
        self._session_edit_count = 0
        _is_sub_subagent = (isinstance(self.role, Role_Worker)
                            and self.parent is not None
                            and isinstance(self.parent.role, Role_Worker))
        if _is_sub_subagent:
            self._struggle_delete_threshold = 3
            self._struggle_edit_threshold = 10
        else:
            self._struggle_delete_threshold = 3
            self._struggle_edit_threshold = 15

    async def run_missing_lemma_survey(self, trigger: str) -> None:
        """Fork an ``Interaction_MissingLemmaSurvey`` and record its report to
        ``missing_lemmas.yaml``. No-op when the survey is disabled
        (``AOA_MISSING_LEMMA_SURVEY`` unset) or for interaction forks.
        Best-effort: a failing survey fork is logged and swallowed — the
        survey must never break the proof loop."""
        if self._missing_lemma_survey_interval <= 0 or self.is_interaction:
            return
        self._query_calls_since_survey = 0
        _t0 = time()
        try:
            lemmas = await self.launch_interaction(
                Interaction_MissingLemmaSurvey(trigger))
        except Exception as e:
            self.warn_AoA_opr(
                f"Missing-lemma survey fork failed: {type(e).__name__}: {e}")
            return
        finally:
            # The survey is instrumentation, not proof work: exclude its
            # wall-clock from the session budget (用户拍板 2026-06-11), else
            # every survey eats into timeout_seconds and confounds the
            # before/after comparison the loop exists to make.
            if self._budget_start_time is not None:
                self._budget_start_time += time() - _t0
        self.log_missing_lemmas(trigger, lemmas)

    # Proof tree logging methods
    def log_proof_operation(self, step: str, operation: str, details: dict[str, Any]):
        """Log proof operation to proof_oprs.yaml."""
        self._log(self.proof_oprs_log_file, "PROOF_OPERATION",
                  None,
                  step=step, operation=operation, details=details)

    def log_proof_tree_snapshot(self, snapshot_type: str):
        """Log proof tree snapshot to proofs.yaml."""
        tree_yaml = self.root.print_string(0)
        self._log(self.proofs_log_file, "PROOF_TREE_SNAPSHOT", None,
                  snapshot_type=snapshot_type, tree_yaml=tree_yaml)

    def _log_cost(self) -> None:
        self.log_AoA_opr(
            f"total: input={self.total_input_tokens} "
            f"cache_write={self.total_cache_creation_input_tokens} "
            f"cache_read={self.total_cache_read_input_tokens} "
            f"output={self.total_output_tokens} tokens, "
            f"cost=${self.total_cost_usd:.4f} "
            f"tool_calls={self.total_tool_calls} "
            f"isabelle_time={self.total_isabelle_time:.2f}s "
            f"model_time={self.total_model_time:.2f}s "
            f"quota_wait_time={self.total_quota_wait_time:.2f}s")

    def log_proof(self):
        """
        Log the current proof tree and cost summary to the log directory.
        """
        self._log_cost()
        if self.log_dir is not None:
            proof_yaml_path = self.log_dir / "proof.yaml"
            try:
                with open(proof_yaml_path, 'w', encoding='utf-8') as f:
                    self.root.print(0, MyIO(f))
                if self.logger is not None:
                    self.logger.debug(f"[{self.role_label}] [PROOF] Written to {proof_yaml_path}")
            except Exception as e:
                if self.logger is not None:
                    self.logger.error(f"Failed to write proof to {proof_yaml_path}: {e}")

    def log_proof_operation_error(self, error_message: str, **extra_data):
        """
        Log a proof operation error to proof_oprs.yaml.

        Args:
            error_message: Error message or description
            **extra_data: Additional error-related data (e.g., errors list, operation details)
        """
        self._log(self.proof_oprs_log_file, "OPERATION_ERROR",
                  None,
                  error_message=error_message,
                  **extra_data)

    def log_cost(self, msg: str):
        """Log cost/usage information to interaction log."""
        self._log(self.interaction_log_file, "COST",
                  lambda: [f"[COST] {msg}"], message=msg)

    def debug_info(self, msg: str):
        """Log debug information to interaction log and logger."""
        self._log(self.interaction_log_file, "DEBUG",
                  lambda: [f"[DEBUG] {msg}"], message=msg)
    async def run(self):
        raise NotImplementedError("`run` must be implemented by subclass")

    def _reset_view_state(self):
        """Reset UI-hint and deduplication state so the agent re-discovers
        entities and re-emits one-shot notices.  Called on compaction and
        context restart."""
        self.seen_entities.clear()
        self.seen_commands.clear()
        self.seen_manual_note = False
        self.search_summary_count = 0
        self.seen_abbreviations.clear()
        self.showed_suffices_notice = False
        self.shown_hints.clear()
        self.shown_subagent_hints.clear()
        self.showed_fill_hint = False
        self.showed_cancelled_notice = False
        self.shown_HAVE_fact_names.clear()
        # Unlike the dedup fields above, reported_scope_facts has NO render surface that
        # naturally re-populates it (only the resume notice emits it). After a reset the
        # worker re-reads the current proof.yaml (full premises), so `.clear()` would dump
        # the whole premise set as "new" on the next park. Re-seed to the current
        # before-target names instead (no-op for non-workers).
        self._seed_reported_scope_facts()

    @property
    def proof_scope_root(self) -> 'Node':
        """The node whose subtree defines this session's proof scope: the
        worker's ``target`` (a worker renders/checks only ``target.sub_nodes`` —
        see ``print_proof_scope``), otherwise the whole ``root``. This is the
        single source of truth for "what subtree does this session render to
        ``proof.yaml``"; line numbers and scoped views outside it are stale."""
        return self.role.target if self.is_worker else self.root  # type: ignore[attr-defined]  — is_worker ⟹ role is Role_Worker

    # --- Worker-scoped relative step ids (no-ops for non-workers) ----------
    def _display_id(self, abs_id: str) -> str:
        """Outbound: render an absolute node id the way the current session
        should see it.  A worker gets the id relative to its proof scope (or
        ``EXTERNAL_STEP`` if out of scope); everyone else gets it unchanged."""
        if not self.is_worker:
            return abs_id
        rel = _relativize_id(abs_id, self.proof_scope_root.id)
        return EXTERNAL_STEP if rel is None else rel

    def _resolve_display_id(self, shown_id: str) -> str:
        """Inbound: turn an id the worker supplied (relative to its scope) back
        into the absolute id the tree uses.  Identity for non-workers."""
        return _absolutize_id(shown_id, self.proof_scope_root.id) if self.is_worker else shown_id

    def _postprocess_outbound_text(self, text: str) -> str:
        """Outbound free text shown to the agent. Two passes:
        (1) resolve `the out-of-scope variable <internal>` (emitted by
            Unify_Diagnostic) to the variable's external name plus the step that
            discarded it — for ALL roles;
        (2) for a worker, relativize each ``step``/``goal``/``Subgoal`` id
            reference, masking out-of-scope ones as ``EXTERNAL_STEP``."""
        text = self._resolve_outscope_vars(text)
        if not self.is_worker:
            return text
        prefix = self.proof_scope_root.id
        def repl(m: 're.Match[str]') -> str:
            rel = _relativize_id(m.group(3), prefix)
            return f"{m.group(1)}{m.group(2)}{EXTERNAL_STEP if rel is None else rel}{m.group(4)}"
        return _ID_IN_TEXT_RE.sub(repl, text)

    def _resolve_outscope_vars(self, text: str) -> str:
        """Rewrite each `the out-of-scope variable <internal>` (the raw skolem
        name emitted by Unify_Diagnostic) to `the out-of-scope variable
        <external> (removed by step <id>)`, using the discarded-vars map
        collected over the proof scope. Falls back to `an out-of-scope variable`
        when the internal name is not in the map — so a raw skolem name is never
        shown to the agent even if no recording step was found."""
        if "out-of-scope variable" not in text:
            return text
        discarded = self.proof_scope_root._collect_discarded_vars({})
        def repl(m: 're.Match[str]') -> str:
            hit = discarded.get(m.group(1))
            if hit is None:
                return "an out-of-scope variable"
            external, step = hit
            return (f"the out-of-scope variable {external} "
                    f"(removed by step {self._display_id(step)})")
        return _OUTSCOPE_VAR_RE.sub(repl, text)

    def _absolutize_text(self, text: str) -> str:
        """Inbound free text from a worker (e.g. a refutation reason surfaced to
        the planner): expand each relative id reference back to absolute.  A
        worker can only express in-scope ids, so this never hits the
        out-of-scope case.  Identity for non-workers."""
        if not self.is_worker:
            return text
        prefix = self.proof_scope_root.id
        return _ID_IN_TEXT_RE.sub(
            lambda m: f"{m.group(1)}{m.group(2)}{_absolutize_id(m.group(3), prefix)}{m.group(4)}",
            text)

    def _rebase_suggestion_ids(self, target: 'Node', text: str) -> 'tuple[str, list[str]]':
        """Rewrite step-id references in dispatcher-authored `text` (this
        session is the dispatcher) into the dispatched worker's namespace,
        rooted at `target`.  In-scope refs are relativized in place; refs
        outside `target`'s subtree are left untouched and returned for the
        caller to reject.  Returns ``(rewritten_text, external_refs)``."""
        prefix = target.id
        external: list[str] = []
        def repl(m: 're.Match[str]') -> str:
            abs_id = self._resolve_display_id(m.group(3))   # dispatcher ns -> absolute
            rel = _relativize_id(abs_id, prefix)            # absolute -> recipient ns
            if rel is None:
                external.append(m.group(3))
                return m.group(0)
            return f"{m.group(1)}{m.group(2)}{rel}{m.group(4)}"
        return _ID_IN_TEXT_RE.sub(repl, text), external

    def proof_scope_unfinished_nodes(self) -> 'set[Node]':
        """Return unfinished nodes scoped to this session's proof responsibility.
        Workers check only their target subtree."""
        unfinished: 'set[Node]' = set()
        self.proof_scope_root.unfinished_nodes(unfinished)
        return unfinished

    def newly_completed_topmost(self) -> 'list[Node]':
        """Steps whose whole subtree just became proved and have not yet been
        announced, scoped to this session's proof responsibility.

        A node qualifies when its subtree holds no unfinished node and no
        ancestor inside the scope is also fully proved — i.e. the maximal proved
        subtrees, a non-overlapping antichain. Of those, only ones not previously
        announced are returned (delta), and they are marked announced here so a
        completion is reported once. The flag is reset on any node found
        unfinished, so a step that regresses and is re-proved is announced again.

        The proof-scope root itself is excluded: a fully proved scope is surfaced
        by the caller's dedicated "all goals proven" path, not as a step here."""
        unfinished = self.proof_scope_unfinished_nodes()
        root = self.proof_scope_root
        finished: 'dict[int, bool]' = {}

        def compute(node: 'Node') -> bool:
            # subtree fully proved iff no node in it is unfinished
            ok = node not in unfinished
            if isinstance(node, NonLeaf_Node):
                for c in node.sub_nodes:
                    if not compute(c):
                        ok = False
            finished[id(node)] = ok
            return ok

        compute(root)

        newly: 'list[Node]' = []

        def walk(node: 'Node', ancestor_finished: bool) -> None:
            fin = finished[id(node)]
            if not fin:
                node._completion_announced = False
            elif not ancestor_finished and node is not root:
                # Announce only structured goal blocks: skip bare leaves (a lone
                # solved Obvious is already conveyed by "Filled step X" + the
                # outline) and the declaration-only global env (id_of_goal() is
                # None). Finishedness still propagates below regardless of type,
                # so a finished leaf neither reports nor un-suppresses siblings.
                #
                # Also skip a COMMENTED node: it counts as "finished" only
                # because a comment contributes no unfinished goals (it is not
                # code), NOT because it was proved. Announcing "All proof goals
                # of step N are now completed" for a commented step is misleading
                # — the outline already shows it as `(commented out)`. The flag
                # is left untouched, so if the step is later uncommented and
                # genuinely proved, the completion is reported then.
                if (isinstance(node, NonLeaf_Node)
                        and node.id_of_goal() is not None
                        and node.status.status != EvaluationStatus.Status.COMMENTED
                        and not node._completion_announced):
                    node._completion_announced = True
                    newly.append(node)
            if isinstance(node, NonLeaf_Node):
                child_anc = ancestor_finished or fin
                for c in node.sub_nodes:
                    walk(c, child_anc)

        walk(root, False)
        return newly

    def _edit_verdict(self, step: 'step', action: str) -> "tuple[EditVerdict, WorkerHandle | None]":
        """May this session ``edit``/``delete`` ``step``? Returns (verdict, the
        blocking handle for LOCKED). Scoped to the session's proof scope root
        X_A (= ``role.target`` for a worker, ``root`` for main).

        Two parts: (1) CONFINEMENT (worker only) — the target must lie inside
        ``subtree(X_A)`` (a proper descendant; a new direct child slot of X_A is
        allowed), else OUT_OF_SCOPE. (2) LOCK (all agents) — the target's region
        must not hold another live sub-agent: ``fill``/``insert_before`` lock on
        {target + descendants} ∪ {ancestors below X_A}; ``amend`` locks only on a
        strict-ancestor sub-agent (it tears down its own target's worker via
        ``_amend_child``, and keeps descendants); ``delete`` never locks (it tears
        down whatever it removes).

        For a worker this IGNORES handles at or above X_A (its blocked spawner
        chain) — sound only because the dispatch gate (``_dispatch_blocked_by``)
        keeps live handles an antichain, so no foreign parked worker encloses X_A.
        The two are one inseparable package."""
        stop = self.proof_scope_root
        try:
            node = self.root.locate_node(step)
            new_slot = False
        except NodeNotFound:
            parent_step = step.rsplit('.', 1)[0] if '.' in step else None
            if parent_step is None:
                return (EditVerdict.OUT_OF_SCOPE if self.is_worker else EditVerdict.OK), None
            try:
                node = self.root.locate_node(parent_step)
            except NodeNotFound:
                return (EditVerdict.OUT_OF_SCOPE if self.is_worker else EditVerdict.OK), None
            new_slot = True
        # (1) confinement (worker only)
        if self.is_worker:
            in_scope = (new_slot and node is stop) or _is_strict_ancestor(stop, node)
            if not in_scope:
                return EditVerdict.OUT_OF_SCOPE, None
        # (2) lock (all agents)
        if action == 'delete':
            return EditVerdict.OK, None
        anc_h = _first_worker_in_ancestors(node, stop=stop)
        if action == 'amend':
            return (EditVerdict.LOCKED, anc_h) if anc_h is not None else (EditVerdict.OK, None)
        # fill / insert_before
        if new_slot:
            # the parent's OWN handle blocks (a parked node's blank child slot),
            # but never X_A's own handle (that is the calling worker itself).
            own = node.worker_handle if (isinstance(node, NonLeaf_Node) and node is not stop) else None
            h = anc_h or own
        else:
            h = anc_h or _first_worker_in_subtree(node)
        return (EditVerdict.LOCKED, h) if h is not None else (EditVerdict.OK, None)

    def _global_lemma_gate(self, step: 'step', action: str) -> 'tuple[bool, Node | None]':
        """The global-lemma delegation gate (the caller checks the predicate
        ``is_major and not is_worker and gate_global_lemma_proofs``).

        Returns ``(blocked, dispatch_target)``: ``blocked`` is True iff a
        ``fill``/``insert_before``/``amend`` on ``step`` would write INTO the proof
        body of a global declaration (a fresh child slot directly under a global
        decl, or a target strictly inside one). ``dispatch_target`` is the node the
        error message should tell the major to ``subagent`` on — computed via
        ``_nearest_goal_for_subagent`` (exactly what ``_subagent_tool_logic`` will
        re-resolve), so it is a step the dispatcher accepts: the decl itself for
        Have/Obtain/SetupRewriting, and the Define itself for a deferred Define. If a
        sub-agent is already parked inside that subtree (reachable via ``amend``,
        which does not LOCK on a descendant worker), the live worker's node is
        returned so calling ``subagent`` on it RESUMES it instead of pointing at an
        ancestor the dispatch gate would reject.

        Post-A, a fill directly on a Define resolves ``dispatch_target`` to the
        **Define itself** (``Define._nearest_goal_for_subagent`` returns self), so the
        gate steers the major to ``subagent`` on it — an improvement, since a direct
        fill on a Define is invalid anyway. (Pre-A this was None because the redirect
        walked Define -> GlobalEnv, whose ``_nearest_goal_for_subagent`` returns None —
        NOT via ``_id_of_openning_prf_to_fill``, which the gate never consults.) A
        residual ``None`` (redirect bottoming out at the Root container / GlobalEnv)
        still returns ``(True, None)``; the caller's ``target is not None`` guard then
        falls through to the normal fill-error path. Resolves the target like ``_edit_verdict``."""
        if action not in ('fill', 'insert_before', 'amend'):
            return (False, None)
        try:
            node = self.root.locate_node(step)
            new_slot = False
        except NodeNotFound:
            parent_step = step.rsplit('.', 1)[0] if '.' in step else None
            if parent_step is None:
                return (False, None)
            try:
                node = self.root.locate_node(parent_step)
            except NodeNotFound:
                return (False, None)
            new_slot = True
        if new_slot and _is_direct_global_decl(node):
            target = node._nearest_goal_for_subagent()
        elif _enclosing_global_decl(node) is not None:
            target = node._nearest_goal_for_subagent()
        else:
            return (False, None)
        if target is None:
            return (True, None)
        live = _first_worker_in_subtree(target)
        return (True, live.target if live is not None else target)

    def _dispatch_blocked_by(self, node: 'Node') -> "WorkerHandle | None":
        """For a FRESH ``subagent`` dispatch on ``node`` (one not already holding a
        handle): the existing handle that makes ``node`` comparable to a live
        worker — an ancestor up to X_A, or any descendant — or ``None`` if dispatch
        is allowed. Keeps live handles an antichain. ``stop = X_A`` ignores the
        dispatcher's OWN handle (on X_A) so a worker may dispatch within its own
        territory; the subtree side still rejects dispatch over its own parked
        sub-workers."""
        stop = self.proof_scope_root
        return _first_worker_in_ancestors(node, stop=stop) or _first_worker_in_subtree(node)

    def _enclosing_dispatched_subagent(self, node: 'Node') -> "WorkerHandle | None":
        """The worker THIS session dispatched whose territory ENCLOSES ``node`` —
        the nearest ancestor of ``node`` (within this session's scope) carrying a
        handle this session itself created (``worker_handle.session is self``), or
        ``None``. By the antichain invariant a session's own live handles are
        pairwise incomparable, so at most one lies on any ancestor chain; it is the
        *immediate* sub-agent the caller can actually see and resume/close. Unlike
        ``_first_worker_in_ancestors`` this skips deeper foreign handles (a nested
        grandchild's spawner), so under 3+ levels of nesting it still points the
        caller at the worker IT owns rather than one it cannot operate on."""
        cur = node.parent
        stop = self.proof_scope_root
        while cur is not None and cur is not stop:
            if (isinstance(cur, NonLeaf_Node) and cur.worker_handle is not None
                    and cur.worker_handle.session is self):
                return cur.worker_handle
            cur = cur.parent
        return None

    def _subagent_blocker(self, node: 'Node') -> "WorkerHandle | None":
        """For a ``subagent`` call on ``node`` (START *or* RESUME): the worker I
        dispatched whose territory overlaps ``node`` and which I should resume/close
        instead — or ``None`` if ``node`` is free for me to act on. Covers ``node``
        lying inside one of my parked sub-agents (ancestor side, also catches a
        RESUME aimed at a nested grandchild handle I cannot see) and, only when
        starting fresh, ``node`` enclosing one of mine (descendant side). A foreign
        handle ON ``node`` itself with no such enclosing worker is an orphan —
        impossible after cascade-close — and is deliberately returned as ``None`` so
        the caller's assertion surfaces the broken invariant rather than masking it."""
        anc = self._enclosing_dispatched_subagent(node)
        if anc is not None:
            return anc
        if node.worker_handle is None:  # type: ignore[attr-defined]  — node is a StdBlock (caller asserts); base Node lacks worker_handle
            return _first_worker_in_subtree(node)
        return None

    # Maximum worker-nesting depth for THIS session's driver (main -> worker is
    # layer 1, its sub-worker layer 2, ...). Overridable per driver as a class var
    # (e.g. 1 to permit only a single layer of sub-agents). Defaults to the
    # module-level ``SUBAGENT_NESTING_DEPTH``.
    SUBAGENT_NESTING_DEPTH: int = SUBAGENT_NESTING_DEPTH

    def _subagent_nesting_depth(self) -> int:
        """How many ``Role_Worker`` sessions enclose this one, counting itself —
        i.e. this session's worker-nesting layer (main = 0, its worker = 1, that
        worker's sub-worker = 2, ...). A worker fork's ``parent`` is its dispatcher
        (``WorkerHandle._run`` forks with ``parent = handle.session``), so the
        ``parent`` chain records the full delegation stack; interaction forks on the
        chain are skipped (only ``Role_Worker`` counts)."""
        depth, s = 0, self
        while s is not None:
            if isinstance(s.role, Role_Worker):
                depth += 1
            s = s.parent
        return depth

    def _can_offer_dispatch_tools(self) -> bool:
        """Whether the dispatch tools (`subagent` / `cancel_subagent`) should be
        advertised to this session. True for a dispatcher — the main agent or a
        worker — that is NOT already at the maximum nesting depth; a sub-sub-agent
        (depth == SUBAGENT_NESTING_DEPTH) cannot delegate further, so the tools are
        hidden from it entirely. Interaction forks never dispatch and so never get
        them. Shared by _tool_schemas_for (MCP registration / APIDriver schemas) and
        the Claude SDK allow-list (_role_allowed_tools); the runtime guard in
        _subagent_tool_logic remains as a backstop."""
        return ((self.is_major or self.is_worker)
                and self._subagent_nesting_depth() < self.SUBAGENT_NESTING_DEPTH)

    async def _prefetch_worker_premises(self) -> None:
        """Resolve the standard-printed propositions of every fact in scope before the
        worker's target and cache them (ascii name -> IsaTerm).  Called at worker
        ``initialize``, and re-called when the in-scope facts change (see below).

        The facts in scope BEFORE the target are immutable for the worker's lifetime
        with ONE exception: a ``request`` call auto-proves general helper lemmas into
        the global env — i.e. into the facts in scope before the target. (A ``request``
        constraint instead amends the worker's OWN target, not a before-target fact.)
        The ``request`` tool therefore re-invokes this method when the worker resumes,
        so the cache picks up the new lemmas. The method is idempotent: it just
        recomputes ``_worker_premise_cache``.
        """
        if not self.is_worker:
            return
        target = self.role.target # type: ignore
        # `_ctxt_before_me()` is the context at the target's position, which is
        # exactly `target.ml_state` (Node's "state before executing the node"),
        # so resolve the before-target hyps against that state. `ml_state` is a
        # `Node` attribute (no StdBlock-only access), so no type guard is needed.
        names = [n.ascii for n in target._ctxt_before_me().hyps]
        pairs = await target.ml_state.fact_propositions(names)
        self._worker_premise_cache = {n: IsaTerm.from_isabelle(p) for n, p in pairs}

    def _seed_reported_scope_facts(self) -> None:
        """Baseline the resume-notice diff: record every fact currently in scope BEFORE
        the worker's target as already reported, keyed to its CURRENT proposition (the
        live-hyps raw ascii), so the next ``consume_new_scope_facts_notice`` surfaces
        only facts the parent adds — or amends under the same name — afterwards.

        Keyed off ``target._ctxt_before_me().hyps`` — the SAME set the notice iterates —
        NOT ``_worker_premise_cache.keys()``. The cache drops names the ML side cannot
        resolve (``fact_propositions``; e.g. a before-target ``Have`` whose op FAILED yet
        still exposes its name, model.py ``Have._fixed_facts_after_me``), so seeding from
        the cache would leave such names un-baselined and falsely report them as "new" on
        the first resume. Reading the live context here is also driver- and
        cache-freshness-independent. No-op for non-workers."""
        if self.is_worker:
            target = self.role.target  # type: ignore[attr-defined]  — is_worker ⟹ role is Role_Worker
            self.reported_scope_facts = {
                n.ascii: raw.ascii
                for n, raw in target._ctxt_before_me().hyps.items()}

    def consume_new_scope_facts_notice(
            self,
            banner: str = "New facts have arrived and are now available "
                          "in your scope") -> str:
        """Render a notice listing the in-scope-before-target facts added — or amended
        under the same name — since the last report, and mark them reported. Returns ""
        if there are none / this is not a worker. Idempotent: an UNCHANGED fact is
        surfaced exactly once across repeated calls; a fact re-amended to a new
        proposition is surfaced again (the worker always gets the latest statement).
        ``banner`` is the heading (the ``request`` resume path overrides it to flag that
        an accepted general lemma / constraint may have been revised by the dispatcher).

        The worker's OWN subtree edits live AFTER the before-target context, so they are
        never in ``_ctxt_before_me().hyps`` and can never be falsely reported here."""
        if not self.is_worker:
            return ""
        target = self.role.target  # type: ignore[attr-defined]  — is_worker ⟹ role is Role_Worker
        new: 'list[tuple[varname, term]]' = []
        for name, raw in target._ctxt_before_me().hyps.items():
            # Change-detection keys on the LIVE-hyps raw ascii (independent of
            # `_worker_premise_cache` freshness): report a fact whose proposition is
            # new, or has CHANGED under the same name since last shown (an amended
            # global lemma / a recycled name) — so the worker always gets the LATEST
            # statement. A reformat-only re-amend re-notifies on purpose.
            key = raw.ascii
            if self.reported_scope_facts.get(name.ascii) == key:
                continue
            # Upgrade to the standard-printed proposition when prefetched (mirror the
            # merge in print_proof_scope); else fall back to the raw stored term.
            new.append((name, self._worker_premise_cache.get(name.ascii, raw)))
            self.reported_scope_facts[name.ascii] = key
        if not new:
            return ""
        buf = StringIO()
        print_hyps(new, 0, buf, {}, banner=banner)
        return buf.getvalue()

    async def _render_useful_lemmas(self) -> str:
        """Resolve this worker's ``useful_lemmas`` (theorem names the planner
        suggested at ``subagent`` dispatch) to their statements and render a
        "Useful lemmas:" block for ``initial_prompt``.

        Resolves the names with the lightweight ``retrieve_entities_by_name``
        (the ``IsaMini.retrieve_entity`` ML callback — NOT ``semantic_knn``, whose
        embedding/vector-store machinery is far too heavy for a by-name lookup),
        then reuses the ``query`` tool's entity renderer
        (``retrieval._render_fetched_entities``) so a suggested lemma reads
        exactly as it would in a ``query`` result — statement, ``[manual]`` tag,
        declaring definition. Names that do not resolve are listed bare (the same
        shape ``_format_fetched_entity`` uses for an entity with no expression).
        Returns "" when there are no lemmas or this is not a worker."""
        role = self.role
        if not isinstance(role, Role_Worker) or not role.useful_lemmas:
            return ""
        from .retrieval import _render_fetched_entities, MANUAL_LEMMA_NOTE
        target = role.target
        # Resolve the lemmas in the worker's own proving scope: the state INSIDE
        # the target block (`_state_after_beginning`, StdBlock-only — sees the
        # target's local fixes/assumptions). This is a DIFFERENT state from
        # `_prefetch_worker_premises`, which resolves the *before*-target premises
        # against `target.ml_state`; for global theorem names the two resolve
        # identically. For a non-block target, fall back to `Node.ml_state`.
        ml_state = (target._state_after_beginning()
                    if isinstance(target, StdBlock)
                    else target.ml_state)
        names = list(role.useful_lemmas)
        entities = await ml_state.retrieve_entities_by_name(names)
        found = [e for e in entities if e is not None]
        unfound = [n for n, e in zip(names, entities) if e is None]
        buf = StringIO()
        if found:
            await _render_fetched_entities(self, ml_state, found, buf, indent=1)
        for name in unfound:
            print_indent(1, buf)
            buf.write(f"- {name}\n")
        body = buf.getvalue().rstrip("\n")
        if not body:
            return ""
        # Explain the [manual] tag the same way `query` results do — the renderer
        # above tags theorems with no simp/intro/elim role as [manual]. The note
        # lives only in the `query` path otherwise, so a worker whose suggested
        # lemmas are [manual] would never see why. Gate on `seen_manual_note` so a
        # later `query` in the worker's run doesn't repeat it.
        if not self.seen_manual_note and any(
                e.entity.kind in _THEOREM_KINDS and not getattr(e.entity, 'roles', [])
                for e in found):
            body += "\n\n" + MANUAL_LEMMA_NOTE
            self.seen_manual_note = True
        return "Useful lemmas:\n" + body

    def _emit_pending_hint_notices(self, indent: int, file: MyIO, *, consume: bool) -> None:
        """Surface Agent Hint Registry NOTICEs at RENDER time (REJECT is a
        separate op-failure path). Walks the rendered proof scope, reads each
        node's authoring-op messages (`_hint_notice_state`), and emits one
        `notice:` block listing each distinct, not-yet-shown `Hint_Notice_Msg`.

        Both surfaces filter against `self.shown_hints`, so a name shows at most
        once per session. Only the inline Outline (`quickview_proof_scope`,
        `consume=True`) MARKS names as shown; `proof.yaml` (`print_proof_scope`,
        `consume=False`) does not mark. Since `proof.yaml` renders BEFORE the
        inline Outline in a tool-call turn, a non-consuming `proof.yaml` cannot
        steal the inline one-shot: on the authoring turn the name is unshown so
        both surfaces show it; the inline render then marks it, and neither
        surface repeats it afterwards. (Mirrors the `showed_suffices_notice`
        render-time precedent.)"""
        emitted: list[str] = []
        seen_here: set[str] = set()
        def walk(node: 'Node') -> None:
            st = node._hint_notice_state()
            if st is not None:
                for m in st.messages:
                    if (isinstance(m, Hint_Notice_Msg)
                            and m.name not in seen_here
                            and m.name not in self.shown_hints):
                        seen_here.add(m.name)
                        emitted.append(m.text)
            for m in node._synthetic_hint_notices():
                if (m.name not in seen_here
                        and m.name not in self.shown_hints):
                    seen_here.add(m.name)
                    emitted.append(m.text)
            for c in getattr(node, 'sub_nodes', ()):
                walk(c)
        walk(self.proof_scope_root)
        if not emitted:
            return
        if consume:
            self.shown_hints.update(seen_here)
        print_indent(indent, file)
        file.write("notice:\n")
        for text in emitted:
            t = self._postprocess_outbound_text(text)
            for i, line in enumerate(t.splitlines() or [""]):
                if i == 0:
                    print_indent(indent + 1, file)
                    file.write(f"- {line}\n")
                else:
                    print_indent(indent + 2, file)
                    file.write(f"{line}\n")

    def print_proof_scope(self, indent: int, file: MyIO,
                          update_line: bool = False, show_warnings: bool = False):
        """Print the proof state scoped to this session's responsibility.
        Workers see a unified premises section (in-scope assumptions + declared facts,
        standard-printed via the prefetched cache) + the bare target goal + own steps."""
        if not self.is_worker:
            self.root.print(indent, file, update_line=update_line, show_warnings=show_warnings)
            self._emit_pending_hint_notices(indent, file, consume=False)
            return
        target = self.proof_scope_root
        # A multi-goal target (a SubgoalMaker — currently only a delegatable
        # Define) has N obligation GoalNode children that EACH self-print their
        # own goal + "fill step" footer under `proof:` below. The single
        # synthesized `goal:` line and the block footer are single-goal artifacts
        # (`target.goal()` is only the leading obligation), so suppress them for
        # multi-goal and let the per-child loop carry the scope.
        is_multi = isinstance(target, SubgoalMaker)

        goal = target.goal() if hasattr(target, 'goal') else None  # type: ignore[attr-defined]  — target is role.target (NonLeaf_Node), guarded by hasattr
        before = target._ctxt_at_me()
        gctx = goal.context if goal is not None else Context({}, {}, {})

        # Unify in-scope context (root + enclosing + target-local) into one block.
        # `before` carries everything in scope at the target (original assumptions,
        # Intro/Have/Obtain/Derive/... — Define/SetupRewriting are no-ops, plus
        # the target's own _fixed_*_at_me contributions such as Have/Suffices
        # for_any variables and premises); `gctx` adds the target's own live
        # local context from the Isabelle goal (e.g. GoalNode case vars).
        merged_vars = {**before.vars, **gctx.vars}
        merged_tvars = {**before.tvars, **gctx.tvars}
        merged_hyps: Hyps = {}
        for n, raw in before.hyps.items():
            # Upgrade to the standard-printed proposition when prefetched (e.g. a Have's
            # full `⋀y. y≥0 ⟹ …` rather than its stored bare conclusion); else fall back.
            merged_hyps[n] = self._worker_premise_cache.get(n.ascii, raw)
        for n, t in gctx.hyps.items():
            merged_hyps.setdefault(n, t)

        print_vars(merged_vars.items(), indent, file, {})
        print_type_vars(merged_tvars.items(), indent, file, {})
        print_hyps(merged_hyps.items(), indent, file, {})

        if not is_multi:
            if goal is not None:
                # Suppress the goal's own context (already surfaced above) -> bare conclusion.
                print_goal(goal, indent, True, file, goal.context)
            else:
                print_indent(indent, file)
                file.write("goal: evaluation pending\n")

        target._print_evaluation_status(indent, file)
        if show_warnings:
            target._print_warnings(indent, file, [Warning.Position.HEADER])

        if target.sub_nodes:  # type: ignore[attr-defined]  — target is role.target (NonLeaf_Node)
            print_indent(indent, file)
            file.write("proof:\n")
            for s in target.sub_nodes:  # type: ignore[attr-defined]
                s.print(indent + 1, file, update_line, show_warnings=show_warnings)
        else:
            print_indent(indent, file)
            file.write("proof: empty\n")

        if not is_multi:
            # Multi-goal: each obligation GoalNode self-prints its own footer in the
            # loop above; the block-level footer is a single-goal artifact (and for a
            # SubgoalMaker its pending-goal body is a no-op since `opening()` is False —
            # its only live output would be FOOTER warnings, dropped here by design).
            target._print_footer(indent, file, show_warnings=show_warnings)  # type: ignore[attr-defined]  — target is role.target (NonLeaf_Node)
        self._emit_pending_hint_notices(indent, file, consume=False)

    def quickview_proof_scope(self, indent: int, file: MyIO):
        """Quickview scoped to this session's proof responsibility."""
        # Consuming surface: inline subagent hints emitted during this render mark
        # themselves shown (one-shot), unlike the non-consuming `proof.yaml` render.
        self._consuming_subagent_hints = True
        try:
            if not self.is_worker:
                self.root.quickview(indent, file)
                self._emit_pending_hint_notices(indent, file, consume=True)
                return
            target = self.proof_scope_root
            _quickview_children_compressed(target.sub_nodes, indent, file)  # type: ignore[attr-defined]  — target is role.target (NonLeaf_Node)
            # Multi-goal (SubgoalMaker): each child self-prints its own pending footer;
            # the block-level footer is a single-goal artifact (and a SubgoalMaker no-op).
            if not isinstance(target, SubgoalMaker):
                target._quickview_pending_footer(indent, file)  # type: ignore[attr-defined]
            self._emit_pending_hint_notices(indent, file, consume=True)
        finally:
            self._consuming_subagent_hints = False

    async def request_restart(self):
        """Request a context restart.  Sets ``self.quit_info = Restart()`` to
        break this session's driver loop, then interrupts.  The loop's restart
        branch detects the ``Restart`` variant, clears ``quit_info`` and
        re-enters with the (memoized) ``initial_prompt()``."""
        self._reset_view_state()
        self.quit_info = Restart()
        await self.interrupt()

    async def interrupt(self):
        """Interrupt the agent's processing immediately.  Default no-op — the
        base class has no active agent loop to halt; drivers such as
        ``ClaudeCode`` override this to cancel their in-flight request."""
        pass

    def refresh_YAML(self):
        """Refresh the YAML file with current proof state.  Default no-op — the
        base class (used by the test suite) has no persistent YAML surface;
        drivers such as ``ClaudeCode`` override this to write/push the file."""
        pass

    async def launch_interaction(self, interaction: 'Interaction') -> Any:
        """Run ``interaction`` and return the answer.

        Three paths, tried in order:
        1. ``ImmediateAnswer`` from ``prompt()`` — short-circuit, no LLM.
        2. Non-forking inline (``_inline_interaction``) — if a channel is
           active and the interaction opts in via ``is_non_forking``.
        3. Forking (``_do_fork``) — spawn a sub-agent session.
        """
        buffer = StringIO()
        try:
            await interaction.prompt(0, MyIO(buffer))
        except ImmediateAnswer as e:
            return e.answer
        prompt_text = buffer.getvalue()

        if self._channel is not None and interaction.is_non_forking:
            return await self._inline_interaction(interaction, prompt_text)

        return await self._do_fork(interaction, prompt_text)

    async def _inline_interaction(
            self, interaction: 'Interaction', prompt_text: str) -> Any:
        """Drive a non-forking interaction via the bidirectional channel."""
        channel = self._channel
        assert channel is not None
        self._nf_pending_interaction = interaction
        try:
            answer_tool = self.tool_name(interaction.answer_tool_name)
            if answer_tool not in prompt_text:
                prompt_text += (
                    f"\nAnswer the question above by calling "
                    f"the `{answer_tool}` tool.")

            self.log_interaction("nf_prompt",
                f"[inline] {type(interaction).__name__}:\n{prompt_text}")
            await channel.outbox.put(
                InteractionPrompt(interaction, prompt_text))

            while True:
                payload = await channel.inbox.get()
                try:
                    result = await interaction.answer(payload)
                    self.log_interaction("nf_answered",
                        f"[inline] answered: {IsaTerm.to_unicode(result)}")
                    return result
                except Interaction_BadAnswer as e:
                    self.log_interaction("nf_bad_answer",
                        f"[inline] bad answer: {e}")
                    await channel.outbox.put(InteractionError(str(e)))
                except IsabelleError as e:
                    error_msg = f"Isabelle error: {'; '.join(pretty_unicode(err) for err in e.errors)}"
                    self.log_interaction("nf_isabelle_error",
                        f"[inline] {error_msg}")
                    await channel.outbox.put(InteractionError(error_msg))
                except ContinuingInteraction as exp:
                    if exp.new_interaction is not None:
                        new_it = exp.new_interaction
                        assert new_it.is_non_forking, (
                            f"ContinuingInteraction replacement "
                            f"{type(new_it).__name__} must be non-forking")
                        try:
                            text = await new_it._render_prompt()
                        except ImmediateAnswer as ia:
                            self.log_interaction("nf_immediate",
                                f"[inline] replacement resolved: {IsaTerm.to_unicode(ia.answer)}")
                            return ia.answer
                        interaction = new_it
                        self._nf_pending_interaction = new_it
                        self.log_interaction("nf_continuing",
                            f"[inline] replaced: {type(new_it).__name__}")
                        await channel.outbox.put(
                            InteractionPrompt(new_it, text))
                    else:
                        assert exp.new_prompt is not None
                        self.log_interaction("nf_continuing",
                            f"[inline] re-prompt")
                        await channel.outbox.put(
                            InteractionPrompt(interaction, exp.new_prompt))
        finally:
            self._nf_pending_interaction = None

    async def _do_fork(self, interaction: 'Interaction',
                       prompt_text: str) -> Any:
        """Spawn a forked sub-agent session. Drivers override this."""
        raise NotImplementedError(
            "`_do_fork` must be implemented by driver subclass")

    def on_log(self, event_type: str, data: dict[str, Any]):
        """Called on every _log invocation. Override to push logs externally."""
        pass

    def on_operation_start(self, step_id: str, operation: str, args: Any):
        """Called before a Minilang operation executes."""
        pass

    def on_operation_end(self, step_id: str, operation: str, args: Any, status: 'EvaluationStatus'):
        """Called after a Minilang operation completes (success or failure)."""
        self.total_isabelle_time += status.time


class SessionConstructor(Protocol):
    def __call__(self, logger: logging.Logger | None, log_dir: str | Path, *,
                 argument: str | None = ...,
                 retrieval_forking_mode: ForkingMode = ...,
                 interactive_retrieval: InteractiveRetrievalMode = ...,
                 timeout_seconds: float = ...,
                 max_tool_calls: int = ...,
                 max_retries: int = ...) -> Session: ...

def agent_driver(name : str):
    """Register a Session constructor (class or factory function) under ``name``."""
    def decorator[T: Type[Session] | SessionConstructor](constructor: T) -> T:
        Session.Driver[name] = constructor
        if isinstance(constructor, type) and issubclass(constructor, Session):
            constructor._driver_name = name  # type: ignore[attr-defined]
        return constructor  # type: ignore[return-value]  — isinstance-narrowing above makes Pyright lose the T binding at the join
    return decorator


# ===== Worker orchestration =====
# The worker event types and ``WorkerHandle`` form one state machine with the
# ``Interaction_ReviewRefutation`` fork above, so they live in the same module
# (removes the former cross-module circular import).

@dataclass
class WorkerComplaint:
    kind: Literal["refute", "surrender", "resource_exhausted"]
    detail: str


# --- Worker events ---------------------------------------------------------
# A live worker communicates with the planning agent through its
# ``WorkerHandle``'s event queue instead of dying and leaving a ``quit_info``
# behind. This lets the worker block (and later resume) while the planning
# agent reviews a refutation, preserving the worker's conversation context.

@dataclass
class WorkerRefute:
    """Worker claims the goal is unprovable and awaits the planning agent's
    review. ``response_future`` is resolved with ``(accepted, reason)`` by
    ``WorkerHandle.resolve_review``; the worker blocks on it inside the
    ``report`` tool until then."""
    detail: str
    response_future: 'asyncio.Future[tuple[bool, str | None]]'

@dataclass
class WorkerSurrender:
    """Worker gives up (no viable strategy / needs help). Terminal — the
    worker interrupts itself right after emitting this."""
    detail: str

@dataclass
class WorkerRequestConstraints:
    """Worker reports that its sub-goal is missing CONSTRAINTS — conditions it
    genuinely needs but was not given when dispatched (the dispatcher
    under-provisioned the sub-goal). The dispatcher adjudicates each one via a
    non-forking ``Interaction_ReviewConstraint`` resolved IN-LOOP in
    ``run_until_yield`` (like a refute, never a park yield to the outer
    dispatcher), so a headless prover's ``run_until_yield`` still returns only
    terminal outcomes (§B). ``constraints`` is the worker's *loose* wish-list of
    ``{description, proposition}`` items (``RequestConstraint``); the dispatcher
    re-states each precisely. NON-terminal: the worker resumes afterwards (with
    the accepted constraint(s) added as premises of its target, or a rejection).
    ``response_future`` is resolved with a feedback STRING by
    ``WorkerHandle.resolve_resume``; the worker blocks on it inside the
    ``request`` tool until then."""
    detail: str
    constraints: list
    response_future: 'asyncio.Future[str]'

@dataclass
class WorkerDifficulty:
    """Emitted by a system struggle checkpoint when it detects a stuck worker.
    NON-terminal: the worker blocks on ``response_future`` (inside the ``delete``
    tool handler) while the dispatcher decides whether to continue or abandon.
    ``response_future`` is resolved with a feedback STRING by
    ``WorkerHandle.resolve_resume``."""
    detail: str
    response_future: 'asyncio.Future[str]'

@dataclass
class WorkerDone:
    """The worker task finished. ``success`` reflects whether the target goal
    is proved. ``detail`` carries the worker's termination reason (its
    ``quit_info``, e.g. a budget/timeout/retry limit) when it stopped without
    proving. Synthesised by ``WorkerHandle`` when the task completes without a
    pending event."""
    success: bool
    detail: str = ""


@dataclass
class WorkerYield:
    """The outcome of one ``WorkerHandle.run_until_yield`` excursion, consumed by
    the ``subagent`` tool logic. ``kind`` discriminates; the other fields are
    kind-specific. The ``constraint_needs_restructure`` park case means: the
    dispatcher ACCEPTED a constraint the worker reported, but the worker's target
    is NOT amendable (an Obtain/Suffices cannot take an added premise), so the
    accepted condition can only be honoured by REWORKING the proof structure — the
    worker is suspended until the dispatcher does so and resumes it. ``detail``
    carries the accepted constraint(s) for the dispatcher's reference."""
    kind: str  # proved | could_not_prove | surrendered | refute_accepted | constraint_needs_restructure | difficulty
    detail: str = ""
    reason: 'str | None' = None

    # Constructors are UPPER-CASE so they cannot collide with the data fields.
    @classmethod
    def PROVED(cls) -> 'WorkerYield':
        return cls(kind="proved")
    @classmethod
    def COULD_NOT_PROVE(cls, detail: str = "") -> 'WorkerYield':
        return cls(kind="could_not_prove", detail=detail)
    @classmethod
    def SURRENDERED(cls, detail: str) -> 'WorkerYield':
        return cls(kind="surrendered", detail=detail)
    @classmethod
    def REFUTE_ACCEPTED(cls, reason: 'str | None', detail: str) -> 'WorkerYield':
        return cls(kind="refute_accepted", reason=reason, detail=detail)
    @classmethod
    def CONSTRAINT_NEEDS_RESTRUCTURE(cls, detail: str) -> 'WorkerYield':
        # A constraint the dispatcher accepted on a NON-amendable target — the
        # worker is parked until the dispatcher reworks the proof structure.
        return cls(kind="constraint_needs_restructure", detail=detail)
    @classmethod
    def DIFFICULTY(cls, detail: str) -> 'WorkerYield':
        return cls(kind="difficulty", detail=detail)


class WorkerHandle:
    """Owns a running worker sub-session and mediates between it and the single
    main (planner) agent.

    The worker runs as its own asyncio task. Its lifecycle events arrive either
    through ``_event_queue`` (refute / surrender / request-constraints — pushed by
    the worker's tools; difficulty — pushed by the system struggle checkpoint)
    or as task completion
    (mapped to ``WorkerDone``). The handle is attached to its target
    ``NonLeaf_Node`` (``node.worker_handle``) while the worker runs or is parked;
    ``run_until_yield`` drives it until it yields control back to the main agent
    (terminal outcome, a constraint-needs-restructure park, or a difficulty park)."""

    def __init__(self, target: NonLeaf_Node, session: 'LMDriver'):
        self.target = target
        self.session = session
        self._event_queue: 'asyncio.Queue' = asyncio.Queue()
        self._task: 'asyncio.Task | None' = None
        self._sub: 'LMDriver | None' = None
        self._pending_review: 'asyncio.Future[tuple[bool, str | None]] | None' = None
        # Pending resume future for a parked/suspended worker — shared by the
        # constraint adjudication (resumed in-loop, or after a structural-restructure
        # park) and the struggle-checkpoint difficulty park, since a worker is only
        # ever waiting on one of them at a time. Resolved with a feedback STRING — a
        # distinct result type from _pending_review's tuple.
        self._pending_resume: 'asyncio.Future[str] | None' = None
        # Set once the worker's accumulated cost has been rolled into the parent
        # (see _settle_costs) — makes the roll-up exactly-once across the _run
        # finally and the aclose fallback.
        self._costs_accumulated: bool = False

    def start(self, suggestions: str = "",
              useful_lemmas: list[str] | None = None,
              *, headless: bool = False) -> None:
        ctx = contextvars.copy_context()
        loop = asyncio.get_running_loop()
        # `headless` is captured into the coroutine args at task creation —
        # BEFORE any worker code runs — so it threads to the prover's Role_Worker
        # with no race (identical channel to suggestions/useful_lemmas).
        self._task = loop.create_task(
            self._run(suggestions, useful_lemmas or [], headless), context=ctx)

    async def _run(self, suggestions: str, useful_lemmas: list[str],
                   headless: bool = False) -> None:
        _session_var.set(None)  # type: ignore
        session = self.session
        try:
            sub = session.__class__._make_fork(
                session, role=Role_Worker(target=self.target,
                                          suggestions=suggestions,
                                          useful_lemmas=useful_lemmas,
                                          worker_handle=self,
                                          headless=headless))
            sub._fork_name = f"{session._fork_name}.worker_{self.target.id}" # type: ignore
            self._sub = sub
            # The worker does NOT inherit the planner's view-dedup caches: that
            # is enforced at construction in Session.__init__ (gated on
            # Role_Worker), so it starts from scratch in its initial prompt.
            await sub.initialize(session.root)
        except Exception as e:
            session.warn_AoA_opr(f"Worker init failed for {self.target.id}: {e}")
            # Expose the failure rather than swallow it (would otherwise surface
            # as a vague could_not_prove): let it propagate to the fatal handler.
            raise InternalError(
                f"sub-agent on {self.target.id} failed to initialize: {e}") from e

        tag = f"[{sub._fork_name}]" # type: ignore
        session.log_interaction("worker", f"{tag} spawned")
        try:
            await sub.run()
            # Final missing-lemma survey before the worker winds down — runs on
            # every natural exit (proved / surrendered / budget exhausted), not
            # on cancellation. No-op unless AOA_MISSING_LEMMA_SURVEY is set.
            await sub.run_missing_lemma_survey("worker_end")
        except asyncio.CancelledError:
            session.warn_AoA_opr(f"{tag} cancelled")
            raise
        except Exception as e:
            session.warn_AoA_opr(f"{tag} failed: {type(e).__name__}: {e}")
            # A worker crashing internally is a bug — re-raise so it propagates
            # (via _wait_next_event → run_until_yield → the executor's sys.exit)
            # instead of being masked as could_not_prove.
            raise InternalError(
                f"sub-agent on {self.target.id} crashed: {type(e).__name__}: {e}") from e
        finally:
            # Defensive: close any sub-agents this worker left parked under its
            # target. A cooperative worker closes/resumes its own sub-agents before
            # finishing; on an early or abnormal exit they would leak as orphaned
            # live tasks no agent can see (immediate-only rendering). Done BEFORE
            # _settle_costs so a leftover's cost rolls up into this worker first.
            # Iterates target's children (never target itself — this worker's own
            # handle lives there). (Single-layer: no nested sub-agents → a no-op.)
            try:
                for child in self.target.sub_nodes:
                    await child.aclose_all_subagents()
            except Exception as e:
                session.warn_AoA_opr(f"{tag} sub-agent cleanup failed: {e}")
            self._settle_costs()
            try:
                await sub.close()
            except Exception as e:
                session.warn_AoA_opr(f"{tag} close failed: {e}")

    def _settle_costs(self) -> None:
        """Roll the worker sub-session's accumulated cost into the parent
        EXACTLY ONCE. Called both from ``_run``'s finally (normal or cancelled
        exit) and as a fallback from ``aclose``; the ``_costs_accumulated`` flag
        makes the two paths idempotent — never double-counting, never skipping.
        (It cannot recover the final, interrupted turn's tokens — those never
        reached an SDK ``ResultMessage`` — only what the sub already recorded.)"""
        if self._costs_accumulated or self._sub is None:
            return
        try:
            self.session._accumulate_subagent_costs(self._sub)
        finally:
            # Mark settled even if accumulation raised midway: a retry would
            # re-apply the already-added fields and double-count.
            self._costs_accumulated = True

    async def _wait_next_event(self):
        """Return the next worker event. A queued event (refute / surrender /
        request-constraints / difficulty) always wins over task completion: ``put_nowait`` synchronously
        resolves the pending ``queue.get()`` future, and FIFO callback
        ordering guarantees we observe it before the task's completion."""
        assert self._task is not None
        queue_get = asyncio.ensure_future(self._event_queue.get())
        done, _pending = await asyncio.wait(
            {self._task, queue_get},
            return_when=asyncio.FIRST_COMPLETED)
        if queue_get in done:
            return queue_get.result()
        queue_get.cancel()
        exc = self._task.exception()
        if exc is not None:
            raise exc
        # Worker succeeded iff the target's subtree has NO unfinished nodes.
        # `target.status` alone is NOT sufficient: for a NonLeaf_Node it
        # reflects only the node's own declaration/goal, not whether the proof
        # below it is complete — child steps may still be unproved. This is the
        # same criterion the worker's own loop uses to decide it is done
        # (proof_scope_unfinished_nodes → target.unfinished_nodes).
        unfinished: set = set()
        self.target.unfinished_nodes(unfinished)
        # When it stopped without proving, carry the worker's own termination
        # reason (quit_info, e.g. a budget/timeout/retry limit) to the planner.
        detail = ""
        if unfinished and self._sub is not None and self._sub.quit_info is not None:
            q = self._sub.quit_info
            detail = q.detail or q.reason
        return WorkerDone(success=not unfinished, detail=detail)

    async def run_until_yield(self) -> 'WorkerYield':
        """Drive the worker until it yields control back to the main agent.
        Re-entered on resume (after the main agent reworks the proof for a parked
        constraint-needs-restructure worker, or answers a struggle-checkpoint
        difficulty park).

        - ``WorkerRefute`` → reviewed in-loop via a fork
          (``Interaction_ReviewRefutation``). Reject → the worker resumes
          transparently (loop continues, main agent never sees it); accept → the
          worker winds down and we return a ``refute_accepted`` yield.
        - ``WorkerRequestConstraints`` → adjudicated IN-LOOP via a NON-forking
          ``Interaction_ReviewConstraint`` (surfaces to the dispatcher through
          its channel; §B preserved — never a park yield). reject / accept on an
          amendable target (the constraint is added IN-PLACE in ``answer()``) →
          the worker resumes in-loop; accept on a NON-amendable target
          (Obtain/Suffices) → PARK (``constraint_needs_restructure``) for the
          dispatcher to rework the proof structure.
        - ``WorkerDifficulty`` → PARK: keep the handle on the node, store the
          pending resume future, and return the difficulty to the main agent.
        - ``WorkerSurrender`` / ``WorkerDone`` → detach and return the outcome."""
        while True:
            event = await self._wait_next_event()
            match event:
                case WorkerRefute():
                    self._pending_review = event.response_future
                    complaint = WorkerComplaint(kind="refute", detail=event.detail)
                    accepted, reason = await self.session.launch_interaction(
                        Interaction_ReviewRefutation(self.target, complaint, self))
                    if accepted:                  # worker is winding down
                        await self.wait_finish()
                        self._detach()
                        return WorkerYield.REFUTE_ACCEPTED(reason, event.detail)
                    continue                      # rejected → worker resumed in-loop
                case WorkerRequestConstraints():
                    self._pending_resume = event.response_future
                    # Adjudicate the reported constraints IN-LOOP. The interaction
                    # is non-forking, so it surfaces to the dispatcher via the
                    # channel (it is awaited inside the dispatcher's channel-routed
                    # `subagent`/`request` task); an amendable target is mutated
                    # IN-PLACE inside `answer()`. The verdict is (kind, feedback):
                    #   - "reject"            → resume the worker with the rejection
                    #   - "accept_amended"    → resume the worker (target now C ⟹ …)
                    #   - "accept_restructure" → PARK for the dispatcher to rework
                    kind, feedback = await self.session.launch_interaction(
                        Interaction_ReviewConstraint(
                            self.target, event.constraints, self))
                    if kind == "accept_restructure":
                        return WorkerYield.CONSTRAINT_NEEDS_RESTRUCTURE(feedback)  # PARK
                    # reject / accept_amended: resume the worker in-loop, exactly
                    # like a rejected refutation (loop continues; the dispatcher
                    # never sees a yield for this excursion).
                    self.resolve_resume(feedback)
                    continue
                case WorkerDifficulty():
                    self._pending_resume = event.response_future
                    return WorkerYield.DIFFICULTY(event.detail)  # PARK
                case WorkerSurrender():
                    await self.wait_finish()
                    self._detach()
                    return WorkerYield.SURRENDERED(event.detail)
                case WorkerDone(success=True):
                    await self.wait_finish()
                    self._detach()
                    return WorkerYield.PROVED()
                case _:  # WorkerDone(success=False)
                    await self.wait_finish()
                    self._detach()
                    return WorkerYield.COULD_NOT_PROVE(event.detail)

    def _detach(self) -> None:
        """Clear this handle from its node on a terminal outcome, then refresh."""
        if self.target.worker_handle is self:
            self.target.worker_handle = None
        self.session.refresh_YAML()

    def retarget(self, new_node: 'NonLeaf_Node') -> None:
        """Migrate this LIVE handle from its current target to ``new_node`` (the
        same tree slot/id) WITHOUT tearing the worker down — used by non-destructive
        ``amend`` (commit-keep). Updates the three references that anchor the worker:
        the node attr, ``self.target``, and the worker session's ``role.target``
        (everything else derives from ``role.target`` + the live id)."""
        old = self.target
        if old.worker_handle is self:
            old.worker_handle = None
        new_node.worker_handle = self
        self.target = new_node
        if self._sub is not None and isinstance(self._sub.role, Role_Worker):
            self._sub.role.target = new_node
            # The worker's memoized opening prompt bakes the OLD lemma name/english
            # (`initial_prompt` -> `_initial_prompt_cache`). Clear it so an SDK
            # restart/compaction rebuilds the header from the amended target rather
            # than re-seeding the stale goal. (Hygiene for this helper; NOT the
            # deferred active "your goal changed" worker notification.)
            self._sub._initial_prompt_cache = None

    def resolve_review(self, accepted: bool, reason: str | None = None) -> None:
        fut = self._pending_review
        self._pending_review = None
        if fut is not None and not fut.done():
            fut.set_result((accepted, reason))

    def resolve_resume(self, feedback: str) -> None:
        """Wake a worker blocked on a resume future — a `request` constraint
        adjudication (resumed in-loop, or after a structural-park restructure) or
        a struggle-checkpoint difficulty park — handing it the dispatcher's
        feedback string (mirrors ``resolve_review`` but with a plain-string
        result)."""
        fut = self._pending_resume
        self._pending_resume = None
        if fut is not None and not fut.done():
            fut.set_result(feedback)

    async def wait_finish(self) -> None:
        if self._task is not None:
            try:
                await self._task
            except asyncio.CancelledError:
                pass

    def cancel(self) -> None:
        """Best-effort synchronous teardown: unblock a worker waiting on its
        review (so its ``await fut`` raises) and cancel the worker task. Does
        NOT await the task — use ``aclose`` for guaranteed cleanup."""
        for fut in (self._pending_review, self._pending_resume):
            if fut is not None and not fut.done():
                fut.cancel()
        self._pending_review = None
        self._pending_resume = None
        if self._task is not None and not self._task.done():
            self._task.cancel()

    async def aclose(self) -> None:
        """Idempotent teardown that GUARANTEES the worker is gone: cancel it,
        then await the task (swallowing ``CancelledError``). Safe to call when
        the worker already finished. Detaches the handle from its node. Called per
        node by the two recursive teardowns: ``Node.discard`` (node leaves the tree
        — delete, amend) and ``Node.aclose_all_subagents`` (node stays —
        cancel_subagent, a worker's own wind-down, the session-close sweep)."""
        self.cancel()
        await self.wait_finish()
        self._settle_costs()  # fallback: ensure cost is rolled up if _run's
                              # finally somehow didn't (idempotent via the flag)
        if self.target.worker_handle is self:
            self.target.worker_handle = None


class EditVerdict(Enum):
    """Result of ``Session._edit_verdict``: may the session touch this step?"""
    OK = auto()
    OUT_OF_SCOPE = auto()      # a worker editing outside its own subtree
    LOCKED = auto()            # the target is comparable to a live sub-agent's node


def _is_direct_global_decl(n: 'Node') -> bool:
    """True iff ``n`` is a provable declaration (Have/Obtain/SetupRewriting/Define)
    sitting DIRECTLY under ``GlobalEnv`` — i.e. a global lemma header."""
    return (isinstance(n, (Have, Obtain, SetupRewriting, Define))
            and isinstance(n.parent, GlobalEnv))


def _enclosing_global_decl(node: 'Node') -> 'Node | None':
    """The nearest STRICT ancestor of ``node`` that is a direct global decl, or
    None if ``node`` is not inside any global decl's body (walk stops at GlobalEnv)."""
    n = node.parent
    while n is not None:
        if _is_direct_global_decl(n):
            return n
        if isinstance(n, GlobalEnv):
            return None
        n = n.parent
    return None


def _is_strict_ancestor(anc: 'Node', node: 'Node') -> bool:
    """True if ``anc`` is a PROPER ancestor of ``node`` (walks ``.parent``;
    excludes ``node`` itself)."""
    cur = node.parent
    while cur is not None:
        if cur is anc:
            return True
        cur = cur.parent
    return False


def _first_worker_in_subtree(n: 'Node') -> 'WorkerHandle | None':
    """First ``worker_handle`` at ``n`` or anywhere below it (DFS), else None."""
    if isinstance(n, NonLeaf_Node):
        if n.worker_handle is not None:
            return n.worker_handle
        for child in n.sub_nodes:
            h = _first_worker_in_subtree(child)
            if h is not None:
                return h
    return None


def _first_worker_in_ancestors(n: 'Node', stop: 'Node | None' = None) -> 'WorkerHandle | None':
    """First ``worker_handle`` strictly above ``n`` (its ancestors), else None.
    When ``stop`` is given, the walk halts BEFORE it (exclusive) — a handle on
    ``stop`` or above is never returned, so the caller's own scope root and its
    spawner chain are ignored. ``stop=None`` walks to the root (the original
    behaviour). ``n is stop`` has no in-scope ancestor (the walk would start
    above ``stop`` and the guard never fire), so it returns None directly."""
    if n is stop:
        return None
    cur = n.parent
    while cur is not None:
        if cur is stop:
            return None
        if isinstance(cur, NonLeaf_Node) and cur.worker_handle is not None:
            return cur.worker_handle
        cur = cur.parent
    return None
