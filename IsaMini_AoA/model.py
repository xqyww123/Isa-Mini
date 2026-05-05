import asyncio
from time import time
from datetime import datetime
from io import StringIO
from pathlib import Path
from .helper import split_id_into_segs, cat_segs_into_id, incr_id_major, incr_id_minor, MyIO
from .linked_list import Cons, LinkedList, from_iterable, iterate, concat
import types as _types
from typing import Any, Awaitable, ClassVar, Iterable, Mapping, NamedTuple, Protocol, Sequence, TypedDict, Callable, cast, Type, Literal, NotRequired, Annotated, TypeAliasType, Union, get_type_hints, get_origin, get_args, is_typeddict
from Isabelle_RPC_Host import Connection, IsabelleError, pretty_unicode, ascii_of_unicode
from Isabelle_RPC_Host.position import IsabellePosition
from Isabelle_RPC_Host.universal_key import (
    EntityKind, universal_key, universal_key_of, universal_key_and_name_of, UndefinedEntity,
)
from Isabelle_Semantic_Embedding.semantics import Semantic_Vector_Store, SemanticRecord, trunc_expr as _trunc_expr_base

AGENT_EXPR_LIMIT = 200
AGENT_GOAL_CHAR_LIMIT = 400

LONG_GOAL_HINT = (
    "note: resulting goal is unusually long, "
    "which is often a sign of a wrong direction.\n"
)

def trunc_expr(s: 'str | IsaTerm') -> str:
    return _trunc_expr_base(s.unicode if isinstance(s, IsaTerm) else s, AGENT_EXPR_LIMIT)
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum
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
    discharge_premises: NotRequired[list['FactByName | None']]

type Fact = FactByName | FactByProposition | FactByDescription

def fact_kind(fact: Fact) -> Literal["name", "proposition", "description"]:
    if "name" in fact:
        return "name"
    if "proposition" in fact:
        return "proposition"
    return "description"

def _where_suffix(fact: Fact) -> str:
    if "name" not in fact:
        return ""
    insts = cast(FactByName, fact).get("instantiations", [])
    if not insts:
        return ""
    where_parts = " and ".join(
        f"{i['name']} = \N{SINGLE LEFT-POINTING ANGLE QUOTATION MARK}{i['value']}\N{SINGLE RIGHT-POINTING ANGLE QUOTATION MARK}"
        for i in insts)
    return f"[where {where_parts}]"

def _of_suffix(fact: Fact) -> str:
    if "name" not in fact:
        return ""
    discharge = cast(FactByName, fact).get("discharge_premises", [])
    if not discharge:
        return ""
    of_parts = []
    for item in discharge:
        if item is None:
            of_parts.append("_")
        else:
            of_parts.append(item["name"] + _where_suffix(item) + _of_suffix(item))
    return "[OF " + " ".join(of_parts) + "]"

def _fact_suffix(fact: Fact) -> str:
    return _where_suffix(fact) + _of_suffix(fact)

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
    __slots__ = ('fact', 'is_local')
    def __init__(self, full_name: 'full_name', short_name: 'short_name', fact: Fact, expression: list[term],
                 kind: EntityKind = EntityKind.THEOREM, roles: list[str] = [],
                 abbreviation_names: 'list[full_name]' = [],
                 is_local: bool = False):
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
            for expr in self.expression:
                print_indent(indent + 1, file)
                file.write(f"  {expr.unicode}\n")
        else:
            file.write(f"- {display_name}\n")
    def pack(self) -> tuple[int, str]:
        suffix = _fact_suffix(self.fact)
        if suffix:
            suffix = ascii_of_unicode(suffix)
        return (0, self.full_name + suffix)

class IsabelleFact_ProveInTime(IsabelleFact):
    """A fact to be proven just-in-time by Isabelle."""
    __slots__ = ('statement',)
    def __init__(self, statement: term):
        self.statement = statement
    def name(self) -> 'term':
        return self.statement
    def print(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        file.write(f"- {self.statement.unicode}\n")
    def pack(self) -> tuple[int, str]:
        return (1, self.statement.ascii)

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
    hyps: Hyps

    @classmethod
    def unpack(cls, data) -> 'Context':
        (vars, hyps) = data
        vars = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in vars.items()}
        hyps = {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in hyps.items()}
        return cls(vars, hyps)
    def __str__(self) -> str:
        vs = ", ".join(f"{k.unicode}: {v.unicode}" for k, v in self.vars.items())
        hs = ", ".join(f"{k.unicode}: {v.unicode}" for k, v in self.hyps.items())
        return f"{{{vs}}}, {{{hs}}}"

class Goal(NamedTuple):
    context: Context
    conclusion: term

    @classmethod
    def unpack(cls, data) -> 'Goal':
        (context, conclusion) = data
        conclusion = IsaTerm.from_isabelle(conclusion)
        return cls(Context.unpack(context), conclusion)
    def visible(self, suppressed: Context) -> 'Goal':
        """Return a Goal with suppressed vars/hyps removed."""
        return Goal(
            Context(
                {k: v for k, v in self.context.vars.items() if k not in suppressed.vars},
                {k: v for k, v in self.context.hyps.items() if k not in suppressed.hyps}
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

MAX_EXPR_ITEMS = 5

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
    print_hyps(goal.context.hyps.items(), indent, file, suppressed.hyps)
    print_indent(indent, file)

    conclusion_str = goal.conclusion.unicode
    was_truncated = False
    if truncate and len(conclusion_str) > AGENT_GOAL_CHAR_LIMIT:
        conclusion_str = _trunc_expr_base(conclusion_str, AGENT_GOAL_CHAR_LIMIT)
        was_truncated = True

    if any(name not in suppressed.vars for name in goal.context.vars) or\
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
    if replace_existing:
        file.write(f"Error: Unfinished Proof! Call command `edit` with action `fill` and target step `{step}`"
            " to replace it with a proof.\n")
    elif show_goal:
        file.write(f"Error: Unfinished Proof! Call command `edit` with action `fill` and target step `{step}`"
            " to provide the proof for the following goal.\n")
    else:
        file.write(f"Error: Unfinished Proof! Call command `edit` with action `fill` and target step `{step}`"
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


class OprError(AoA_Error):
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
    """Unified failure carrier for fill/insert_before/amend."""
    def __init__(self,
                 target_step: step,
                 operation: 'EditOperation | None' = None,
                 unapplied_oprs: 'list[Parsed_Opr] | None' = None,
                 is_error: bool = True):
        # `operation` is None when raised from a node factory (only site:
        # Obvious → GoalIsNontrivial); the enclosing edit method fills it
        # in at catch time.
        self.target_step = target_step
        self.operation = operation
        self.unapplied_oprs = list(unapplied_oprs) if unapplied_oprs else []
        self.is_error = is_error
    def __str__(self) -> str:
        match self.operation:
            case EditOperation.FILL:
                return (f"Cannot fill a node with id {self.target_step}"
                        if self.target_step else "Cannot fill this step")
            case EditOperation.INSERT:
                return (f"Cannot insert before the node {self.target_step}"
                        if self.target_step else "Cannot insert before this step")
            case EditOperation.AMEND:
                return (f"Cannot amend the node {self.target_step}"
                        if self.target_step else "Cannot amend this step")
            case _:
                raise InternalError(
                    f"CannotEdit.__str__: unknown operation {self.operation!r}")


class CannotEdit_BlockClosed(CannotEdit):
    """A block-closed proof line can take no more appends."""
    def __init__(self, closed_by: 'step | None', *args, **kw):
        super().__init__(*args, **kw)
        self.closed_by = closed_by
    def __str__(self) -> str:
        if self.closed_by is None:
            tail = "The proof block is closed."
        else:
            tail = (f"The proof block is closed. "
                    f"You should edit node {self.closed_by} instead.")
        return f"{super().__str__()}\n{tail}"


class CannotEdit_NodeNotFound(CannotEdit):
    """Locate failed: the target step id does not exist."""
    def __str__(self) -> str:
        return f"{super().__str__()}\nThe node is not found."


class CannotEdit_BadNode(CannotEdit):
    """`fill` target has a SUCCESS step at or below it."""
    def __str__(self) -> str:
        return (f"{super().__str__()}\n"
                f"The target already exists. "
                f"Fill does not overwrite existing successful steps.")


class CannotEdit_Root(CannotEdit):
    """`amend` was called on the root node."""
    def __str__(self) -> str:
        return f"{super().__str__()}\nIt is the root node."


class CannotEdit_EvaluationFailed(CannotEdit):
    """Set by an `_on_edit_failure` hook that terminated the edit."""
    def __init__(self, reason: 'FailureReason', *args, **kw):
        super().__init__(*args, **kw)
        self.reason = reason
    def __str__(self) -> str:
        return f"{super().__str__()}\n{self.reason.reason}"


class GoalIsNontrivial(CannotEdit):
    """Raised by `Obvious.__init__` when the parent goal is non-trivial."""
    _message = ("You cannot claim the goal is obvious again. "
                "You must provide step-by-step proofs.")
    def __init__(self, parent: 'Node', **kw):
        super().__init__(target_step=parent.id, **kw)
        self.parent = parent
    def __str__(self) -> str:
        return f"{super().__str__()}\n{self._message}"


class FactNotFound(OprError):
    pass
class FactNotFound_BySearch(FactNotFound):
    def __init__(self, criterions: list[list['Search_Criterion']]):
        self.criterions = criterions
    def __str__(self) -> str:
        return f"No fact found for the following criteria: {self.criterions}"
class FactNotFound_ByName(FactNotFound):
    def __init__(self, name: str):
        self.name = name
    def __str__(self) -> str:
        return f"No fact found with name {self.name}"

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
        return f"Step with id {self.id} is not found"

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
        return f"Cannot delete {self.id} because the node is not found"
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
        joined = ", ".join(sorted(missing))
        super().__init__(
            arg,
            f"Missing required field(s) for operation {operation}: {joined}",
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

VALIDATORS: dict[type, Callable[[Any, str], Any]] = {}

def validator(typ: type):
    """Decorator to register a custom validator for a type."""
    def decorator(fn: Callable[[Any, str], Any]):
        VALIDATORS[typ] = fn
        return fn
    return decorator

def _is_union_origin(origin) -> bool:
    return origin is Union or origin is _types.UnionType

def validate(typ: type, data: Any, path: str) -> Any:
    """Validate and normalize `data` against `typ`. Returns canonical form."""
    if isinstance(typ, TypeAliasType):
        return validate(typ.__value__, data, path)
    if typ in VALIDATORS:
        return VALIDATORS[typ](data, path)
    if is_typeddict(typ):
        return _validate_typed_dict(typ, data, path)
    origin = get_origin(typ)
    if origin is list:
        return _validate_list(get_args(typ)[0], data, path)
    if _is_union_origin(origin):
        return _validate_union(get_args(typ), data, path)
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

def _validate_list(elem_type: type, data: Any, path: str) -> Any:
    if not isinstance(data, list):
        raise ArgumentError({}, f"{path}: expected an array, got {type(data).__name__}")
    for i, item in enumerate(data):
        data[i] = validate(elem_type, item, f"{path}[{i}]")
    return data

def _validate_union(args: tuple[type, ...], data: Any, path: str) -> Any:
    none_types = [a for a in args if a is type(None)]
    real_types = [a for a in args if a is not type(None)]
    if none_types and data is None:
        return None
    if len(real_types) == 1:
        return validate(real_types[0], data, path)
    for t in real_types:
        if get_origin(t) is Literal:
            if data in get_args(t):
                return data
    non_literal = [t for t in real_types if get_origin(t) is not Literal]
    for t in non_literal:
        try:
            return validate(t, data, path)
        except (ArgumentError, KeyError, TypeError, ValueError):
            pass
    for t in non_literal:
        if t in (str, int, bool, float):
            if isinstance(data, t):
                return data
    return data

## Minilang Runtime
### Evaluation Status

class EvaluationStatus(NamedTuple):
    class Status(Enum):
        SUCCESS = "success"
        CANCELLED = "cancelled"
        FAILURE = "failure"
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
    def __init__(self, case: str, vars: list[Var], hyps: list[Hyp]) -> None:
        self.case = case
        self.vars = vars
        self.hyps = hyps
    @classmethod
    def unpack(cls, data) -> 'Consider_Case_Msg':
        (case, items_data) = data
        context = Context.unpack(items_data)
        vars = list(context.vars.items())
        hyps = list(context.hyps.items())
        return cls(case, vars, hyps)

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
    def SUFFICES(fixes: 'list[tuple[str, str | None]]',
                 assumes: 'list[tuple[str | None, str]]',
                 conclusion: xterm) -> 'Minilang_Operation':
        return Minilang_Operation("SUFFICES", (
            [(n, ascii_of_unicode(t) if t else None) for n, t in fixes],
            [(n, ascii_of_unicode(t)) for n, t in assumes],
            ascii_of_unicode(conclusion)
        ))
    @staticmethod
    def OBTAIN(variables: list[Explicit_Var], constraints: list[tuple[str | None, xterm]]) -> 'Minilang_Operation':
        vars = [(v["name"], ascii_of_unicode(v["type"]) if "type" in v else None) for v in variables]
        return Minilang_Operation("OBTAIN", (vars, [(n, ascii_of_unicode(c)) for n, c in constraints]))
    @staticmethod
    def RULE(rule_ref: 'IsabelleFact | None') -> 'Minilang_Operation':
        return Minilang_Operation("RULE", [rule_ref.pack()] if rule_ref is not None else [])
    @staticmethod
    def HAMMER(fact_refs: 'list[IsabelleFact]', timeout: int = 20) -> 'Minilang_Operation':
        return Minilang_Operation("HAMMER", ([r.pack() for r in fact_refs], timeout))
    @staticmethod
    def CHAINING(name: str | None, fact_refs: 'list[IsabelleFact]') -> 'Minilang_Operation':
        return Minilang_Operation("CHAINING", (name, [r.pack() for r in fact_refs]))
    @staticmethod
    def INTRO(bindings: Bindings | None) -> 'Minilang_Operation':
        if bindings is not None:
            var_bindings = [(vb.internal_varname.ascii, vb.external_varname.ascii, vb.type.ascii)
                           for vb in bindings[0]]
            fact_bindings = [(fb.expr, fb.name.ascii, fb.pretty.ascii)
                            for fb in bindings[1]]
            packed_bindings: Any = (var_bindings, fact_bindings)
        else:
            packed_bindings = None
        return Minilang_Operation("INTRO", (packed_bindings, False))
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
    def BRANCH(cases: list[tuple[str | None, xterm]]) -> 'Minilang_Operation':
        return Minilang_Operation("BRANCH", [(n, ascii_of_unicode(t)) for n, t in cases])
    @staticmethod
    def CASE_SPLIT(target: xterm, vars: list[varname_spec] | None, rule: 'IsaTerm | None') -> 'Minilang_Operation':
        return Minilang_Operation("CASE_SPLIT",
            (ascii_of_unicode(target), _pack_varnames(vars),
             rule.ascii if rule is not None else None))
    @staticmethod
    def INDUCT(target: xterm, vars: list[varname_spec] | None, arbitrary: list[xvarname],
               facts_to_generalize: list[str], rule: 'IsaTerm | None') -> 'Minilang_Operation':
        return Minilang_Operation("INDUCT",
            (ascii_of_unicode(target), _pack_varnames(vars),
             [ascii_of_unicode(t) for t in arbitrary],
             list(facts_to_generalize),
             rule.ascii if rule is not None else None))
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

    async def execute(self, opr: Extended_Minilang_Operation, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        if assign_to is None:
            assign_to = Minilang_State(self.connection, type(self).assign_name())
        if isinstance(opr, Minilang_Operation):
            dest_name = assign_to.name
            session = the_session()
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
        try:
            await self.connection.callback("IsaMini.reset_state", self.name)
        except:
            pass
        self.leading_goal = None
        self.display_goals_count = 0
        self._initialized = False
        self.new_subgoals_count = None
    # def search_fact(self, dnf_criterions: list[list[Search_Criterion]]) -> FactRef:
    #     fact_ref_and_props = self.connection.callback("IsaMini.lookup_fact",
    #                                                    (self.name, dnf_criterions))
    #     match fact_ref_and_props:
    #         case []:
    #             raise FactNotFound(dnf_criterions)
    #         case [single]:
    #             ref, _ = single
    #             return ref
    #         case _:
    #             raise NotImplementedError("Here we should list all the options and ask the LLM to choose which one does it mean")
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
                out[i] = IsabelleFact_ProveInTime(IsaTerm.from_agent(prop))
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
                out[idx] = IsabelleFact_Presented(
                    full_name=query_name, short_name=short_name,
                    fact=original_fact, expression=exprs,
                    kind=kind, roles=roles, is_local=is_local)
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
        """Search k nearest entities by semantic similarity, returning resolved entities.
        If exact_name is given, does an exact lookup (score=1.0), ignoring other criteria.
        If query is None, returns pattern-filtered entities without semantic ranking.
        For TheoremK, extends the domain with local contextual thm keys.
        Pattern/theory filters (empty = no restriction) are forwarded to
        the entity enumeration callbacks for ML-side filtering.
        Returns (results, warnings) where warnings include notices about
        undeclared free variables in term patterns."""
        from Isabelle_Semantic_Embedding.semantics import Semantic_DB

        # Exact name lookup — bypass all search criteria
        if exact_name is not None:
            scored_recs: list[tuple[float, SemanticRecord]] = []
            for tag in kinds:
                try:
                    uk, full_name = await universal_key_and_name_of(self.connection, tag, exact_name, ctxt=self.name)
                except UndefinedEntity:
                    if "." in exact_name:
                        short = exact_name.rsplit(".", 1)[1]
                        try:
                            uk, full_name = await universal_key_and_name_of(self.connection, tag, short, ctxt=self.name)
                        except Exception:
                            continue
                    else:
                        continue
                except IsabelleError:
                    continue
                rec = Semantic_DB[uk]
                if rec is not None:
                    scored_recs.append((1.0, rec))
                else:
                    scored_recs.append((1.0, SemanticRecord(tag, full_name, None, None)))
            if not scored_recs:
                return [], [f'Undefined: "{exact_name}"']
            warnings: list[str] = []
            # Skip to entity resolution below
        else:

            term_patterns = [ascii_of_unicode(p) for p in term_patterns]
            type_patterns = [ascii_of_unicode(p) for p in type_patterns]
            target_type = ascii_of_unicode(target_type)
            # Build domain
            if EntityKind.THEOREM in kinds:
                local_entries: list[tuple] = await self.connection.callback(
                    "IsaMini.contextual_thms", self.name)
                local_keys = [bytes(k_) for k_, _ in local_entries]
                local_names = {bytes(k_): name for k_, name in local_entries}
                domain: Semantic_Vector_Store.Domain = Semantic_Vector_Store.ContextExtended(
                    local_keys, extra_names=local_names)
            else:
                domain = Semantic_Vector_Store.ContextAll
            store: Semantic_Vector_Store = await self.connection.semantic_vector_store()  # type: ignore
            if query is not None:
                raw_results, warnings_raw = await store.lookup(query, k, kinds, domain,
                                       term_patterns=term_patterns,
                                       type_patterns=type_patterns,
                                       theories_include=theories_include,
                                       name_contains=name_contains,
                                       target_type=target_type,
                                       ctxt=self.name)
                warnings = [pretty_unicode(w) for w in warnings_raw]
                scored_recs = [(score, rec) for score, rec in raw_results]
            else:
                # Pattern-only search: get filtered entities, look up records, no ranking
                from Isabelle_RPC_Host.context import entities_of
                entries, warnings_raw = await entities_of(self.connection, kinds,
                                         term_patterns=term_patterns,
                                         type_patterns=type_patterns,
                                         theories_include=theories_include,
                                         name_contains=name_contains,
                                         limit=k,
                                         target_type=target_type,
                                         ctxt=self.name)
                warnings = [pretty_unicode(w) for w in warnings_raw]
                scored_recs = []
                for uk, name, _ in entries:
                    rec = Semantic_DB[uk]
                    if rec is not None:
                        scored_recs.append((0.0, rec))
                    else:
                        scored_recs.append((0.0, SemanticRecord(EntityKind(uk[16]), name, None, None)))
        if not scored_recs:
            return [], warnings
        # Resolve entities via RPC
        entity_keys = [(rec.kind, rec.name) for _, rec in scored_recs]
        infos = await self._retrieve_entity(entity_keys)
        out: list[RetrievedEntity] = []
        for (score, rec), info in zip(scored_recs, infos):
            if info is None:
                sname: 'short_name' = IsaTerm.from_isabelle(rec.name)
                exprs: list[term] = []
                roles: list[str] = []
                abbrev_names: 'list[full_name]' = []
                is_local = False
            else:
                sname, exprs, roles, abbrev_names, is_local = info
            if rec.kind in _THEOREM_KINDS:
                entity: IsabelleEntity = IsabelleFact_Presented(
                    full_name=rec.name, short_name=sname,
                    fact=FactByName(name=sname.ascii),
                    expression=exprs, kind=rec.kind, roles=roles,
                    abbreviation_names=abbrev_names, is_local=is_local)
            else:
                entity = IsabelleEntity(
                    full_name=rec.name, short_name=sname,
                    expression=exprs, kind=rec.kind, roles=roles,
                    abbreviation_names=abbrev_names)
            out.append(RetrievedEntity(
                entity=entity,
                score=score,
                interpretation=' '.join(rec.interpretation.split()) if rec.interpretation else None))
        return out, warnings
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
            if len(e.errors) >= 2 and e.errors[0] == "Unparsed":
                raise InternalError_UnparsedTerm(term_str, e.errors[1])
            else:
                raise

    async def unfold_syntax(self, term_str: str) -> tuple[str, str, str]:
        """Parse term and unfold higher-theory syntax.
        Returns (head_const_name, raw_main_display, normal_display).
        Raises InternalError_UnparsedTerm if parsing fails."""
        try:
            head_name, raw_display, normal_display = await self.connection.callback(
                "IsaMini.unfold_syntax",
                (self.name, ascii_of_unicode(term_str)))
            raw = pretty_unicode(raw_display).replace("??.", "")
            return (head_name, raw, pretty_unicode(normal_display))
        except IsabelleError as e:
            _PREFIX = "Unparsed: "
            if e.errors and e.errors[0].startswith(_PREFIX):
                raise InternalError_UnparsedTerm(term_str, e.errors[0][len(_PREFIX):])
            else:
                raise

    async def schematic_variables_of(self) -> Vars:
        """
        Get all schematic variables from the leading proof goal.
        Returns a dict of {varname: type} where varnames are formatted as ?name.idx.
        """
        try:
            vars_list = await self.connection.callback("IsaMini.schematic_variables_of", self.name)
            return {IsaTerm.from_isabelle(k): IsaTerm.from_isabelle(v) for k, v in vars_list}
        except IsabelleError as e:
            raise

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
                        expression=[IsaTerm.from_isabelle(prop)]) for full_name, sname, prop in result]

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
        return result

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
            return result
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

### Interaction

# Structured answer object carried by every interaction reply. Each
# Interaction subclass's `answer()` method documents which fields it
# consumes and in what priority order; fields not consumed are ignored.
#
# - `indexes`       : selection into a numbered candidate list
# - `name`          : exact name of an accessible fact/entity (strict
#                     lookup — no fallback to prove-in-time)
# - `statement`     : an Isabelle term string (prove-in-time for
#                     rule-retrieval interactions; instantiation value
#                     for single-variable schematic interactions)
# - `instantiations`: (variable-name, term) pairs for multi-variable
#                     schematic instantiation
class Answer(NamedTuple):
    # The list defaults are shared; the codebase treats Answer as read-only
    # (constructed once per reply, never mutated in place).
    indexes: Annotated[list[int], "sorted and all elements are distinct"] = []
    name: str | None = None
    statement: str | None = None
    instantiations: list[tuple[str, str]] = []

    def is_empty(self) -> bool:
        """All four fields empty — conventionally means 'give up / expand'."""
        return (not self.indexes and self.name is None
                and self.statement is None and not self.instantiations)

def normalize_answer(indexes: list[int] | None,
                     name: str | None,
                     statement: str | None,
                     instantiations: list[dict[str, str]] | None) -> Answer:
    """Build a structured Answer from the raw tool-arg fields.

    All four fields are independent — interactions extract what they need
    in their own priority order. Empty / missing inputs become the
    conventional empty values (empty list, None)."""
    idx = sorted(set(indexes)) if indexes else []
    n = name if name else None
    s = statement if statement else None
    insts = [(i["variable"], i["term"]) for i in instantiations] if instantiations else []
    return Answer(indexes=idx, name=n, statement=s, instantiations=insts)


# Small helpers shared by the `Interaction.answer` overrides. They exist so
# each subclass doesn't have to restate "this interaction only accepts
# indexes / only some fields" with slightly different wording, and so the
# "range-check + BadAnswer" pattern around candidate indexing is stated
# once. Forward refs: both raise `Interaction_BadAnswer` defined below —
# called at runtime, so declaration order doesn't matter.

_ANSWER_FIELDS = ("indexes", "name", "statement", "instantiations")

def _reject_fields(answer: 'Answer', *, allow: set[str], hint: str) -> None:
    """Raise `Interaction_BadAnswer` if `answer` carries any field outside
    `allow` (empty-list / None fields count as 'not used'). `hint` is
    appended verbatim — use it to suggest what the interaction does
    expect, e.g. 'Select by `indexes`.'."""
    using: set[str] = set()
    if answer.indexes: using.add("indexes")
    if answer.name is not None: using.add("name")
    if answer.statement is not None: using.add("statement")
    if answer.instantiations: using.add("instantiations")
    extra = using - allow
    if extra:
        raise Interaction_BadAnswer(
            f"This interaction does not accept "
            f"{', '.join(sorted(extra))}. {hint}")

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

# Abstract tool identifiers (driver-agnostic)
type tool = str
TOOL_EDIT:   tool = "edit"
TOOL_DELETE: tool = "delete"
TOOL_ANSWER: tool = "answer"
TOOL_SEARCH: tool = "query"
TOOL_READ:   tool = "read"
ALL_PROOF_TOOLS: tuple[tool, ...] = (TOOL_EDIT, TOOL_DELETE, TOOL_ANSWER, TOOL_SEARCH, TOOL_READ)

class Interaction:
    forking: ForkingMode = ForkingMode.FORKING_WITH_CTXT
    fork_allowed_tools: list[tool] = [TOOL_ANSWER, TOOL_SEARCH]
    async def prompt(self, indent: int, file: MyIO) -> None:
        raise NotImplementedError("`prompt` must be implemented by subclass")
    async def answer(self, answer: Answer) -> Any:
        raise NotImplementedError("`answer` must be implemented by subclass")

class ImmediateAnswer(Exception):
    """Raised by prompt() when the interaction resolves without LLM input."""
    def __init__(self, answer: Any):
        self.answer = answer

class InteractionExpanded(Exception):
    """Raised by answer() when the interaction's candidate list has been expanded
    and the caller should re-prompt the LLM with the new list. The new prompt text
    is carried in ``new_prompt``. The interaction remains active."""
    def __init__(self, new_prompt: str):
        self.new_prompt = new_prompt

class Interaction_BadAnswer(Exception):
    """Raised when an answer to an interaction is invalid. The interaction remains active."""
    pass


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
        return IsabelleFact_Presented(
            full_name=name, short_name=short_name,
            fact=FactByName(name=name),
            expression=exprs, roles=roles, abbreviation_names=abbrev,
            is_local=is_local)
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
            self.fork_allowed_tools = [TOOL_ANSWER]

    async def _render_prompt(self) -> str:
        """Render the prompt into a string. Used after candidate-list expansion
        to build the new prompt text carried by InteractionExpanded."""
        buf = StringIO()
        await self.prompt(0, MyIO(buf))
        return buf.getvalue()

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

    async def answer(self, answer: Answer) -> 'list[IsabelleEntity | IsabelleFact]':
        # Base class: accepts `indexes` only. Subclasses (e.g.
        # Interaction_RetrieveForProof) override to also consume `name` /
        # `statement`.
        _reject_fields(answer, allow={"indexes"},
                       hint="Select candidate(s) by `indexes`.")
        # Empty answer — expand search if possible
        if not answer.indexes:
            if self.k < self.FINAL_K:
                self.k = self.FINAL_K
                self._candidate_facts_cache = None
                await self.candidate_facts()
                raise InteractionExpanded(await self._render_prompt())
            else:
                await self._log_retrieval_training_data([])
                the_session().log_retrieval(self.query, ["none selected"])
                return []
        # Index answer
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
        if self.single_choice:
            file.write(f"\nIf an entry above matches what you need, answer with its index.\n")
        else:
            file.write(f"\nAnswer with the indices of all matching {title}.\n")
        file.write("Otherwise, if none matches but the statement is trivially provable, "
                   "formalize the statement into Isabelle propositions and answer with them as text. "
                   "IMPORTANT: all numeric literals MUST be type-annotated, "
                   "example: `(2::nat)` not `2`.\n")
        if self.k >= self.FINAL_K:
            file.write("If none of the above applies, answer empty to give up "
                       "the search and prove the statement yourself later.\n")
        else:
            file.write("If none of the above applies, answer empty to see more candidates.\n")

    async def answer(self, answer: Answer) -> 'list[IsabelleEntity | IsabelleFact]':
        """Priority order: name > indexes > statement (> empty-expand).

        `name`      → strict lookup of an accessible named fact. BadAnswer
                      if the name doesn't resolve — it does NOT fall through
                      to prove-in-time.
        `indexes`   → select from the candidate list (delegates to super).
        `statement` → prove-in-time: treat as a new proposition to prove
                      inline.
        (all empty) → expand the candidate list, or give up on the second
                      empty answer (delegates to super)."""
        session = the_session()
        # 1. Name lookup (strict — does not fall through)
        if answer.name is not None:
            presented = await _try_resolve_as_named_fact(self.state, answer.name)
            if presented is None:
                raise Interaction_BadAnswer(
                    f"No accessible fact found with name '{answer.name}'.")
            await self._log_retrieval_training_data([])
            session.log_retrieval(self.query, [f"named: {answer.name}"])
            return [presented]
        # 2. Index selection → delegate to super (which also handles empty
        #    → expand/give-up). But first peel off the statement (prove-
        #    in-time) and empty-with-no-expansion-left paths that super
        #    would reject.
        if answer.statement is not None and not answer.indexes:
            await self._log_retrieval_training_data([], prove_in_time=answer.statement)
            session.log_retrieval(self.query, [f"prove-in-time: {answer.statement}"])
            return [IsabelleFact_ProveInTime(IsaTerm.from_agent(answer.statement))]
        if answer.is_empty() and self.k >= self.FINAL_K:
            await self._log_retrieval_training_data([])
            session.log_retrieval(self.query, ["unfound"])
            if self.single_choice:
                return [IsabelleFact_Unfound(
                    FactByDescription(english=self.query))]
            return []
        return await super().answer(answer)


class Interaction_InstantiateSchematics(Interaction):
    """Prompt the LLM to instantiate schematic variables of an induction /
    case-split rule.

    The pre-flight `IsaMini.analyze_induct` / `analyze_case_split` callback
    reports schematic variables appearing in the rule's consume premises.
    Under `consumes_policy = subgoals`, unconsumed premises are surfaced as
    `Prem<i>` subgoals, but only when they contain no schematic variables;
    this interaction closes that gap by asking the agent to make them
    concrete before the rule is applied.

    Consumes the `instantiations` field of `Answer`. Every schematic
    variable listed in `schematic_vars` must appear exactly once in the
    answer."""

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
            "that must be instantiated before the rule can be applied.\n")
        print_indent(indent, file)
        file.write("Consume premises (they become `Prem<i>` subgoals, "
                   "or are discharged by `using` facts):\n")
        for i, prem in enumerate(self.consume_premises):
            print_indent(indent + 1, file)
            file.write(f"{i}. {prem}\n")
        print_indent(indent, file)
        file.write("Schematic variables to instantiate:\n")
        for name, typ in self.schematic_vars:
            print_indent(indent + 1, file)
            file.write(f"- {name} :: {typ}\n")
        print_indent(indent, file)
        file.write("Answer with `instantiations`, a list of "
                   "{variable, term} objects. Each term must be a "
                   "type-correct Isabelle expression.\n")

    async def answer(self, answer: Answer) -> IsaTerm:
        if not answer.instantiations:
            names = ", ".join(n for n, _ in self.schematic_vars)
            raise Interaction_BadAnswer(
                f"This interaction requires `instantiations` for variables: {names}.")
        required = {n for n, _ in self.schematic_vars}
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
            raise Interaction_BadAnswer(
                f"Unknown schematic variable(s): {', '.join(sorted(extra))}. "
                f"Expected one of: {', '.join(sorted(required))}.")
        insts = [(n, by_name[n]) for n, _ in self.schematic_vars]
        err: str | None = await self.state.connection.callback(
            "IsaMini.validate_instantiation",
            (self.state.name, self.rule_name.ascii, insts))
        if err is not None:
            raise Interaction_BadAnswer(
                f"Instantiation rejected by Isabelle:\n{err}")
        where_parts = " and ".join(
            f"{v} = \N{SINGLE LEFT-POINTING ANGLE QUOTATION MARK}{t}\N{SINGLE RIGHT-POINTING ANGLE QUOTATION MARK}"
            for v, t in insts)
        rule_src = f'"{self.rule_name.unicode}"[where {where_parts}]'
        return IsaTerm.from_agent(rule_src)


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
    # No search needed — restrict the fork to the answer tool only.
    fork_allowed_tools = [TOOL_ANSWER]

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
        # Render the case context (vars + hyps + goal). Goal already carries
        # the case's vars/hyps in its context — Isabelle pushes them into
        # the HHF state's items at case entry (see library/proof.ML around
        # line 2390-2412), so no caller-side merging is needed here.
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
        file.write("Answer with its index if so, or with empty `indexes` to "
                   "leave this case without a proof for now.\n")

    async def answer(self, answer: Answer) -> str | None:
        _reject_fields(answer, allow={"indexes"},
                       hint="Select one supplied case_name by `indexes` "
                            "(at most one), or answer with empty `indexes` "
                            "to drop.")
        if not answer.indexes:
            return None
        if len(answer.indexes) > 1:
            raise Interaction_BadAnswer(
                "Select at most one supplied case_name.")
        idx = answer.indexes[0]
        _check_index(idx, len(self.supplied_options))
        return self.supplied_options[idx]


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
            await node._refresh_me_alone(auto_intro=auto_intro)
        else:
            await node._cancel()
            cancelled = True
        if not cancelled:
            await node._refresh_all_after_me()
        self.committed.append(node)
        if cancelled or node.status.status != EvaluationStatus.Status.FAILURE:
            return (EditFailureBehavior.CONTINUE, cancelled)
        behavior, _ = node._on_edit_failure(self)
        if behavior is EditFailureBehavior.TERMINATE_AND_REVERT:
            rp = node._delete_me()
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

class Node(ABC):
    parent: 'NonLeaf_Node | None'
    id: 'step'
    line: int
    _changes_pending_goal = True
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
            self.session = self.parent.session
        else:
            self.id = self.local_step
            self.session = the_session()
        self.status : EvaluationStatus = EVALUATION_NOT_YET
        self.warnings : list[Warning] = []
        self.changed : bool = False
        self._kind : str = "step"
        self._first_time = True
        self._has_considered_auto_intro = False
        self._is_trivial: bool | None = None
        self.age = self.session.age
        self.line = 0
        self._prev_eval_status: tuple[EvaluationStatus.Status, str | None] | None = None

    def _on_upstream_change(self) -> None:
        """Called when a predecessor is amended or inserted, meaning
        the proof state flowing into this node may have changed.
        Override to clear caches that depend on upstream state."""
        self._is_trivial = None

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
        """Return e.g. 'step 1' or 'goal 2.1'."""
        return f"{self._kind} {self.id}"
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
        file.write(f"- {self._kind} id: {self.id}\n")
        return indent + 1
    def print(self, indent: int, file : MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        return self._print_step_id(indent, file, update_line)
    def quickview_title(self) -> str:
        return type(self).__name__
    def _should_print_done(self) -> bool:
        return not self.does_quickview_need_detail()
    def quickview_header(self, indent: int, file: MyIO) -> int:
        print_indent(indent, file)
        changed_mark = "changed, " if self.changed else ""
        done_mark = "done, " if self._should_print_done() else ""
        match self.status.status:
            case EvaluationStatus.Status.FAILURE:
                status_mark = "failed, "
            case EvaluationStatus.Status.CANCELLED:
                status_mark = "pending, "
            case _:
                status_mark = ""
        file.write(f"{self._kind} {self.id}: {self.quickview_title()} ({changed_mark}{status_mark}{done_mark}line {self.line})\n")
        return indent + 1
    def does_quickview_need_detail(self) -> bool:
        return self.changed or self.status.status != EvaluationStatus.Status.SUCCESS
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
                print_paragraph(indent, file, reason.reason)
            case EvaluationStatus.Status.CANCELLED:
                print_indent(indent, file)
                file.write("Error: the evaluation is cancelled due to failures in preceding nodes\n")
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
                    file.write(self.id)
                file.write(f":\n")
                for warning in warnings:
                    if isinstance(warning.printer, str):
                        if '\n' in warning.printer:
                            for i, line in enumerate(warning.printer.splitlines()):
                                if i == 0:
                                    print_indent(indent+1, file)
                                    file.write(f"- ")
                                else:
                                    print_indent(indent+2, file)
                                file.write(f"{line}\n")
                        else:
                            print_indent(indent+1, file)
                            file.write(f"- {warning.printer}\n")
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

    async def _cancel(self) -> None:
        if self.status.status == EvaluationStatus.Status.CANCELLED:
            return
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
        self.age = self.session.age
        self._first_time = False
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
            await self.parent._refresh_all_children_after(self, self.status.status == EvaluationStatus.Status.SUCCESS)
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
            outcome.failure = e
            return outcome
        cascade_from: Node | None = None
        for i, node in enumerate(result.created):
            can_continue = parent._can_continue_before_child(node)
            cancelled = False
            if can_continue:
                await node._refresh_me_alone(auto_intro=True)
            else:
                await node._cancel()
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
            e.unapplied_oprs = list(gns[result.stopped_at:])
            e.is_error = len(outcome.committed) == 0
            outcome.failure = e
        return outcome
    async def insert_before(
        self, step: step, gns: 'list[Parsed_Opr]',
    ) -> 'EditOutcome':
        """Insert `gns` as siblings before `step`, in order.  Returns an
        `EditOutcome` — never raises AoA_Error."""
        op = EditOperation.INSERT
        outcome = EditOutcome(operation=op, request=gns)
        if not gns:
            return outcome
        try:
            node = self.locate_node(step)
        except NodeNotFound:
            outcome.failure = CannotEdit_NodeNotFound(
                target_step=step, operation=op, unapplied_oprs=list(gns), is_error=True)
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
    def unfinished_nodes(self, ret: set['Node']) -> None:
        if self.status.status != EvaluationStatus.Status.SUCCESS:
            ret.add(self)
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
                c.status.status == EvaluationStatus.Status.SUCCESS
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
                rp = child._delete_me()
                while i < len(node.sub_nodes):
                    node._delete_child(node.sub_nodes[i])
                node._is_trivial = None
                break
        if rp is not None:
            await rp._refresh_me_alone(auto_intro=False)
            if rp.parent is not None:
                await rp._refresh_all_after_me()
        return await node.append(gns, op=op)
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
    def _all_fixed_vars_before_me(self, ret: Vars) -> Vars:
        if self.parent is not None:
            self.parent._all_fixed_vars_before_a_child(self, ret)
        return ret
    def _all_fixed_facts_before_me(self, ret: Hyps) -> Hyps:
        if self.parent is not None:
            self.parent._all_fixed_facts_before_a_child(self, ret)
        return ret
    def _ctxt_before_me(self) -> Context:
        vars = self._all_fixed_vars_before_me({})
        hyps = self._all_fixed_facts_before_me({})
        return Context(vars, hyps)
    def _ctxt_at_me(self) -> Context:
        vars = self._all_fixed_vars_before_me({})
        self._fixed_vars_at_me(vars)
        hyps = self._all_fixed_facts_before_me({})
        self._fixed_facts_at_me(hyps)
        return Context(vars, hyps)
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
    def _warn_discarded_nodes(self, discarded_nodes: list['Node'], msg: str, position: Warning.Position) -> None:
        ids = [node.titled_id for node in discarded_nodes]
        def printer(indent: int, file: MyIO) -> int:
            print_indent(indent, file)
            file.write('- ')
            file.write(msg)
            file.write(': ')
            file.write(', '.join(ids))
            file.write('\n')
            return indent
        self.warnings.append(Warning(position, printer))
    def _on_reset(self) -> None:
        self.warnings.clear()
    def reset(self) -> None:
        self._on_reset()
    def reset_changed(self) -> None:
        self.changed = False
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
        self.session.age += 1
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
            if rp.age < self.session.age:
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
                new_node, old = await self.parent._amend_child(self, gns[0])
            except GoalIsNontrivial as e:
                e.operation = op
                e.unapplied_oprs = list(gns)
                e.is_error = True
                outcome.failure = e
                return outcome, self
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
                                await old._cancel()
                            await old._refresh_all_after_me()
                            break
                    outcome.committed.pop()
                    return outcome, old
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
        rp = old_self._delete_me()
        if rp is not None:
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
    def _amend_from(self, old: 'Node') -> None:
        self._first_time = False
    async def amend(self, id: step, gns: 'list[Parsed_Opr]') -> 'EditOutcome':
        """Replace the node at `id` with nodes built from `gns`.  Returns
        an `EditOutcome` — never raises AoA_Error."""
        op = EditOperation.AMEND
        outcome = EditOutcome(operation=op, request=gns)
        if not gns:
            return outcome
        try:
            old_node = self.locate_node(id)
        except NodeNotFound:
            outcome.failure = CannotEdit_NodeNotFound(
                target_step=id, operation=op, unapplied_oprs=list(gns), is_error=True)
            return outcome
        if old_node.parent is not None and isinstance(old_node.parent, NonLeaf_Node):
            the_session().working_block = old_node.parent
        sub_outcome, _ = await old_node.amend_me(gns, op=op)
        return sub_outcome

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
        op = self.the_operation()
        if isinstance(op, FailureReason):
            raise InternalError(f"Cannot assemble a node with failed operation: {op.reason}")
        output.append(op)
        return output
    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        now = time()
        await super()._refresh_me_alone(auto_intro)
        op = self.the_operation()
        if isinstance(op, FailureReason):
            self.status = EvaluationStatus.Failure(time() - now, op)
            return
        try:
            await self.ml_state.execute(op, self.resulting_state())
            self.status = EvaluationStatus.Success(time() - now)
        except IsabelleError as err:
            self.status = EvaluationStatus.Failure(time() - now, FailureReason(''.join(err.errors)))
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

class NonLeaf_Node(Node):
    _closed_by: Node | None # Some proof operation (e.g. Branch) may close a block, preventing all later appending to this block.
    sub_nodes: list['Node']

    class _InsertBatchResult(NamedTuple):
        created: 'list[Node]'
        stopped_at: 'int | None'
        error: 'GoalIsNontrivial | None'

    def __init__(self, config: NodeConfig, thought: str, sub_nodes: list['Node']):
        super().__init__(config, thought)
        self.sub_nodes = sub_nodes
        self._closed_by = None
    def _on_upstream_change(self) -> None:
        super()._on_upstream_change()
        for child in self.sub_nodes:
            child._on_upstream_change()

    def opening(self) -> bool:
        return self._closed_by is None
    def _open(self) -> None:
        self._closed_by = None
    def _close_by(self, child: Node) -> None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                self._closed_by = child
                discarded_nodes = self.sub_nodes[i+1:]
                self.sub_nodes = self.sub_nodes[:i+1]
                if discarded_nodes:
                    self._warn_discarded_nodes(
                        discarded_nodes,
                        f"Due to the change of the proof node {child.id}, the following nodes are truncated",
                        Warning.Position.FOOTER
                    )
                return
        raise InternalError("The target node is not my children")
    async def _refresh_footer(self) -> FailureReason | None:
        return None
    def _can_continue_before_child(self, child: 'Node') -> bool:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i == 0:
                    return True
                return self.sub_nodes[i-1].status.status == EvaluationStatus.Status.SUCCESS
        raise InternalError("The target node is not my children")
    async def _refresh_all_children_after(self, after: 'Node | Literal["end"]', can_continue_i: bool) -> None:
        """
        refreshing the status of all the nodes excluding and after the `after`
        """
        can_continue : bool | None = None
        if after == "end":
            can_continue = True
        else:
            for child in self.sub_nodes:
                if can_continue is None:
                    if child is after:
                        can_continue = can_continue_i
                else:
                    if can_continue:
                        await child._refresh_me_alone(auto_intro=True)
                        can_continue = child.status.status == EvaluationStatus.Status.SUCCESS
                    else:
                        await child._cancel()
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
            child_segs = split_id_into_segs(child.local_step)
            next_segs = split_id_into_segs(self.sub_nodes[next_idx].local_step)
            if len(child_segs) > len(next_segs):
                segs = child_segs[:len(next_segs) + 1]
                segs[-1] += 1
                new_id = cat_segs_into_id(segs)
            else:
                new_id = cat_segs_into_id(child_segs + [1])
        else:
            if not self.opening():
                return
            new_id = self._local_step_of_next_proof_step()
        ml_state = await child.resulting_state().clone(None)
        config = NodeConfig(new_id, ml_state, self)
        intro = Intro(config, "", None)
        self.session.auto_intro_nodes.append(intro)
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
        error: GoalIsNontrivial | None = None
        for k, gn in enumerate(gns):
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
                prev_id = split_id_into_segs(prev_step)
                if len(prev_id) > len(before_segs):
                    segs = prev_id[:len(before_segs) + 1]
                    segs[-1] += 1
                    new_id = cat_segs_into_id(segs)
                else:
                    new_id = cat_segs_into_id(prev_id + [1])
            config = NodeConfig(new_id, await before.ml_state.clone(None), self)
            try:
                node = gn.factory(config)
            except GoalIsNontrivial as e:
                stopped_at = k
                error = e
                break
            created.append(node)
        if created:
            existing_ids = {id(x) for x in self.sub_nodes}
            for node in created:
                if id(node) in existing_ids:
                    raise InternalError("The target node to insert is already in my children")
            self.sub_nodes[insert_idx:insert_idx] = created
            self._is_trivial = None
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
            else:
                c._fixed_vars_after_me(ret)
        raise InternalError("The target node is not my children")
    def _all_fixed_facts_before_a_child(self, child: Node, ret: Hyps) -> Hyps:
        self._all_fixed_facts_before_me(ret)
        self._fixed_facts_at_me(ret)
        for c in self.sub_nodes:
            if c is child:
                return ret
            else:
                c._fixed_facts_after_me(ret)
        raise InternalError("The target node is not my children")
    def unfinished_nodes(self, ret: set['Node']) -> None:
        super().unfinished_nodes(ret)
        for child in self.sub_nodes:
            child.unfinished_nodes(ret)
    def _print_all_warnings(self, file: MyIO) -> None:
        self._print_warnings(0, file, [Warning.Position.HEADER], show_at=True)
        for child in self.sub_nodes:
            child._print_all_warnings(file)
        self._print_warnings(0, file, [Warning.Position.FOOTER], show_at=True)
    def does_quickview_need_detail(self) -> bool:
        return super().does_quickview_need_detail() or \
            any(child.does_quickview_need_detail() for child in self.sub_nodes)
    def quickview(self, indent: int, file: MyIO) -> int:
        if not self.does_quickview_need_detail():
            return self.quickview_header(indent, file)
        indent = super().quickview(indent, file)
        children = self.sub_nodes
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
                    file.write("...\n")
                    children[i - 2].quickview(indent, file)
                    children[i - 1].quickview(indent, file)
                else:
                    for j in range(run_start, i):
                        children[j].quickview(indent, file)
            else:
                child.quickview(indent, file)
                i += 1
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
    def reset_changed(self) -> None:
        super().reset_changed()
        for child in self.sub_nodes:
            child.reset_changed()
    def _delete_child(self, child: Node) -> None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                self.sub_nodes.pop(i)
                if self._closed_by is child:
                    self._closed_by = None
                return
        raise InternalError("The target node is not my children")
    async def _amend_child(self, child: 'Node', gn: Parsed_Opr) -> 'tuple[Node, Node]':
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                config = NodeConfig(child.local_step, await child.ml_state.clone(None), self)
                new_node = gn.factory(config)
                self.sub_nodes[i] = new_node
                self._is_trivial = None
                for sibling in self.sub_nodes[i+1:]:
                    sibling._on_upstream_change()
                new_node._amend_from(child)
                if self._can_continue_before_child(new_node):
                    await new_node._refresh_me_alone(auto_intro=True)
                else:
                    await new_node._cancel()
                await new_node._refresh_all_after_me()
                return new_node, child
        raise InternalError("The target node is not my children")
    def _amend_from(self, old: 'Node') -> None:
        super()._amend_from(old)
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
        parsed = _parse_optional_raw_proof(arg.get("proof"), f"{path}.proof")
        return Parsed_Opr(
            cls=cls,
            factory=lambda cfg: cast(Any, cls)(cfg, arg, parsed),
            raw=arg)
    async def _cancel(self) -> None:
        if self.status.status == EvaluationStatus.Status.CANCELLED:
            return
        await super()._cancel()
        await self._state_before_ending_.reset()
        for child in self.sub_nodes:
            await child._cancel()
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
    def assemble(self, output: list[Minilang_Operation] | None = None) -> list[Minilang_Operation]:
        if output is None:
            output = []
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
            await self.ml_state.execute(opr, self._state_after_beginning())
            return None
        except IsabelleError as err:
            return self._beginning_opr_err_msgs(err)
    async def _refresh_footer(self) -> FailureReason | None:
        ending_opr = self.ending_opr()
        if ending_opr is None:
            await self._state_before_ending_.clone(self.resulting_state())
        else:
            try:
                await self._state_before_ending_.execute(ending_opr, self.resulting_state())
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
                        await child._refresh_me_alone(auto_intro=True)
                        if child.status.status != EvaluationStatus.Status.SUCCESS:
                            can_continue = False
                            failed_child = child
                    else:
                        await child._cancel()
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
        for child in self.sub_nodes:
            if can_continue:
                await child._refresh_me_alone(auto_intro=True)
                can_continue = child.status.status == EvaluationStatus.Status.SUCCESS
                if not can_continue:
                    reason = self._child_refresh_failure_err_msgs(child)
                    failed_child = child
            else:
                await child._cancel()
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
        hyps = self._all_fixed_facts_before_me({})
        self._fixed_vars_at_me(vars)
        self._fixed_facts_at_me(hyps)
        for child in self.sub_nodes:
            child._fixed_vars_after_me(vars)
            child._fixed_facts_after_me(hyps)
        return Context(vars, hyps)
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
    def unfinished_nodes(self, ret: set['Node']) -> None:
        super().unfinished_nodes(ret)
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
            if isinstance(child, Obvious) and child.status.status != EvaluationStatus.Status.SUCCESS:
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
    def does_quickview_need_detail(self) -> bool:
        if super().does_quickview_need_detail():
            return True
        if self.opening():
            if not self._state_before_ending_.initialized() or self.should_I_show_pending_goal() is not None:
                return True
        return False
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.opening():
            if not self._state_before_ending_.initialized():
                print_indent(indent, file)
                file.write("Error: Evaluation pending\n")
                self._prev_pending_goal = None
            elif (goal_and_step := self.should_I_show_pending_goal()) is not None:
                goal, step_to_fill = goal_and_step
                print_indent(indent, file)
                line_hint = f" (line {self.open_pending_proof_line})" if self.open_pending_proof_line is not None else ""
                if self.session.showed_fill_hint:
                    file.write(f"Error: Unfinished Proof{line_hint}. Fill step `{step_to_fill}`\n")
                else:
                    file.write(f"Error: Unfinished Proof{line_hint}. Call command `edit` with action `fill` and target step `{step_to_fill}`\n")
                    self.session.showed_fill_hint = True
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
        return indent
    def print_string(self, indent: int, show_warnings: bool = True) -> str:
        buffer = StringIO()
        self.print(indent, MyIO(buffer), show_warnings=show_warnings)
        return buffer.getvalue()
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
            if (auto_intro
                    and not any(gn.cls is Intro or gn.cls is Induction for gn in gns)
                    and await self._state_after_beginning().need_intro(False)):
                local_step = self._local_step_of_next_proof_step()
                ml_state = await self._state_after_beginning().clone(None)
                config = NodeConfig(local_step, ml_state, self)
                intro = Intro(config, "", None)
                self.sub_nodes.append(intro)
                self.session.auto_intro_nodes.append(intro)
            for gn in gns:
                local_step = self._local_step_of_next_proof_step()
                ml_state = await self._state_after_beginning().clone(None)
                sub_config = NodeConfig(local_step, ml_state, self)
                try:
                    new_child = gn.factory(sub_config)
                except GoalIsNontrivial:
                    return FailureReason(
                        "Nested proof contains Obvious on a goal that is not "
                        "trivially provable")
                self.sub_nodes.append(new_child)
            if inherited:
                last = self.sub_nodes[-1] if self.sub_nodes else None
                if isinstance(last, StdBlock):
                    for child in inherited:
                        child.parent = last
                    last.sub_nodes.extend(inherited)
                else:
                    self._warn_discarded_nodes(
                        inherited,
                        "The last provided proof operation cannot host the "
                        "previously inherited sub-proof steps; these inherited "
                        "steps have been discarded",
                        Warning.Position.FOOTER)
            return None
        if (auto_intro
                and not self.sub_nodes
                and await self._state_after_beginning().need_intro(False)):
            local_step = self._local_step_of_next_proof_step()
            ml_state = await self._state_after_beginning().clone(None)
            config = NodeConfig(local_step, ml_state, self)
            intro = Intro(config, "", None)
            self.sub_nodes.append(intro)
            self.session.auto_intro_nodes.append(intro)
        return None
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
        def _block_closed(unapplied: 'list[Parsed_Opr]') -> CannotEdit_BlockClosed:
            return CannotEdit_BlockClosed(
                self._closed_by.id if self._closed_by is not None else None,
                self.id,
                operation=op, unapplied_oprs=unapplied,
                is_error=len(outcome.committed) == 0)
        if not self.opening():
            outcome.failure = _block_closed(list(gns))
            return outcome
        if not gns:
            return outcome
        for i, gn in enumerate(gns):
            if not self.opening():
                outcome.failure = _block_closed(list(gns[i:]))
                return outcome
            local_step = self._local_step_of_next_proof_step()
            ml_state = await self._state_before_ending_.clone(None)
            config = NodeConfig(local_step, ml_state, self)
            try:
                node = gn.factory(config)
            except GoalIsNontrivial as e:
                e.operation = op
                e.unapplied_oprs = list(gns[i:])
                e.is_error = len(outcome.committed) == 0
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

    def __init__(self, config: NodeConfig, is_single_goal: bool, show_goal: bool,
                 pending_proof: 'proof | None' = None):
        super().__init__(config, "", [])
        self.is_single_goal = is_single_goal
        self.show_goal = show_goal
        self._allow_multi_goal = True
        self._kind = "goal"
        self.case_vars = None
        self.case_hyps = None
        self._prev_quickview_context: tuple[Vars, Hyps] | None = None
        self._prev_quickview_conclusion: term | None = None
        self._pending_proof: 'proof | None' = pending_proof
    @property
    def titled_id(self) -> str:
        return self.id
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
                    goal = Goal(Context(merged_vars, merged_hyps), goal.conclusion)
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
        old_case = (self.case_vars, self.case_hyps)
        consider_case_msgs = [m for m in self.ml_state.messages if isinstance(m, Consider_Case_Msg)]
        match consider_case_msgs:
            case []:
                pass
            case [consider_case_msg]:
                self._reset_local_step(consider_case_msg.case)
                self.case_vars = consider_case_msg.vars
                self.case_hyps = consider_case_msg.hyps
            case _:
                raise InternalError(f"Expected exactly one Consider_Case_Msg in Case's messages, got {len(consider_case_msgs)}")
        if not is_init and (self.case_vars, self.case_hyps) != old_case:
            self.changed = True
        # `_pending_proof` may have been populated by the parent
        # Install `_pending_proof` (set by SubgoalMaker orchestration)
        # as sub_nodes, with auto-Intro injection if needed.
        if self._pending_proof is not None and not self.sub_nodes:
            gns = self._pending_proof
            self._pending_proof = None
            if (not any(gn.cls is Intro or gn.cls is Induction for gn in gns)
                    and await self.ml_state.need_intro(False)):
                local_step = self._local_step_of_next_proof_step()
                ml_state = await self.ml_state.clone(None)
                config = NodeConfig(local_step, ml_state, self)
                intro = Intro(config, "", None)
                self.sub_nodes.append(intro)
                self.session.auto_intro_nodes.append(intro)
            for gn in gns:
                local_step = self._local_step_of_next_proof_step()
                ml_state = await self.ml_state.clone(None)
                sub_config = NodeConfig(local_step, ml_state, self)
                try:
                    self.sub_nodes.append(gn.factory(sub_config))
                except GoalIsNontrivial:
                    break
        elif is_init and not self.sub_nodes and await self.ml_state.need_intro(False):
            local_step = self._local_step_of_next_proof_step()
            ml_state = await self.ml_state.clone(None)
            config = NodeConfig(local_step, ml_state, self)
            intro = Intro(config, "", None)
            self.sub_nodes.append(intro)
            self.session.auto_intro_nodes.append(intro)
        return await super()._refresh_me_alone(auto_intro)
    async def _auto_intro_after_me(self) -> None:
        pass
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        goal = self.goal()
        if goal is not None:
            ret.update(goal.context.vars)
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
                file.write(f"done\n")
            return indent
        else:
            done_mark = "done, " if self._should_print_done() else ""
            print_indent(indent, file)
            file.write(f"- {self.id} ({done_mark}line {self.line})\n")
            child_indent = indent + 1
            if self.show_goal:
                goal = self.goal()
                if goal is not None:
                    suppressed = self._ctxt_before_me()
                    if self.case_vars or self.case_hyps:
                        merged_vars = {v[0]: v[1] for v in (self.case_vars or [])} | goal.context.vars
                        merged_hyps = {h[0]: h[1] for h in (self.case_hyps or [])} | goal.context.hyps
                    else:
                        merged_vars = goal.context.vars
                        merged_hyps = goal.context.hyps
                    visible_vars = {k: v for k, v in merged_vars.items() if k not in suppressed.vars}
                    visible_hyps = {k: v for k, v in merged_hyps.items() if k not in suppressed.hyps}
                    visible = (visible_vars, visible_hyps)
                    if visible != self._prev_quickview_context:
                        print_vars(merged_vars.items(), child_indent, file, suppressed.vars)
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


class SubgoalMaker(GoalContainer, StdBlock):
    def _should_print_done(self) -> bool:
        return bool(self.sub_nodes) and super()._should_print_done()
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._initial_goal_index : int = 1
        self._supplied_proofs: 'dict[str, proof_with_case_vars] | None' = None

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

    def _amend_from(self, old: 'Node') -> None:
        Node._amend_from(self, old)
        if isinstance(old, type(self)) and isinstance(old, NonLeaf_Node):
            if self._supplied_proofs is None:
                self._supplied_proofs = {}
            for gn in old.sub_nodes:
                if isinstance(gn, GoalNode) and gn.sub_nodes:
                    self._supplied_proofs[f"{PREFIX_OLD}{gn.local_step}"] = (
                        None, [self._node_to_parsed_opr(n) for n in gn.sub_nodes])
            if not self._supplied_proofs:
                self._supplied_proofs = None
            old.sub_nodes.clear()
        elif isinstance(old, NonLeaf_Node) and old.sub_nodes:
            self._warn_discarded_nodes(
                list(old.sub_nodes),
                "Amending to a different proof structure; previous child "
                "proofs cannot be carried over and have been dropped",
                Warning.Position.HEADER,
            )
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

    def _truncate_siblings_for_splice(self) -> None:
        parent = self.parent
        if parent is None:
            return
        idx = next(i for i, c in enumerate(parent.sub_nodes) if c is self)
        discarded = parent.sub_nodes[idx + 1:]
        del parent.sub_nodes[idx + 1:]
        if discarded:
            parent._warn_discarded_nodes(
                discarded,
                "Discarded because the operation's body terminates "
                "the proof; no sibling should follow",
                Warning.Position.FOOTER)

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
                new_node = parsed_op.factory(config)
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
                self._truncate_siblings_for_splice()
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
                self._truncate_siblings_for_splice()
                self._cleanup_inherited_proofs()
                return
            entry = self._supplied_proofs.pop(picked, None)
            if entry is not None:
                self._truncate_siblings_for_splice()
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
            # TODO: try to reuse the existing subnodes instead of discarding them.
            if not self._first_time and goals_count == len(self.sub_nodes):
                pass
            else:
                self._on_regenerating_goals(goals_count)
                if (decision == _OpenSubgoalBlock.YES_AND_CLOSE_PARENT_BLOCK
                        and self.parent is not None):
                    self.parent._close_by(self)
                if self.sub_nodes:
                    self._warn_discarded_nodes(
                        list(self.sub_nodes),
                        "Due to changes in this operation's subgoal structure, the following previously held proof steps are discarded",
                        Warning.Position.FOOTER)
                self.sub_nodes = []
                ml_state = await s0.clone(None)
                for i in range(goals_count):
                    new_node = self._new_goal_node(i, ml_state)
                    self.sub_nodes.append(new_node)
                    if i < goals_count - 1:
                        ml_state = await ml_state.sorry_next(None, None)
        else:
            if self.sub_nodes:
                self._warn_discarded_nodes(
                    list(self.sub_nodes),
                    "Since this operation no longer opens a proof block, the following previously held proof steps are discarded",
                    Warning.Position.FOOTER)
                self.sub_nodes = []
            # Re-open the parent iff the parent is currently closed (by any
            # closer) AND we are the tail of its sub_nodes — i.e., whatever
            # closing happened previously is now effectively undone because
            # this refresh doesn't open a block.  (`_close_by` always
            # truncates the parent to end at the closer, so the "I'm the
            # tail" check is how we identify the closer without tracking
            # identity across refresh cycles.)
            if (self.parent is not None
                    and self.parent._closed_by is not None
                    and self.parent.sub_nodes
                    and self.parent.sub_nodes[-1] is self):
                self.parent._open()
        if not is_init and len(self.sub_nodes) != old_n_subnodes:
            self.changed = True
        if self._supplied_proofs:
            await self._orchestrate_proofs()
        return None
    def _id_of_openning_prf_to_fill(self) -> step | None:
        return None
    def opening(self) -> bool:
        return False


class CaseSplit_Like(SubgoalMaker):
    # Subclass-specific "kind" label — overridden on CaseSplit / Induction.
    # Used by `_rematch` when building `Interaction_MapCase`.  Named
    # `_case_kind` (not `_kind`) to avoid shadowing Node's instance-level
    # `_kind` attribute set in Node.__init__.
    _case_kind: ClassVar[Literal["case-split", "induction"]]

    case_vars: list[Var] | None
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
        self.case_hyps = None
        self._resolved_rule_str = None
        self._rule_resolved = False
        # quickview dedup: remember what case_vars / case_hyps we last
        # printed so we don't repeat them on every re-render unless
        # they actually changed (mirrors Intro's `_prev_bindings`).
        self._prev_case_printed: tuple[list[Var] | None, list[Hyp] | None] | None = None

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
        (possibly with a `[where ?v = t]` attribute clause) and cache it
        in `self._resolved_rule_str`.

        Three stages:
          1. Map `rule_spec` → `rule_name: str | None`. `FactByDescription`
             forks an `Interaction_RetrieveForProof` (single_choice).
          2. Call the `IsaMini.analyze_induct` / `analyze_case_split`
             callback to discover any schematic variables appearing in
             the rule's consume premises.
          3. If schematic vars are present, fork an
             `Interaction_InstantiateSchematics` to collect instantiations,
             then assemble `rule_name[where ?v1 = t1, ...]`.

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
            results = await self.session.fork_interaction(retrieve)
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
            analysis = await self.ml_state.connection.callback(
                callback_name, callback_args)
        except IsabelleError as err:
            return FailureReason(
                f"Pre-flight analysis of {kind} rule failed: "
                f"{''.join(err.errors)}")
        # 3. instantiate schematic vars if any
        if analysis is not None:
            picked_name, _, consume_prems, _, schematic_vars = analysis
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
                    await self.session.fork_interaction(instantiate)
                self._rule_resolved = True
                return None
        self._resolved_rule_str = (IsaTerm.from_isabelle(rule_name)
                                   if rule_name is not None else None)
        self._rule_resolved = True
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
            current = (self.case_vars, self.case_hyps)
            if current != self._prev_case_printed:
                if self.case_vars:
                    print_vars(self.case_vars, indent, file, {}, "fixing variables")
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
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        if not self.sub_nodes and self.case_hyps:
            for name, prop in self.case_hyps:
                ret[name] = prop
        return ret
    def _fixed_vars_after_me(self, ret: Vars) -> Vars:
        return self._fixed_vars_at_me(ret)
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return self._fixed_facts_at_me(ret)
    async def _refresh_the_beginning_opr(self) -> 'FailureReason | None':
        is_init = self._first_time
        old_case = (self.case_vars, self.case_hyps)
        fail = await super()._refresh_the_beginning_opr()
        if fail is not None:
            return fail
        if (self.sub_nodes
                and isinstance(self.sub_nodes[0], GoalNode)
                and self.sub_nodes[0].case_vars is not None):
            opr = self.beginning_opr()
            if isinstance(opr, Minilang_Operation):
                try:
                    await self.ml_state.execute(opr, self._state_after_beginning())
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
                    self.case_hyps = m0.hyps
                case _:
                    raise InternalError(
                        f"Expected at most one Consider_Case_Msg in Case's "
                        f"messages, got {len(msgs)}")
        if not is_init and (self.case_vars, self.case_hyps) != old_case:
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
        return await self.session.fork_interaction(interaction)

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

class Obvious_ToolArg(TypedDict):
    facts: list[FactByName | FactByProposition]

@proof_operation("Obvious", Obvious_ToolArg)
class Obvious(Leaf):
    def __init__(self, config: NodeConfig, arg: Obvious_ToolArg):
        if config.parent is not None and config.parent._is_trivial is False:
            raise GoalIsNontrivial(config.parent)
        super().__init__(config, "")
        self._raw_facts: list[FactByName | FactByProposition] = [
            f for f in arg["facts"] if f is not None]
        self.fact_refs: list[IsabelleFact] | None = None

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
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent
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
            elif self.status.status == EvaluationStatus.Status.FAILURE:
                self.parent._is_trivial = False
    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        facts = self.fact_refs if self.fact_refs is not None else []
        return Minilang_Operation.HAMMER(facts, 30)
    def _on_edit_failure(self, outcome: 'EditOutcome') -> 'tuple[EditFailureBehavior, EditOutcome]':
        if self.status.status == EvaluationStatus.Status.FAILURE:
            # Multi-op batches skip auto-revert so the agent sees
            # the failing node and can amend it.
            if len(outcome.request) > 1:
                return super()._on_edit_failure(outcome)
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
        self.chain_name: str | None = arg.get("name")
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

#### Witness

class Witness_ToolArg(TypedDict):
    thought: str
    witness: xterm

@proof_operation("Witness", Witness_ToolArg)
class Witness(Leaf):
    def __init__(self, config: NodeConfig, arg: Witness_ToolArg):
        super().__init__(config, arg["thought"])
        self.witness = arg["witness"]
    def quickview_title(self) -> str:
        return f"Witness {self.witness}"
    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Witness\n")
        print_indent(indent, file)
        file.write(f"witness: {self.witness}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

    def the_operation(self) -> Minilang_Operation:
        return Minilang_Operation.WITNESS([self.witness])


#### Define

class Define_ToolArg(TypedDict):
    thought: str
    name: str
    type: NotRequired[xtyp]
    equations: list[xterm]
    metric: NotRequired[list[xterm]]

@proof_operation("Define", Define_ToolArg)
class Define(SubgoalMaker):
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
        self.type: str | None = arg.get("type")
        self.equations = list(arg["equations"])
        self.metric = list(arg.get("metric", []))
        # Set by _refresh_the_beginning_opr based on reporter messages
        # the ML side emits when FUN pushes a deferred block. Controls
        # whether the block has GoalNode children / ending END.
        self._deferred_block_opened: bool = False

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
    def __init__(self, constants: list[str], candidate_defs: list[IsabelleFact_Presented],
                 state: 'Minilang_State | None' = None):
        """
        Args:
            constants: List of constants being unfolded
            candidate_defs: List of candidate definitions
            state: Optional Minilang_State for name-based fact resolution
        """
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
        file.write(f"Select definition(s) to use in unfolding. Call `{tn(TOOL_ANSWER)}` with `indexes`, or the `name` of a definition, or leave empty to skip.\n")
    async def answer(self, answer: Answer) -> list[IsabelleFact]:
        """Priority: name > indexes. `statement` is rejected (use Have/Obvious
        instead if you want to prove-in-time)."""
        _reject_fields(answer, allow={"indexes", "name"},
                       hint="Select a definition by `indexes` or `name`.")
        if answer.name is not None:
            # Try matching against candidate names first
            for d in self.candidate_defs:
                if d.short_name.unicode == answer.name or d.full_name == answer.name:
                    return [d]
            # Try general RPC lookup
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
                self.fact_refs = await the_session().fork_interaction(
                    Interaction_ChooseDef(self.targets, all_defs, state=self.ml_state))
        elif self.ml_state.initialized():
            self.fact_refs = await self.ml_state.refresh_facts(self.fact_refs)
        await super()._refresh_me_alone(auto_intro)

    def _on_edit_failure(self, outcome: 'EditOutcome') -> 'tuple[EditFailureBehavior, EditOutcome]':
        if self.status.status == EvaluationStatus.Status.FAILURE:
            # Multi-op batches skip auto-revert so the agent sees
            # the failing node and can amend it.
            if len(outcome.request) > 1:
                return super()._on_edit_failure(outcome)
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
    instantiations: NotRequired[list[Instantiation]]          # Variable instantiations (default: [])
    discharging_facts: NotRequired[list[FactByName]]          # Facts to discharge premises (default: [])
    result_name: str                                          # Name to bind the result under

@proof_operation("Derive", Derive_ToolArg)
class Derive(Leaf):
    def __init__(self, config: NodeConfig, arg: Derive_ToolArg):
        super().__init__(config, arg["thought"])
        self.rule: FactByName = arg["rule"]
        self.instantiations: list[Instantiation] = [
            x for x in arg.get("instantiations", []) if x is not None]
        self.discharging_facts: list[FactByName] = [
            f for f in arg.get("discharging_facts", []) if f is not None]
        self.result_name: str = arg["result_name"]
        self.rule_ref: IsabelleFact | None = None
        self.discharge_refs: list[IsabelleFact] | None = None
        self.result_facts: list[tuple[varname, term]] | None = None
        """(fact_name, pretty_expression) pairs for facts derived by SPECIALIZE,
        populated from Specialize_Result_Msg after successful execution."""
        self._prev_result_facts: list[tuple[varname, term]] | None = None

    def quickview_title(self) -> str:
        if self.rule_ref is not None:
            return f"Derive {self.rule_ref.name().unicode}"
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
                file.write("To use this rule safely, select which specific subterm(s) to rewrite:\n")
                for i, (pretty, _raw) in enumerate(matches):
                    print_indent(indent + 1, file)
                    file.write(f"{i}. {pretty}\n")
            else:
                print_indent(indent, file)
                file.write("No matching subterms found in rewrite targets.\n")
            print_indent(indent, file)
            file.write("Answer with the index(es) of the subterm(s) to rewrite, or leave empty to drop this rule.\n")
    async def answer(self, answer: Answer) -> list[tuple[int, list[lambda_term]]]:
        """Returns [(fact_index, [selected_raw_terms])] for each looping rule.
        Empty selection for a rule means drop it. Accepts `indexes` only."""
        _reject_fields(answer, allow={"indexes"},
                       hint="Select subterm(s) by `indexes`.")
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

Rewrite_ToolArg = TypedDict('Rewrite_ToolArg', {
    'thought': str,
    'using': list[FactByName | FactByProposition],
    'use system simplifiers': bool,
    'rewrite goal': bool,
    'rewrite premises': list[str]
})

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
        self.fact_targets: list[list[lambda_term] | None] | None = None
        self.bindings: Bindings | None = None
        self.running_time = 0
        self._prev_bindings: Bindings | None = None
        self._prev_result_goal: Goal | None | str = None
        """Tracks the post-rewrite goal for quickview change detection.
        None = not yet shown, 'solved' = goal was solved, Goal = goal changed to."""
    def quickview_title(self) -> str:
        targets: list[str] = []
        if self.rewrite_goal:
            targets.append("goal")
        targets.extend(self.rewrite_premises)
        return f"Rewrite {', '.join(targets)}"
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
            # Send full fact references (including [where ...] attributes) so
            # the ML side resolves the same instantiated theorems that SIMPLIFY uses.
            fact_names = [f.pack()[1] for f in self.using
                          if isinstance(f, IsabelleFact_Presented)]
            if fact_names:
                looping_info = await self.ml_state.check_looping_rules(
                    fact_names, self.rewrite_goal, self.rewrite_premises)
                if looping_info:
                    selections: list[tuple[int, list[lambda_term]]] = \
                        await the_session().fork_interaction(
                            Interaction_SelectRewriteTargets(looping_info, fact_names))
                    fact_targets: list[list[lambda_term] | None] = [None] * len(self.using)
                    for fact_idx, selected_terms in selections:
                        if fact_idx < len(fact_targets):
                            fact_targets[fact_idx] = selected_terms
                    self.fact_targets = fact_targets
        elif self.ml_state.initialized():
            self.using = await self.ml_state.refresh_facts(self.using)
        old_bindings = self.bindings
        old_goal = (self.resulting_state().leading_goal
                    if self.status.status == EvaluationStatus.Status.SUCCESS
                    else None)
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

        if not is_init:
            if self.bindings != old_bindings:
                self.changed = True
            if self.status.status == EvaluationStatus.Status.SUCCESS and old_goal is not None:
                new_goal = self.resulting_state().leading_goal
                if new_goal != old_goal:
                    self.changed = True

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
    _changes_pending_goal = False
    def __init__(self, config: NodeConfig, arg : Have_ToolArg,
                 parsed_proof: 'proof | None' = None):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
        self.name = arg["name"]
        self.auto_apply = arg.get("auto_apply", False)
        self._input_for_any: list[Explicit_Var] = self.statement.get("for_any", [])
        self._input_premises: list[PremiseBinding] = self.statement.get("premises", [])
        # Merged for_any: user-specified + any additional implicit fixes from ML
        self.for_any: list[tuple[varname, typ]] = []
        self._prev_for_any: list[tuple[varname, typ]] = []
        # Pre-parsed subproof body (list[Parsed_Opr]); consumed by
        # _attach_proof on first refresh.
        self._proof: 'proof | None' = parsed_proof
    def quickview_title(self) -> str:
        return f"Have {self.name}"
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
            file.write(f"the statement is quantified over {names_str}\n")
            self._prev_for_any = self.for_any
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
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        ret[IsaTerm.from_agent(self.name)] = IsaTerm.from_agent(self.statement['conclusion'])
        return ret

#### Suffices

class Suffices_ToolArg(TypedDict):
    thought: str
    statement: Statement
    proof: NotRequired[raw_proof | None]

@proof_operation("Suffices", Suffices_ToolArg)
class Suffices(StdBlock):
    def __init__(self, config: NodeConfig, arg : Suffices_ToolArg,
                 parsed_proof: 'proof | None' = None):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
        self._input_for_any: list[Explicit_Var] = self.statement.get("for_any", [])
        self._input_premises: list[PremiseBinding] = self.statement.get("premises", [])
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
        if not self.sub_nodes and not self.session.showed_suffices_notice:
            print_indent(indent, file)
            file.write("notice: Need to show the provided statement implies the goal\n")
            self.session.showed_suffices_notice = True
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

#### Obtain

class Obtain_ToolArg(TypedDict):
    thought: str
    variables: list[Explicit_Var]
    constraints: list[ConstraintBinding]
    proof: NotRequired[raw_proof | None]

@proof_operation("Obtain", Obtain_ToolArg)
class Obtain(StdBlock):
    _changes_pending_goal = False
    def __init__(self, config: NodeConfig, arg : Obtain_ToolArg,
                 parsed_proof: 'proof | None' = None):
        super().__init__(config, arg["thought"], [])
        self.variables = arg["variables"]
        self.constraints = arg["constraints"]
        self._proof: 'proof | None' = parsed_proof
        # Populated from `New_Item_Msg` after OBTAIN runs: the vars +
        # facts Isabelle actually fixed, with types inferred by the ML
        # side. Used by `_fixed_*_after_me` so subsequent siblings see
        # them and the parent's pending-goal suppression can hide them
        # rather than re-listing under the pending goal. Preferred over
        # walking `self.variables` / `self.constraints` because (a) the
        # agent may omit an explicit `type:` and ML inference fills it
        # in, and (b) IsaTerm conversion is already done here.
        self._introduced: Context = Context({}, {})
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
                 _pending_bindings: tuple[list, list] | None = None):
        super().__init__(config, thought)
        self.bindings = bindings
        self.running_time = 0
        self._pending_bindings = _pending_bindings
        self._prev_bindings: Bindings | None = None
    @classmethod
    def gen_single(cls, arg: Intro_ToolArg,
                   path: str = "<direct>") -> Parsed_Opr:
        var_bindings = arg.get("variable_bindings", [])
        fact_bindings = arg.get("fact_bindings", [])
        pending = (var_bindings, fact_bindings) if var_bindings or fact_bindings else None
        thought = arg["thought"]
        factory = lambda cfg: Intro(cfg, thought, None, _pending_bindings=pending)
        return Parsed_Opr(cls=cls, factory=factory, raw=arg)

    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.bindings is not None and self.bindings != self._prev_bindings:
            print_var_bindings(self.bindings[0], indent, file, "fixing variables")
            print_fact_bindings(self.bindings[1], indent, file, "assuming premises")
            self._prev_bindings = self.bindings
        return indent
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
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent
    def the_operation(self) -> Minilang_Operation:
        return Minilang_Operation.INTRO(self.bindings)
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
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            self.running_time += 1
            messages = self.resulting_state().messages
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
        for c in self.sub_nodes:
            if c is child:
                return ret
            elif isinstance(c, GoalNode):
                for gc in c.sub_nodes:
                    gc._fixed_facts_after_me(ret)
            else:
                c._fixed_facts_after_me(ret)
        raise InternalError("The target node is not my children")
    def _all_fixed_vars_before_a_child(self, child: Node, ret: Vars) -> Vars:
        self._all_fixed_vars_before_me(ret)
        self._fixed_vars_at_me(ret)
        for c in self.sub_nodes:
            if c is child:
                return ret
            elif isinstance(c, GoalNode):
                for gc in c.sub_nodes:
                    gc._fixed_vars_after_me(ret)
            else:
                c._fixed_vars_after_me(ret)
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
                selected = await the_session().fork_interaction(result)
                self.rule_ref = selected[0]
        elif self.rule_ref is not None and self.ml_state.initialized():
            [self.rule_ref] = await self.ml_state.refresh_facts([self.rule_ref])
        await super()._refresh_me_alone(auto_intro)
    def quickview_title(self) -> str:
        if self.rule_ref is not None:
            return f"Inference Rule {self.rule_ref.name().unicode}"
        return "Inference Rule"
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
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
        return Minilang_Operation.RULE(self.rule_ref)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to apply the inference rule.{"".join(["\n"+e for e in err.errors])}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("An InferenceRule doesn't have an ending operation")
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, indent-1)
        else:
            return ("derived subgoals", indent+1)

### Contradiction

class Contradiction_ToolArg(TypedDict):
    hypothesis_name: str

@proof_operation("Contradiction", Contradiction_ToolArg)
class Contradiction(Leaf):
    def __init__(self, config: NodeConfig, arg: Contradiction_ToolArg):
        super().__init__(config, "")
        self.hypothesis_name: str = arg["hypothesis_name"]
        self.bindings: Bindings | None = None

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        return Minilang_Operation.CONTRADICTION(self.hypothesis_name)

    async def _refresh_me_alone(self, auto_intro: bool) -> None:
        await super()._refresh_me_alone(auto_intro)
        if self.status.status == EvaluationStatus.Status.SUCCESS:
            intro_msgs = [m for m in self.resulting_state().messages
                          if isinstance(m, Intro_Bindings_Msg)]
            if intro_msgs:
                self.bindings = intro_msgs[0].final

    def quickview_title(self) -> str:
        return f"Contradiction (hypothesis: {self.hypothesis_name})"

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
            cases[ci] = case = validate(Branch_Case_ToolArg, case, case_path)
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
            self._resolved_rule_str)
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
    facts_to_generalize: NotRequired[list[FactByName]]
    proofs: NotRequired[list[Proof_PerCase] | None]

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
            f for f in (arg.get("facts_to_generalize") or []) if f is not None]
        self.fact_refs_to_generalize: list[IsabelleFact_Presented] = []
        self._supplied_proofs = proofs_by_case
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
            arbitrary = [v["name"] for v in self.variables if v["status"] == "generalized"]
            fail = await self._resolve_rule(
                self.rule_spec, self.target_isabelle_term, arbitrary, "induction")
            if fail is not None:
                return fail
        await self._resolve_facts_to_generalize()
        fail = await super()._refresh_the_beginning_opr()
        if fail is None:
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
                            f"Fact `{display}` in `facts_to_generalize` does not mention any "
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
            new_var_names = [v for v in vars if v not in var_names_as_isa]
            if new_var_names:
                if is_init:
                    return FailureReason(
                        f"The {titled_string_of_and_list(new_var_names, 'variable', 'variables')} "
                        f"appear in the induction context but are not classified in the 'variables' argument. "
                        f"You should indicate whether each is 'arbitrary' (generalized during induction) or "
                        f"'fixed' (held constant).")
                else:
                    msg = (
                        f"The {titled_string_of_and_list(new_var_names, 'variable', 'variables')} are not classified "
                        "as fixed or generalized; fixed is assumed. "
                        f"Change this by calling the `edit` tool with action `amend` and target step `{self.id}`"
                    )
                    self.warnings.append(Warning(Warning.Position.HEADER, msg))
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
                    f"Fact `{f.name().unicode}` in `facts_to_generalize` was not found; skipped."))
            elif isinstance(f, IsabelleFact_Presented):
                if not f.is_local:
                    self.warnings.append(Warning(
                        Warning.Position.HEADER,
                        f"Fact `{f.short_name.unicode}` in `facts_to_generalize` is a global "
                        f"theorem; only local proof-context facts can be carried through "
                        f"induction — skipped."))
                else:
                    self.fact_refs_to_generalize.append(f)
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
            file.write(f"facts to generalize: {string_of_and_list([r.short_name.unicode for r in self.fact_refs_to_generalize])}\n")
        super()._print_header(indent, file)
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.INDUCT(
            self.target_isabelle_term,
            cast(list[varname_spec] | None, self._case_vars_of_child(0)),
            [var["name"] for var in self.variables if var["status"] == "generalized"],
            [r.full_name for r in self.fact_refs_to_generalize],
            self._resolved_rule_str)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Induction failed because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Branch doesn't have an ending operation")

### Top Root

class GlobalEnv(StdBlock):
    _body_affects_siblings = True
    def __init__(self, config: NodeConfig):
        if not isinstance(config.parent, Root):
            raise InternalError("The parent of a GlobalEnv must be a Root")
        super().__init__(config, "", [])
        self.id = "global"
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
        # Aggregate vars introduced by children (e.g. a global Obtain), so
        # that sibling GoalNodes see them in their Python-side context.
        for child in self.sub_nodes:
            child._fixed_vars_after_me(ret)
        return ret
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        # Aggregate facts established by children (e.g. global Have's) so that
        # sibling GoalNodes see them in their Python-side context. Without
        # this, Root's _all_fixed_facts_before_a_child(GoalNode, ...) walk
        # would call the default no-op on GlobalEnv and drop every global
        # declaration on the floor, even though the underlying Isabelle state
        # does carry them.
        for child in self.sub_nodes:
            child._fixed_facts_after_me(ret)
        return ret
    def _print_footer(self, indent: int, file: MyIO, show_warnings: bool = False) -> None:
        print_indent(indent, file)
        file.write(f"You can write global declarations by calling command `edit` with action `fill` and target step `{self.id}.{len(self.sub_nodes)+1}`\n")
    def unfinished_nodes(self, ret: set['Node']) -> None:
        for child in self.sub_nodes:
            child.unfinished_nodes(ret)

class Root(GoalContainer, StdBlock):
    def __init__(self, context_and_flat_goal: tuple[Context, tuple['Goal | None', int]],
                 connection: Connection, session: 'Session'):
        (context, (leading_goal, goals_count)) = context_and_flat_goal
        ml_state0 = Minilang_State(connection, '$init')
        ml_state0.leading_goal = leading_goal
        ml_state0.display_goals_count = goals_count
        ml_state0._initialized = True
        super().__init__(NodeConfig("$root", ml_state0, None), "", [])
        self.context = context
        self.session = session
        self.global_env = GlobalEnv(NodeConfig("global", Minilang_State.assign(ml_state0), self))
        self.sub_nodes.append(self.global_env)
        self.final_ml_state = Minilang_State.assign(ml_state0)
        self._closed_by = self
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
                raise InternalError(f"Bad id, {id}")
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
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        ret.update(self.context.hyps)
        return ret
    
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        raise InternalError("Depreciated")

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
    Branch-case.  `None` stays `None`; a list is recursively parsed into
    a flat `list[Parsed_Opr]`."""
    if raw is None:
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
        if not isinstance(body, list):
            raise ArgumentError({},
                f"{body_path}: expected an array of proof operations, "
                f"got {type(body).__name__}")
        out.append(Parse_Op_List(body, body_path))
    return out


## Session

import contextvars

_session_var: contextvars.ContextVar['Session'] = contextvars.ContextVar('_session_var')

def the_session() -> 'Session':
    return _session_var.get()

def tn(t: tool) -> str:
    """Resolve abstract tool id to driver-specific name via the current session."""
    return the_session().tool_name(t)


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

# abstract base class for a session
class Session:
    root: Root
    age: int
    logger: logging.Logger | None
    log_dir: Path | None
    interaction_log_path: Path | None
    proofs_log_path: Path | None
    proof_oprs_log_path: Path | None
    interaction_log_file: Any | None  # File handle for interaction.yaml
    proofs_log_file: Any | None       # File handle for proofs.yaml
    proof_oprs_log_file: Any | None   # File handle for proof_oprs.yaml

    # class variables
    Driver: dict[str, 'SessionConstructor'] = {}

    def __init__(self, logger: logging.Logger | None = None, log_dir: str | Path = "",
                 parent: 'Session | None' = None,
                 retrieval_forking_mode: ForkingMode = ForkingMode.FORKING_WITH_CTXT,
                 interactive_retrieval: InteractiveRetrievalMode = InteractiveRetrievalMode.YES):
        """
        Args:
            logger: Python logger for runtime debug messages to the server log stream.
            log_dir: Directory for persistent session logs (interaction.yaml, proofs.yaml,
                proof_oprs.yaml). Empty string disables file logging.
            parent: Parent session for subsessions. None means this is a major session.
            retrieval_forking_mode: Forking strategy for interactive retrieval.
            interactive_retrieval: Whether to use fork-based interactive retrieval.
        """
        self.parent = parent
        _session_var.set(self)
        self.age = 0
        self.last_proof_op_time: float = time()
        self.logger = logger or (parent.logger if parent else None)
        # On a fork, the interaction it is answering (plus its eventual
        # result). None on the main session; also None on forks before
        # assignment and after cleanup.
        self.fork_pending: 'Fork_Pending | None' = None
        self.working_block: 'NonLeaf_Node | None' = None
        self.warnings: list[str] = []
        self.auto_intro_nodes: list['Intro'] = []
        self.total_cost_usd: float = 0.0
        self.total_input_tokens: int = 0
        self.total_output_tokens: int = 0
        self.total_cache_creation_input_tokens: int = 0
        self.total_cache_read_input_tokens: int = 0
        self.total_tool_calls: int = 0
        self.total_isabelle_time: float = 0.0
        self.total_model_time: float = 0.0
        self.retrieval_forking_mode: ForkingMode = (
            parent.retrieval_forking_mode if parent is not None
            else retrieval_forking_mode)
        self.interactive_retrieval: InteractiveRetrievalMode = (
            parent.interactive_retrieval if parent is not None
            else interactive_retrieval)
        self.seen_entities: 'set[short_name]' = (
            set(parent.seen_entities) if parent is not None else set())
        self.seen_commands: dict[IsabellePosition, str] = (
            dict(parent.seen_commands) if parent is not None else {})
        self.seen_opaque_note: bool = (
            parent.seen_opaque_note if parent is not None else False)
        self.showed_suffices_notice: bool = False
        self.seen_abbreviations: set[str] = (
            set(parent.seen_abbreviations) if parent is not None else set())
        self.showed_fill_hint: bool = False
        if parent is not None:
            # Subsessions share parent's log files
            self.log_dir = parent.log_dir
            self.interaction_log_path = parent.interaction_log_path
            self.proofs_log_path = parent.proofs_log_path
            self.proof_oprs_log_path = parent.proof_oprs_log_path
            self.retrieval_log_path = parent.retrieval_log_path
            self.interaction_log_file = parent.interaction_log_file
            self.proofs_log_file = parent.proofs_log_file
            self.proof_oprs_log_file = parent.proof_oprs_log_file
            self.retrieval_log_file = parent.retrieval_log_file
        else:
            self.log_dir = None
            self.interaction_log_path = None
            self.proofs_log_path = None
            self.proof_oprs_log_path = None
            self.retrieval_log_path = None
            self.interaction_log_file = None
            self.proofs_log_file = None
            self.proof_oprs_log_file = None
            self.retrieval_log_file = None
            if log_dir != "":
                self._setup_log_directory(log_dir)

    @property
    def is_major(self) -> bool:
        return self.parent is None

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

        # Open log files in append mode, keep them open
        self.interaction_log_file = open(self.interaction_log_path, 'a', encoding='utf-8')
        self.proofs_log_file = open(self.proofs_log_path, 'a', encoding='utf-8')
        self.proof_oprs_log_file = open(self.proof_oprs_log_path, 'a', encoding='utf-8')
        self.retrieval_log_file = open(self.retrieval_log_path, 'a', encoding='utf-8')

        # Write initial session start markers
        session_start = {
            "event": "SESSION_START",
            "timestamp": datetime.now().isoformat(),
        }
        self._append_yaml(self.interaction_log_file, session_start)
        self._append_yaml(self.proofs_log_file, session_start)
        self._append_yaml(self.proof_oprs_log_file, session_start)
        self._append_yaml(self.retrieval_log_file, session_start)

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

    async def __aenter__(self) -> 'Session':
        """Enter the runtime context for this session."""
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Exit the runtime context and clean up the session."""
        await self.close()
        return False

    def system_prompt(self) -> str | None:
        """Return the system prompt, or None if the driver folds it into the initial message."""
        return (
            "You are a formal theorem proving agent.\n"
            "A proof goal and an incomplete proof are provided in `./proof.yaml` under the current directory.\n"
            "Analyze the proof goal, plan a proof, and complete it using the MCP proof tools.\n"
            "Continue until no errors remain.\n"
            "Be concise in text output.\n"
            "\n"
            "## Tools\n"
            f"- {self.tool_name(TOOL_EDIT)}: Fill, insert, or amend proof steps (your primary tool)\n"
            f"- {self.tool_name(TOOL_DELETE)}: Delete proof steps\n"
            f"- {self.tool_name(TOOL_SEARCH)}: Search for theorems, constants, types, and rules; help you understand unfamiliar terms\n"
            f"- {self.tool_name(TOOL_READ)}: Read `proof.yaml`. Use only when necessary.\n"
        )

    def initial_prompt(self) -> str:
        """Return the initial user message to start the proof session."""
        buf = StringIO()
        self.root.print(0, MyIO(buf), update_line=True, show_warnings=True)
        proof_state = buf.getvalue()
        if self.system_prompt() is not None:
            return (
                "Complete the following proof using the MCP proof tools.\n"
                + proof_state
                + "\n`proof.yaml` contains the full proof state, but read it only when you lose track of it."
            )
        else:
            return (
                "An incomplete proof is provided as follows\n"
                + proof_state
                + f"Analyze the proof goal, plan a proof, and complete it using tools `{self.tool_name(TOOL_EDIT)}` and `{self.tool_name(TOOL_DELETE)}`.\n"
                "Continue building the proof until no error remains.\n"
                "`proof.yaml` contains the full proof state, but read it only when you lose track of it."
            )

    def retry_prompt(self, unfinished_nodes: set['Node']) -> str:
        """Return the retry message when proof steps remain incomplete."""
        return (
            f"Steps {', '.join([node.id for node in unfinished_nodes])} are incomplete. "
            f"You must call the `{self.tool_name(TOOL_EDIT)}` tool to complete the steps. "
            "Continue building the proof until `proof.yaml` contains no remaining errors."
        )

    def tool_name(self, t: tool) -> str:
        """Translate abstract tool id to the name the LLM sees.
        Base implementation returns identity; drivers override."""
        return t

    def is_proof_tool(self, external_name: str) -> bool:
        """Check whether an external tool name corresponds to a proof tool."""
        return any(self.tool_name(t) == external_name for t in ALL_PROOF_TOOLS)

    async def close(self):
        """Clean up the session and release resources.
        Subsessions do not close shared log files — only major sessions do."""
        if not self.is_major:
            return
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

        # Clean up the context session reference
        try:
            if _session_var.get() is self:
                _session_var.set(None)  # type: ignore
        except LookupError:
            pass

    async def initialize(self, root: Root):
        if hasattr(self, 'root'):
            raise InternalError("The session is already initialized.")
        self.root = root
        self.working_block = root
        await root._refresh_me_alone(auto_intro=True)

    def retrieval_state(self) -> Minilang_State:
        if self.working_block is not None:
            return self.working_block.latest_refreshed_state()
        return self.root.ml_state

    def _log(self, log_file_handle: Any, event_type: str, debug_messages: Callable[[], list[str]] | None, **data):
        """
        Internal method to log events to YAML and debug logger.

        Args:
            log_file_handle: Open file handle for the log file
            event_type: Type of event (e.g., "MODEL_OUTPUT", "PROOF_OPERATION")
            debug_messages: Callable that returns list of debug messages (only called if logger is not None)
            **data: Additional data fields for the YAML log entry
        """
        if log_file_handle is not None:
            log_entry = {
                "event": event_type,
                "timestamp": datetime.now().isoformat(),
                **data
            }
            self._append_yaml(log_file_handle, log_entry)
        if self.logger is not None and debug_messages is not None:
            for msg in debug_messages():
                self.logger.debug(msg)
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
            self.logger.warning(f"[AOA_WARN] {message}")

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

    def log_retry(self, unfinished_nodes: set[Any], retry_prompt: str):
        """Log retry attempt to interaction.yaml."""
        node_ids = [str(node.id) for node in unfinished_nodes]
        self._log(self.interaction_log_file, "RETRY",
                  lambda: [f"[RETRY] Unfinished nodes: {[node.id for node in unfinished_nodes]}",
                           f"[RETRY] Prompt: {retry_prompt}"],
                  unfinished_nodes=node_ids,
                  retry_prompt=retry_prompt)

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
            f"model_time={self.total_model_time:.2f}s")

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
                    self.logger.debug(f"[PROOF] Written to {proof_yaml_path}")
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

    async def fork_interaction(self, interaction: 'Interaction') -> Any:
        """Run ``interaction`` by spawning a sub-agent and awaiting its answer.

        Short-circuits via ``ImmediateAnswer`` without spawning a subprocess.
        Otherwise spawns a forked session with its own MCP endpoint, queries
        the LLM with the rendered prompt, and drives the answer loop
        (including ``InteractionExpanded`` re-prompts) until the fork
        submits a final answer. Returns the answer produced by
        ``interaction.answer``. Must be implemented by subclass."""
        raise NotImplementedError("`fork_interaction` must be implemented by subclass")

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
                 retrieval_forking_mode: ForkingMode = ...,
                 interactive_retrieval: InteractiveRetrievalMode = ...) -> Session: ...

def agent_driver(name : str):
    """Register a Session constructor (class or factory function) under ``name``."""
    def decorator[T: Type[Session] | SessionConstructor](constructor: T) -> T:
        Session.Driver[name] = constructor
        return constructor
    return decorator


