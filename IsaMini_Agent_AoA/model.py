from time import time
from datetime import datetime
from io import StringIO
from pathlib import Path
from .helper import split_id_into_segs, cat_segs_into_id, incr_id_major, incr_id_minor, MyIO
from typing import Any, Awaitable, Iterable, NamedTuple, Protocol, Sequence, TypedDict, Callable, cast, Type, Literal, NotRequired, Annotated
from Isabelle_RPC_Host import Connection, IsabelleError, pretty_unicode, ascii_of_unicode
from Isabelle_RPC_Host.position import IsabellePosition
from Isabelle_RPC_Host.universal_key import (
    EntityKind, universal_key, universal_key_of, universal_key_and_name_of, UndefinedEntity,
)
from Isabelle_Semantic_Embedding.semantics import Semantic_Vector_Store, SemanticRecord, trunc_expr as _trunc_expr_base

AGENT_EXPR_LIMIT = 200

def trunc_expr(s: str) -> str:
    return _trunc_expr_base(s, AGENT_EXPR_LIMIT)
from abc import ABC, abstractmethod
from enum import Enum
import json
import logging
import os
import sqlite3
import sys
import yaml
import platformdirs
from io import StringIO

type varname = str
type varname_spec = varname | None # underscore '_' is represented as None
type typ = str
type term = str
type lambda_term = Any
type step = str
type local_step = str
type Var = tuple[varname, typ]
type Hyp = tuple[varname, term]
type Vars = dict[varname, typ]
type Hyps = dict[varname, term]
type SubProof = Literal["Given later"] | dict  # Obvious_ToolArg at runtime

def _subproof_is_obvious(sp: SubProof) -> bool:
    return isinstance(sp, dict) and sp.get("operation") == "Obvious"

# SubProof_parsed: the result of parsing a SubProof.
# A sync gen_node that creates the Obvious sub-node (with resolved facts), or None for "Given later".
# Defined as a forward reference since gen_node is declared later.
type SubProof_parsed = 'gen_node | None'

class Explicit_Var(TypedDict):
    name: varname
    type: str | None

class FactByProposition(TypedDict):
    refer_by: Literal["proposition"]
    proposition: str

class FactByDescription(TypedDict):
    refer_by: Literal["description"]
    english: str

class FactByName(TypedDict):
    refer_by: Literal["name"]
    name: str

type Fact = FactByName | FactByProposition | FactByDescription

class FailureReason(NamedTuple):
    """A human-readable failure reason, used in Interaction.answer() returns
    and Leaf.the_operation() returns."""
    reason: str

class EditFailureResponse(NamedTuple):
    is_error: bool
    failure_reason: FailureReason | None
    revert: bool

class IsabelleEntity:
    """A resolved Isabelle entity (constant, type, class, locale, etc.) with display info."""
    __slots__ = ('full_name', 'short_name', 'expression', 'kind', 'roles')
    def __init__(self, full_name: str, short_name: str, expression: list[str],
                 kind: EntityKind, roles: list[str] = []):
        self.full_name = full_name
        self.short_name = short_name
        self.expression = expression
        self.kind = kind
        self.roles = roles

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
    def name(self) -> str: ...
    @abstractmethod
    def print(self, indent: int, file: MyIO) -> None: ...
    @abstractmethod
    def pack(self) -> Any:
        """Pack for RPC. Returns the packed form, or FailureReason on error."""
        ...
    def __repr__(self) -> str:
        return self.name()

class IsabelleFact_Presented(IsabelleFact, IsabelleEntity):
    """A resolved fact with full information from Isabelle. `kind` must be
    theorem-like (see _THEOREM_KINDS)."""
    __slots__ = ('fact',)
    def __init__(self, full_name: str, short_name: str, fact: Fact, expression: list[term],
                 kind: EntityKind = EntityKind.THEOREM, roles: list[str] = []):
        assert kind in _THEOREM_KINDS, \
            f"IsabelleFact_Presented requires a theorem-like kind, got {kind}"
        self.full_name = full_name
        self.short_name = short_name
        self.fact = fact
        self.expression = expression
        self.kind = kind
        self.roles = roles
    def name(self) -> str:
        return self.short_name
    def print(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        if len(self.expression) == 1:
            file.write(f"- {self.short_name}: {self.expression[0]}\n")
        elif len(self.expression) > 1:
            file.write(f"- {self.short_name}:\n")
            for expr in self.expression:
                print_indent(indent + 1, file)
                file.write(f"  {expr}\n")
        else:
            file.write(f"- {self.short_name}\n")
    def pack(self) -> tuple[int, str]:
        return (0, self.full_name)

class IsabelleFact_ProveInTime(IsabelleFact):
    """A fact to be proven just-in-time by Isabelle."""
    __slots__ = ('statement',)
    def __init__(self, statement: str):
        self.statement = statement
    def name(self) -> str:
        return self.statement
    def print(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        file.write(f"- {self.statement}\n")
    def pack(self) -> tuple[int, str]:
        return (1, ascii_of_unicode(self.statement))

class IsabelleFact_Unfound(IsabelleFact):
    """A fact that could not be found in the Isabelle context."""
    __slots__ = ('fact',)
    def __init__(self, fact: Fact):
        self.fact = fact
    def name(self) -> str:
        match self.fact["refer_by"]:
            case "name": return cast(FactByName, self.fact)["name"]
            case "proposition": return cast(FactByProposition, self.fact)["proposition"]
            case "description": return cast(FactByDescription, self.fact)["english"]
    def print(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        file.write(f"- Error: fact \"{self.name()}\" not found\n")
    def pack(self) -> Any:
        raise InternalError(f"Attempting to pack an unfound fact \"{self.name()}\". "
                            "Unfound facts should be filtered out before packing.")


class Context(NamedTuple):
    vars: Vars
    hyps: Hyps

    @classmethod
    def unpack(cls, data) -> 'Context':
        (vars, hyps) = data
        vars = {pretty_unicode(k): pretty_unicode(v) for k, v in vars.items()}
        hyps = {pretty_unicode(k): pretty_unicode(v) for k, v in hyps.items()}
        return cls(vars, hyps)
    def __str__(self) -> str:
        return f"{self.vars}, {self.hyps}"

class Goal(NamedTuple):
    context: Context
    conclusion: term

    @classmethod
    def unpack(cls, data) -> 'Goal':
        (context, conclusion) = data
        conclusion = pretty_unicode(conclusion)
        return cls(Context.unpack(context), conclusion)
    def __str__(self) -> str:
        return f"{self.context} ⊢ {self.conclusion}"
    def __repr__(self) -> str:
        return str(self)

class Goals(NamedTuple):
    context: Context
    goals: list[Goal]

    @classmethod
    def unpack(cls, data) -> 'Goals':
        (context, goals) = data
        return cls(Context.unpack(context), [Goal.unpack(goal) for goal in goals])
    def __str__(self) -> str:
        return f"{self.context} ⊢ {self.goals}"

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
                          expressions: list[str]) -> bool:
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
        file.write(f"- {name}: {type}\n")

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
        file.write(f"- {name}: {term}\n")

def print_goal(goal: Goal, indent: int, show_header: bool, file, suppressed: Context):
    print_vars(goal.context.vars.items(), indent, file, suppressed.vars)
    print_hyps(goal.context.hyps.items(), indent, file, suppressed.hyps)
    print_indent(indent, file)
    if any(name not in suppressed.vars for name in goal.context.vars) or\
        any(name not in suppressed.hyps for name in goal.context.hyps):
        file.write(f"goal: {goal.conclusion}\n")
    else:
        if show_header:
            file.write("goal: ")
        file.write(goal.conclusion)
        file.write("\n")

def print_pending_goal(goal: Goal, step: step, indent: int, file : MyIO, suppressed: Context,
                       show_goal: bool = True) -> int:
    line = file.current_line()
    print_indent(indent, file)
    file.write(f"Error: Unfinished Proof! Call command `edit` with action `fill` and target step `{step}`"
        " to provide the proof for the following goal.\n")
    if show_goal:
        print_indent(indent, file)
        file.write("pending proof goal:\n")
        print_goal(goal, indent+1, False, file, suppressed)
    return line

def string_of_and_list(l: list[Any]) -> str:
    match l:
        case []:
            return ""
        case [a]:
            return str(a)
        case [a, b]:
            return f"{a} and {b}"
        case [*rest, last]:
            return ", ".join(str(x) for x in rest) + f", and {last}"
        case _:
            raise ValueError(f"Impossible")
def titled_string_of_and_list(l: list[Any], singular: str, plural: str) -> str:
    if len(l) == 1:
        return f"{singular} {l[0]}"
    else:
        return f"{plural} {string_of_and_list(l)}"


## Errors
type timedelta = float # in seconds

class AoA_Error(Exception):
    pass


class OprError(AoA_Error):
    pass

class CannotInsert(OprError):
    def __init__(self, insert_into: 'Node', reason : str):
        self.reason = reason
        self.insert_into = insert_into
    def __str__(self) -> str:
        return f"Cannot insert before the node {self.insert_into.id}.\n{self.reason}"
class CannotInsert_NodeNotFound(CannotInsert):
    def __init__(self, id: step):
        self.id = id
    def __str__(self) -> str:
        return f"Cannot insert before the node {self.id} because it is not found"

class CannotAppend(OprError):
    def __init__(self, target : 'Node', reason : str):
        self.reason = reason
        self.target = target
    def __str__(self) -> str:
        return f"Cannot append on node {self.target.id}.\n{self.reason}"
class CannotAppend_BlockClosed(CannotAppend):
    def __init__(self, target : 'Node', closed_by: 'Node | None'):
        if closed_by is None:
            msg = f"The proof block is closed."
        else:
            msg = f"The proof block is closed. You should append to node {closed_by.id} instead."
        super().__init__(target, msg)

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

class GenNode_Error(InternalError):
    """
    Raised during gen_node construction when node cannot be created.
    Should be caught by append/insert methods and converted to Cannot* errors.
    """
    def __init__(self, reason: str):
        self.reason = reason
    def __str__(self) -> str:
        return self.reason

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

class CannotFill(OprError):
    pass
class CannotFill_NodeNotFound(CannotFill):
    def __init__(self, id: step):
        self.id = id
    def __str__(self) -> str:
        return f"Cannot fill a node with id {self.id}"
class CannotFill_BadNode(CannotFill):
    def __init__(self, id: step):
        self.id = id
    def __str__(self) -> str:
        return f"Cannot fill a node with id {self.id}"
class CannotRename(OprError):
    pass
class CannotRename_NotFound(CannotRename):
    def __init__(self, old_name: str, new_name: str):
        self.old_name = old_name
        self.new_name = new_name
class CannotRename_VariableNotFound(CannotRename_NotFound):
    def __str__(self) -> str:
        return f"Cannot rename. The variable {self.old_name} is not found"
class CannotRename_FactNotFound(CannotRename_NotFound):
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

class CannotAmend(OprError):
    pass
class CannotAmend_NodeNotFound(CannotAmend):
    def __init__(self, id: step):
        self.id = id
    def __str__(self) -> str:
        return f"Cannot amend the node {self.id} because the node is not found"
class CannotAmend_Root(CannotAmend):
    def __str__(self) -> str:
        return f"Cannot amend the root node"

class GoalIsNontrivial(AoA_Error):
    """Raised when Obvious is attempted on a goal that previously failed Obvious."""
    _message = ("You cannot claim the goal is obvious again. "
                "You must provide step-by-step proofs.")
    def __init__(self, parent: 'Node'):
        self.parent = parent
    def __str__(self) -> str:
        return self._message

class CannotAppend_GoalIsNontrivial(CannotAppend, GoalIsNontrivial):
    def __init__(self, parent: 'Node'):
        CannotAppend.__init__(self, parent, GoalIsNontrivial._message)
        GoalIsNontrivial.__init__(self, parent)

class CannotFill_GoalIsNontrivial(CannotFill, GoalIsNontrivial):
    def __init__(self, parent: 'Node'):
        GoalIsNontrivial.__init__(self, parent)
    def __str__(self) -> str:
        return GoalIsNontrivial._message

class CannotInsert_GoalIsNontrivial(CannotInsert, GoalIsNontrivial):
    def __init__(self, parent: 'Node'):
        CannotInsert.__init__(self, parent, GoalIsNontrivial._message)
        GoalIsNontrivial.__init__(self, parent)

class CannotAmend_GoalIsNontrivial(CannotAmend, GoalIsNontrivial):
    def __init__(self, parent: 'Node'):
        GoalIsNontrivial.__init__(self, parent)
    def __str__(self) -> str:
        return GoalIsNontrivial._message

class NoAliveState(AoA_Error):
    """Raised when interactive_gen needs a live proof state for retrieval/interaction
    but none is available (e.g., operating on a cancelled node)."""
    _message = ("No alive proof state is available for interactive operations. "
                "The target proof context may have been cancelled or not yet evaluated.")
    def __str__(self) -> str:
        return self._message

class CannotAppend_NoAliveState(CannotAppend, NoAliveState):
    def __init__(self, target: 'Node'):
        CannotAppend.__init__(self, target,
            "Cannot fill this step because the proof context here was not successfully evaluated, "
            "due to a failure in a preceding proof step.")

class CannotInsert_NoAliveState(CannotInsert, NoAliveState):
    def __init__(self, target: 'Node'):
        CannotInsert.__init__(self, target,
            "Cannot insert before this step because the proof context here was not successfully evaluated, "
            "due to a failure in a preceding proof step.")

class CannotAmend_NoAliveState(CannotAmend, NoAliveState):
    def __init__(self, target: 'Node', child: 'Node'):
        CannotAmend.__init__(self, target, child,
            "Cannot amend this step because the proof context here was not successfully evaluated, "
            "due to a failure in a preceding proof step.")

type ToolCall_arg = dict[str, Any]
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

def _check_tool_arg_keys(toolarg_typed_dict: type, data: ToolCall_arg, operation: str) -> None:
    """
    Ensure that `data` contains all required keys defined by the TypedDict `toolarg_typed_dict`.
    Raises ArgumentError if any required key is missing.
    """
    required_keys = getattr(
        toolarg_typed_dict,
        "__required_keys__",
        set(getattr(toolarg_typed_dict, "__annotations__", {}).keys()),
    )
    missing = [k for k in required_keys if k not in data]
    if missing:
        raise ArgumentError_MissingRequiredKeys(data, operation, missing)

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
    name: str          # external_name
    pretty: str        # pretty

type Bindings = tuple[list[VariableBinding], list[FactBinding]]

def print_var_bindings(var_bindings: list[VariableBinding], indent: int, file: MyIO, banner='variables'):
    if var_bindings:
        print_indent(indent, file)
        file.write(banner)
        file.write(":\n")
        for vb in var_bindings:
            print_indent(indent + 1, file)
            if vb.external_varname == vb.internal_varname:
                file.write(f"- {vb.external_varname}: {vb.type}\n")
            else:
                file.write(f"- {vb.external_varname}: {vb.type}    (renamed from \"{vb.internal_varname}\")\n")

def print_fact_bindings(fact_bindings: list[FactBinding], indent: int, file: MyIO, banner='facts'):
    if fact_bindings:
        print_indent(indent, file)
        file.write(banner)
        file.write(":\n")
        for fb in fact_bindings:
            print_indent(indent + 1, file)
            file.write(f"- {fb.name}: {fb.pretty}\n")

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
    def __init__(self, goals: list[str]) -> None:
        super().__init__()
        self.goals = goals  # List of pretty-printed goal strings (empty list if no goals)
    @classmethod
    def unpack(cls, data) -> 'Goals_Msg':
        # data is List String - empty list means no goals
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
                internal_varname=v[0],
                external_varname=v[1],
                type=pretty_unicode(v[2])
            ) for v in var_names
        ]
        fact_bindings = [
            FactBinding(
                expr=p[0],
                name=p[1],
                pretty=pretty_unicode(p[2])
            ) for p in prem_names
        ]
        return (var_bindings, fact_bindings)

class Simplify_Fallback_Nosys_Msg(Message):
    """The simplification timed out with system simplifiers and succeeded without them."""
    pass

class Specialize_Result_Msg(Message):
    """Result facts produced by SPECIALIZE.
    Each entry is a (fact_name, pretty_printed_proposition) pair."""
    def __init__(self, facts: list[tuple[str, str]]) -> None:
        super().__init__()
        self.facts = facts
    @classmethod
    def unpack(cls, data: list) -> 'Specialize_Result_Msg':
        # data is [(fact_name, pretty_expression), ...]
        return cls([(name, pretty_unicode(expr)) for name, expr in data])

class Newly_Fixed_Vars_Msg(Message):
    """Free variables that the ML side implicitly fixed when setting up a
    sub-proof goal (e.g. `Have "myf n = n + 7"` auto-fixes `n`). Surfaced as
    a `for_any:` block on the corresponding node."""
    def __init__(self, vars: list[tuple[str, str]]) -> None:
        super().__init__()
        self.vars = vars  # [(external_name, type_str), ...]
    @classmethod
    def unpack(cls, data) -> 'Newly_Fixed_Vars_Msg':
        return cls([(name, pretty_unicode(typ)) for (name, typ) in data])

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
        case (5, x):
            return Specialize_Result_Msg.unpack(x)
        case (6, x):
            return Newly_Fixed_Vars_Msg.unpack(x)
        case _:
            raise Exception(f"BUG bad message kind: {data}")

### Minilang Proof Tree

class ML_ProofTree:
    def children(self) -> list['ML_ProofTree']:
        raise NotImplementedError("children must be implemented by subclass")
    def top_goal(self) -> Goal:
        raise NotImplementedError("top_goal must be implemented by subclass")
    def top_goal_or_none(self) -> 'Goal | None':
        """Return the top goal, or None if the proof tree is solved (SOLVED_TREE)."""
        raise NotImplementedError("top_goal_or_none must be implemented by subclass")
    def top_goals(self) -> list[Goal]:
        """
        The goals of the leftest internal node
        """
        raise NotImplementedError("top_goals must be implemented by subclass")

class MLPT_Goal(ML_ProofTree):
    def __init__(self, goal: Goal):
        self.goal = goal
    def children(self) -> list[ML_ProofTree]:
        return []
    def top_goal(self) -> Goal:
        return self.goal
    def top_goal_or_none(self) -> 'Goal | None':
        return self.goal
    def top_goals(self) -> list[Goal]:
        return [self.goal]
    def __str__(self) -> str:
        return str(self.goal)
    def __eq__(self, other) -> bool:
        if not isinstance(other, MLPT_Goal):
            return False
        return self.goal == other.goal

class MLPT_Bundle(ML_ProofTree):
    def __init__(self, context : Context, subs : list[ML_ProofTree]):
        self.context = context
        self.subs = subs
    def children(self) -> list[ML_ProofTree]:
        return self.subs
    def top_goal(self) -> Goal:
        return self.subs[0].top_goal()
    def top_goal_or_none(self) -> 'Goal | None':
        if not self.subs:
            return None  # SOLVED_TREE
        return self.subs[0].top_goal_or_none()
    def top_goals(self) -> list[Goal]:
        if all(isinstance(sub, MLPT_Goal) for sub in self.subs):
            return [cast(MLPT_Goal, sub).goal for sub in self.subs]
        else:
            left = self.subs[0]
            if isinstance(left, MLPT_Goal):
                raise InternalError("The leftest internal's children should all be goals")
            return left.top_goals()
    def __str__(self) -> str:
        return f"({self.context} ⊢ {self.subs})"
    def __eq__(self, other) -> bool:
        if not isinstance(other, MLPT_Bundle):
            return False
        return self.context == other.context and self.subs == other.subs

class MLPT_Block(ML_ProofTree):
    def __init__(self, sub : ML_ProofTree):
        self.sub = sub
    def children(self) -> list[ML_ProofTree]:
        return [self.sub]
    def top_goal(self) -> Goal:
        return self.sub.top_goal()
    def top_goal_or_none(self) -> 'Goal | None':
        return self.sub.top_goal_or_none()
    def top_goals(self) -> list[Goal]:
        return self.sub.top_goals()
    def __str__(self) -> str:
        return f"{{{self.sub}}}"
    def __eq__(self, other) -> bool:
        if not isinstance(other, MLPT_Block):
            return False
        return self.sub == other.sub

def unpack_MLPT(data) -> ML_ProofTree:
    (kind, x) = data
    match kind:
        case 0:
            return MLPT_Goal(Goal.unpack(x))
        case 1:
            return MLPT_Bundle(Context.unpack(x[0]), [unpack_MLPT(sub) for sub in x[1]])
        case 2:
            return MLPT_Block(unpack_MLPT(x))
        case _:
            raise Exception(f"BUG bad MLPT kind: {kind}")

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
        return (self.positive, (5, self.pattern))
class Criterion_XSimp(Search_Criterion):
    def __init__(self, positive: bool, pattern: term, for_any: list[Explicit_Var]):
        super().__init__(positive)
        self.pattern = pattern
        self.for_any = for_any
    def dump(self) -> Any:
        return (self.positive, (5, self.pattern))
        # TODO: implement the for_any
        # return (self.positive, (8, (self.pattern, self.for_any)))
class Criterion_Pattern(Search_Criterion):
    def __init__(self, positive: bool, pattern: term):
        super().__init__(positive)
        self.pattern = pattern
    def dump(self) -> Any:
        return (self.positive, (6, self.pattern))
class Criterion_XPattern(Search_Criterion):
    def __init__(self, positive: bool, pattern: term, for_any: list[Explicit_Var]):
        super().__init__(positive)
        self.pattern = pattern
        self.for_any = for_any
    def dump(self) -> Any:
        return (self.positive, (6, self.pattern))
        # TODO: implement the for_any
        #return (self.positive, (7, (self.pattern, self.for_any)))


### Minilang Runtime

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
    def SORRY(varnames : list[varname_spec] | None) -> 'Minilang_Operation':
        return Minilang_Operation("SORRY", varnames)
    @staticmethod
    def NEXT(varnames : list[varname_spec] | None) -> 'Minilang_Operation':
        return Minilang_Operation("NEXT", ([], varnames))
    @staticmethod
    def END() -> 'Minilang_Operation':
        return Minilang_Operation("END", [])
    @staticmethod
    def HAVE(name: str, statement: term, auto_apply: bool) -> 'Minilang_Operation':
        return Minilang_Operation("HAVE", (name, ascii_of_unicode(statement), auto_apply))
    @staticmethod
    def SUFFICES(statement: term) -> 'Minilang_Operation':
        return Minilang_Operation("SUFFICES", ascii_of_unicode(statement))
    @staticmethod
    def OBTAIN(variables: list[Explicit_Var], constraints: list[tuple[str | None, term]]) -> 'Minilang_Operation':
        vars = [(v["name"], ascii_of_unicode(v["type"]) if "type" in v else None) for v in variables]
        return Minilang_Operation("OBTAIN", (vars, [(n, ascii_of_unicode(c)) for n, c in constraints]))
    @staticmethod
    def RULE(rule_ref: 'IsabelleFact | None') -> 'Minilang_Operation':
        return Minilang_Operation("RULE", [rule_ref.pack()] if rule_ref is not None else [])
    @staticmethod
    def HAMMER(fact_refs: 'list[IsabelleFact]', timeout: int = 20) -> 'Minilang_Operation':
        return Minilang_Operation("HAMMER", ([r.pack() for r in fact_refs], timeout))
    @staticmethod
    def INTRO(bindings: Bindings | None, split: bool) -> 'Minilang_Operation':
        return Minilang_Operation("INTRO", (bindings, split))
    @staticmethod
    def SIMPLIFY(fact_refs: 'list[IsabelleFact]', use_system_simps: bool, premise_names: list[str], simplify_goal: bool, bindings: tuple[list[tuple[str, str, str]], list[tuple[lambda_term, str, str]]] | None) -> 'Minilang_Operation':
        return Minilang_Operation("SIMPLIFY", ([r.pack() for r in fact_refs], use_system_simps, premise_names, simplify_goal, bindings))
    @staticmethod
    def UNFOLD(fact_refs: 'list[IsabelleFact]') -> 'Minilang_Operation':
        return Minilang_Operation("UNFOLD", [r.pack() for r in fact_refs])
    @staticmethod
    def WITNESS(terms: list[term]) -> 'Minilang_Operation':
        return Minilang_Operation("WITNESS", terms)
    @staticmethod
    def BRANCH(cases: list[tuple[str | None, term]]) -> 'Minilang_Operation':
        return Minilang_Operation("BRANCH", [(n, ascii_of_unicode(t)) for n, t in cases])
    @staticmethod
    def CASE_SPLIT(target: term, vars: list[varname_spec] | None, rule: 'IsabelleFact | None') -> 'Minilang_Operation':
        return Minilang_Operation("CASE_SPLIT", (ascii_of_unicode(target), vars, rule))
    @staticmethod
    def INDUCT(target: term, vars: list[varname_spec] | None, arbitrary: list[varname], rule: 'IsabelleFact | None') -> 'Minilang_Operation':
        return Minilang_Operation("INDUCT", (ascii_of_unicode(target), vars, [ascii_of_unicode(t) for t in arbitrary], rule.pack() if rule is not None else None))
    @staticmethod
    def SPECIALIZE(
        name: str,
        rule_ref: 'IsabelleFact',
        instantiations: list[tuple[str, str]],  # (var_name, term_string)
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

type Extended_Minilang_Operation = Minilang_Operation | list[Minilang_Operation]


class Minilang_State:
    def __init__(self, connection: Connection, name: str, prooftree : ML_ProofTree | None):
        self.connection = connection
        self.name = name
        self.prooftree = prooftree
        self.messages : list[Message] = [] # the messages received during executing the operation that assigns to this state
    def initialized(self) -> bool:
        return self.prooftree is not None
    def prooftree_of(self) -> ML_ProofTree:
        if self.prooftree is None:
            raise InternalError("Prooftree is not initialized")
        return self.prooftree
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
        return Minilang_State(connection, cls.assign_name(), None)
    async def execute(self, opr: Extended_Minilang_Operation, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        if assign_to is None:
            assign_to = Minilang_State(self.connection, type(self).assign_name(), None)
        if isinstance(opr, Minilang_Operation):
            dest_name = assign_to.name
            session = the_session()
            # Log proof operation
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
                (msgs, tree) = await self.connection.callback("IsaMini.proof_opr",
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
            assign_to.prooftree = unpack_MLPT(tree)
            assign_to.messages = msgs
        else:
            raise NotImplementedError("Here we should implement the execution of a list of Minilang operations")
            #msgs = opr(self, assign_to)
        return assign_to
    async def sorry(self, varnames: list[varname_spec] | None, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        return await self.execute(Minilang_Operation.SORRY(varnames), assign_to)
    async def skip(self, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        return await self.execute(Minilang_Operation.SKIP(), assign_to)
    async def clone(self, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        if not self.initialized():
            if assign_to is None:
                assign_to = Minilang_State(self.connection, type(self).assign_name(), None)
            assign_to.messages = list(self.messages)
            return assign_to
        ret = await self.execute(Minilang_Operation.SKIP(), assign_to)
        ret.messages = self.messages
        return ret
    async def reset(self) -> None:
        """Remove this state from the Isabelle state table and mark as uninitialized."""
        try:
            await self.connection.callback("IsaMini.reset_state", self.name)
        except:
            pass
        self.prooftree = None
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
        out: list[IsabelleFact | Interaction_RetrieveForProof] = [None] * len(facts)  # type: ignore
        # Collect FactByName indices for batch lookup
        name_indices: list[int] = []
        name_queries: list[str] = []
        for i, fact in enumerate(facts):
            if fact["refer_by"] == "proposition":
                prop = cast(FactByProposition, fact)["proposition"]
                out[i] = IsabelleFact_ProveInTime(prop)
            elif fact["refer_by"] == "description":
                desc = " ".join(cast(FactByDescription, fact)["english"].split())
                out[i] = Interaction_RetrieveForProof(
                    state=self, query=desc, kinds=[EntityKind.THEOREM])
            else:
                name_indices.append(i)
                name_queries.append(fact["name"])
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
                    short_name, exprs, roles = result
                    out[idx] = IsabelleFact_Presented(
                        full_name=query_name, short_name=short_name,
                        fact=fact, expression=exprs, roles=roles)
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
                short_name, exprs, roles = result
                out[idx] = IsabelleFact_Presented(
                    full_name=query_name, short_name=short_name,
                    fact=original_fact, expression=exprs,
                    kind=kind, roles=roles)
        return out
    async def semantic_knn(self, query: str | None, k: int,
                     kinds: list[EntityKind],
                     term_patterns: list[str] = [],
                     type_patterns: list[str] = [],
                     theories_include: list[str] = [],
                     name_contains: list[str] = [],
                     exact_name: str | None = None,
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
                    uk, full_name = await universal_key_and_name_of(self.connection, tag, exact_name)
                except UndefinedEntity:
                    if "." in exact_name:
                        short = exact_name.rsplit(".", 1)[1]
                        try:
                            uk, full_name = await universal_key_and_name_of(self.connection, tag, short)
                        except Exception:
                            continue
                    else:
                        continue
                except IsabelleError:
                    continue
                rec = Semantic_DB[uk]
                if rec is not None:
                    scored_recs.append((1.0, rec._replace(name=ascii_of_unicode(rec.name))))
                else:
                    scored_recs.append((1.0, SemanticRecord(tag, ascii_of_unicode(full_name), None, None)))
            if not scored_recs:
                return [], [f'Undefined: "{exact_name}"']
            warnings: list[str] = []
            # Skip to entity resolution below
        else:

            term_patterns = [ascii_of_unicode(p) for p in term_patterns]
            type_patterns = [ascii_of_unicode(p) for p in type_patterns]
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
                raw_results, warnings = await store.lookup(query, k, kinds, domain,
                                       term_patterns=term_patterns,
                                       type_patterns=type_patterns,
                                       theories_include=theories_include,
                                       name_contains=name_contains)
                scored_recs = [(score, rec._replace(name=ascii_of_unicode(rec.name)))
                               for score, rec in raw_results]
            else:
                # Pattern-only search: get filtered entities, look up records, no ranking
                from Isabelle_RPC_Host.context import entities_of
                entries, warnings = await entities_of(self.connection, kinds,
                                         term_patterns=term_patterns,
                                         type_patterns=type_patterns,
                                         theories_include=theories_include,
                                         name_contains=name_contains,
                                         limit=k)
                scored_recs = []
                for uk, name, _ in entries:
                    rec = Semantic_DB[uk]
                    if rec is not None:
                        scored_recs.append((0.0, rec._replace(name=ascii_of_unicode(rec.name))))
                    else:
                        scored_recs.append((0.0, SemanticRecord(EntityKind(uk[16]), ascii_of_unicode(name), None, None)))
        if not scored_recs:
            return [], warnings
        # Resolve entities via RPC
        entity_keys = [(rec.kind, rec.name) for _, rec in scored_recs]
        infos = await self._retrieve_entity(entity_keys)
        out: list[RetrievedEntity] = []
        for (score, rec), info in zip(scored_recs, infos):
            if info is None:
                short_name, exprs, roles = rec.name, [], []
            else:
                short_name, exprs, roles = info
            if rec.kind in _THEOREM_KINDS:
                entity: IsabelleEntity = IsabelleFact_Presented(
                    full_name=rec.name, short_name=short_name,
                    fact=FactByName(refer_by="name", name=short_name),
                    expression=exprs, kind=rec.kind, roles=roles)
            else:
                entity = IsabelleEntity(
                    full_name=rec.name, short_name=short_name,
                    expression=exprs, kind=rec.kind, roles=roles)
            out.append(RetrievedEntity(
                entity=entity,
                score=score,
                interpretation=' '.join(rec.interpretation.split()) if rec.interpretation else None))
        return out, warnings
    async def compute_bindings(self, var_names: list[str], fact_names: list[str]) -> Bindings:
        """
        Compute bindings for the leading proof goal by binding provided names in order.
        var_names[i] is bound to the i-th quantified variable in the goal.
        fact_names[j] is bound to the j-th premise in the goal.
        Raises IsabelleError if the lengths don't match the goal structure.
        """
        bindings_data = await self.connection.callback("IsaMini.compute_bindings",
                                                  (self.name, var_names, fact_names))
        return Intro_Bindings_Msg._unpack_bindings(bindings_data)
    async def need_intro(self, consider_conj: bool) -> bool:
        """
        Check if the leading proof goal needs INTRO (i.e., has quantified variables or premises).
        If consider_conj is True, also considers conjunction as needing intro.
        """
        result = await self.connection.callback("IsaMini.need_intro", (self.name, consider_conj))
        return result
    async def _retrieve_entity(self, entities: list[tuple[EntityKind, str]]
        ) -> list[tuple[str, list[str], list[str]] | None]:
        """Retrieve entity info by kind and name (short or full).
        Returns list of (short_name, extra_strings, roles) or None per entity.
        extra_strings: propositions for theorems/rules, [type] for constants, [] for others.
        roles: list of system rule set tags ('simp', 'intro', 'elim') for theorems, [] for others."""
        args = [(int(kind), name) for kind, name in entities]
        results = await self.connection.callback(
            "IsaMini.retrieve_entity", (self.name, args))
        return [(pretty_unicode(r[0]), [pretty_unicode(e) for e in r[1]], list(r[2]))
                if r is not None else None for r in results]
    async def check_term(self, term_str: str) -> tuple[typ, Vars, Vars]:
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
                                                                         (self.name, term_str))
            frees = dict(frees_list)
            vars = dict(vars_list)
            return (term_type, frees, vars)
        except IsabelleError as e:
            if len(e.errors) >= 2 and e.errors[0] == "Unparsed":
                raise InternalError_UnparsedTerm(term_str, e.errors[1])
            else:
                raise

    async def schematic_variables_of(self) -> Vars:
        """
        Get all schematic variables from the leading proof goal.
        Returns a dict of {varname: type} where varnames are formatted as ?name.idx.
        """
        try:
            vars_list = await self.connection.callback("IsaMini.schematic_variables_of", self.name)
            return dict(vars_list)
        except IsabelleError as e:
            raise

    async def potential_defs_of(self, terms: list[str]) -> list[IsabelleFact_Presented]:
        """
        Get potential definitions for terms via Potential_Defs_Of RPC.
        Returns list of IsabelleFact_Presented, deduplicated by proposition.
        """
        result = await self.connection.callback("IsaMini.potential_defs_of", (self.name, terms))
        return [IsabelleFact_Presented(full_name=full_name,
                        short_name=short_name,
                        fact=FactByName(refer_by="name", name=short_name),
                        expression=[prop]) for full_name, short_name, prop in result]

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

### Interaction

# abstract base class
type answer = Annotated[list[int], "sorted and all elements are distinct"] | str

def normalize_answer(indexes: list[int] | None, text: str | None) -> answer:
    """Normalize the answer from two optional fields.
    indexes takes priority; text is used only when indexes is empty or absent."""
    if indexes:
        return sorted(set(indexes))
    if text:
        return text
    return []

class ForkingMode(Enum):
    NO = 0                        # inline, not forked
    FORKING_WITH_CTXT = 1         # fork inheriting parent conversation context
    FORKING_WITHOUT_CTXT = 2      # fork with fresh context, same model (opus)
    FORKING_CHEAPER_NO_CTXT = 3   # fork with fresh context, cheaper model (sonnet)

class InteractiveRetrievalMode(Enum):
    NO = "no"                                        # direct results, no forking
    YES = "yes"                                      # fork-based, answer tool only
    YES_WITH_RECURSIVE_RETRIEVAL = "yes_recursive"   # fork-based, can also search

INTERACTIVE_RETRIEVAL_MAP = {m.value: m for m in InteractiveRetrievalMode}

# Abstract tool identifiers (driver-agnostic)
type tool = str
TOOL_ANSWER: tool = "answer"
TOOL_SEARCH: tool = "query"

class Interaction:
    forking: ForkingMode = ForkingMode.NO
    fork_allowed_tools: list[tool] | None = None  # None = use session default
    async def prompt(self, indent: int, file: MyIO) -> None:
        raise NotImplementedError("`prompt` must be implemented by subclass")
    async def answer(self, answer: answer) -> Any:
        raise NotImplementedError("`answer` must be implemented by subclass")

class ImmediateAnswer(Exception):
    """Raised by prompt() when the interaction resolves without LLM input."""
    def __init__(self, answer: Any):
        self.answer = answer

type AsyncKontinuation = Callable[[list[Any]], Awaitable[Any]]

class RaiseInteraction(Exception):
    def __init__(self, interactions: list[Interaction],
                 kontinuation: AsyncKontinuation):
        self.interactions = interactions
        self.kontinuation = kontinuation

class Working_Interactions(NamedTuple):
    interactions: list[Interaction]
    results: list[Any]
    result_set: list[bool | Awaitable[Any]]  # False=pending, True=done, Awaitable=in-flight
    kontinuation: AsyncKontinuation

    async def run_continuation(self) -> Any:
        """Await any in-flight results, then call the continuation."""
        for i, flag in enumerate(self.result_set):
            if isinstance(flag, bool):
                if not flag:
                    raise InternalError(f"Interaction {i} not resolved before calling continuation")
            else:
                # Awaitable — wait for it
                await flag
                if not self.result_set[i] is True:
                    raise InternalError(f"Forked interaction {i} did not store its result")
        return await self.kontinuation(self.results)

class Interaction_BadAnswer(Exception):
    """Raised when an answer to an interaction is invalid. The interaction remains active."""
    pass

#### Fact Retrieval

_THEOREM_KINDS = frozenset({EntityKind.THEOREM, EntityKind.INTRODUCTION_RULE, EntityKind.ELIMINATION_RULE})

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
        self._candidate_facts_cache: list[RetrievedEntity] | None = None
        # Empty query forces FORKING_WITH_CTXT (fork needs parent context to judge relevance)
        session = the_session()
        if not query:
            self.forking = ForkingMode.FORKING_WITH_CTXT
        else:
            self.forking = session.retrieval_forking_mode
        # Tool access in forks: YES = answer only, YES_RECURSIVE = full access (None = default)
        if session.interactive_retrieval == InteractiveRetrievalMode.YES:
            self.fork_allowed_tools = [TOOL_ANSWER]

    async def candidate_facts(self) -> list[RetrievedEntity]:
        if self._candidate_facts_cache is None:
            self._candidate_facts_cache, _ = await self.state.semantic_knn(
                self.query, self.k, self.kinds,
                term_patterns=self.term_patterns,
                type_patterns=self.type_patterns,
                theories_include=self.theories_include,
                name_contains=self.name_contains)
        return self._candidate_facts_cache

    def _entity_title(self) -> str:
        """Dynamic title for the entity kind(s): 'theorems', 'constants', etc."""
        _KIND_TERMS = {
            EntityKind.THEOREM: "theorems", EntityKind.CONSTANT: "constants",
            EntityKind.TYPE: "types", EntityKind.CLASS: "typeclasses",
            EntityKind.LOCALE: "locales",
            EntityKind.INTRODUCTION_RULE: "introduction rules",
            EntityKind.ELIMINATION_RULE: "elimination rules",
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
                file.write(f"{i}. {fetched.entity.short_name}:")
                truncated = print_expression_list(indent+2, file, exprs)
            else:
                file.write(f"{i}. {fetched.entity.short_name}\n")
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
                 "expression": f.entity.expression,
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

    async def answer(self, answer: answer) -> 'list[IsabelleEntity | IsabelleFact]':
        # Text answer — rejected by default; subclass overrides for prove-in-time
        if isinstance(answer, str) and answer:
            raise Interaction_BadAnswer("Free-text answers are not allowed here. Select by index.")
        # Empty answer — expand search if possible
        if not answer:
            if self.k < self.FINAL_K:
                self.k = self.FINAL_K
                self._candidate_facts_cache = None
                await self.candidate_facts()
                async def identity(results: list[Any]) -> Any:
                    return results[0]
                raise RaiseInteraction([self], identity)
            else:
                await self._log_retrieval_training_data([])
                the_session().log_retrieval(self.query, ["none selected"])
                return []
        # Index answer
        if self.single_choice and len(answer) > 1:
            raise Interaction_BadAnswer("Please select exactly one entry.")
        facts = await self.candidate_facts()
        selected: list[IsabelleEntity] = []
        for idx in answer:
            if idx < 0 or idx >= len(facts):
                raise Interaction_BadAnswer(
                    f"Index {idx} out of range (0–{len(facts) - 1}).")
            selected.append(facts[idx].entity)
        await self._log_retrieval_training_data(list(answer))
        session = the_session()
        results = []
        for e in selected:
            expr = ", ".join(e.expression) if e.expression else ""
            results.append(f"{e.short_name}: {expr}" if expr else e.short_name)
        session.log_retrieval(self.query, results)
        return cast(list[IsabelleEntity | IsabelleFact], selected)


class Interaction_RetrieveForProof(Interaction_Retrieve):
    """Retrieve theorems/rules for proof operations. Supports prove-in-time and relevant constants."""

    def __init__(self, state: Minilang_State,
            query: str, kinds: list[EntityKind],
            **kwargs: Any):
        super().__init__(state, query, kinds, **kwargs)
        self._relevant_constants_cache: list[tuple[str, str, str | None]] | None = None

    async def relevant_constants(self) -> list[tuple[str, str, str | None]]:
        """Fetch relevant constants via semantic search (cached).
        Returns list of (short_name, type, interpretation) triples."""
        if self._relevant_constants_cache is None:
            results, _ = await self.state.semantic_knn(self.query, 10, [EntityKind.CONSTANT])
            self._relevant_constants_cache = [
                (r.entity.short_name,
                 r.entity.expression[0] if r.entity.expression else "",
                 r.interpretation)
                for r in results if r.score >= 0.5]
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
                file.write(f"- {short_name}: {typ}\n")
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

    async def answer(self, answer: answer) -> 'list[IsabelleEntity | IsabelleFact]':
        session = the_session()
        # Text answer → prove-in-time
        if isinstance(answer, str) and answer:
            await self._log_retrieval_training_data([], prove_in_time=answer)
            session.log_retrieval(self.query, [f"prove-in-time: {answer}"])
            return [IsabelleFact_ProveInTime(answer)]
        # Empty answer with no expansion left
        if not answer and self.k >= self.FINAL_K:
            await self._log_retrieval_training_data([])
            session.log_retrieval(self.query, ["unfound"])
            if self.single_choice:
                return [IsabelleFact_Unfound(
                    FactByDescription(refer_by="description", english=self.query))]
            return []
        return await super().answer(answer)


### The Abstract Model

# parsing_node receives two Minilang_State arguments:
#   alive_state: the latest initialized state within the current proof block.
#       Always non-None (search walks up through ancestors to root).
#       Suitable ONLY for retrieval (e.g., fetch_facts, potential_defs_of).
#       Must NOT be used for proof-goal-specific checks (e.g., need_intro).
#   exact_state: the actual ml_state at the insertion point, if available.
#       Suitable for proof-goal-specific operations (e.g., compute_bindings).
#       May be None if the state is not yet initialized.
# The exact state is also available later via config.ml_state in gen_node.
type parsing_node = Callable[[Minilang_State, Minilang_State | None], Awaitable['gen_node']]
type gen_node = Callable[[NodeConfig], 'Node']
type may_gen_node = Callable[[NodeConfig], 'Node | None']

def _trivial_parsing(gn: gen_node) -> parsing_node:
    """Wrap a sync gen_node in a parsing_node that ignores both states."""
    async def parse(alive_state: Minilang_State,
                    exact_state: Minilang_State | None = None) -> gen_node:
        return gn
    return parse

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

class Node(ABC):
    parent: 'NonLeaf_Node | None'
    id: 'step'
    line: int
    _changes_pending_goal = True

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
        self._is_trivial: bool | None = None
        self.age = self.session.age
        self.line = 0

    @property
    def titled_id(self) -> str:
        """Return e.g. 'step 1' or 'goal 2.1'."""
        return f"{self._kind} {self.id}"
    def id_of_goal(self) -> step | None:
        return self.id
    def _reset_local_step(self, new_local_step: str) -> None:
        self.local_step = new_local_step
        if self.parent is not None and self.parent.id:
            self.id = f"{self.parent.id}.{self.local_step}"
        else:
            self.id = self.local_step
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
        return self.quickview_header(indent, file)
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
        self.warnings[:] = [warning for warning in self.warnings if warning.position not in positions]
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
    def _on_edit_failure(self) -> EditFailureResponse:
        """Hook called when this node's evaluation status is FAILURE after fill/insert_before/amend.
        Derived classes can override to customize failure handling.
        Returns (is_error, failure_reason, revert)."""
        return EditFailureResponse(is_error=True, failure_reason=None, revert=False)
    @abstractmethod
    def assemble(self, output: list[Minilang_Operation] | None = None) -> list[Minilang_Operation]:
        """
        Assembling all the abstract tree model into the final sequence of Minilang operations
        """
        ...
    async def _refresh_me_alone(self) -> None:
        """
        must update self.status
        Convention: Any node must be up to date after calling any public Node method
        """
        self.age = self.session.age
        self._first_time = False
    async def _refresh_all_after_me(self) -> None:
        """
        refreshing the status of all the nodes excluding and after the `self`
        """
        if self.parent is None:
            raise InternalError("Don't know how to refresh a node and all its after nodes when the node's parent is none")
        else:
            await self.parent._refresh_all_children_after(self, self.status.status == EvaluationStatus.Status.SUCCESS)
    async def insert_before_me(self, pn: parsing_node) -> 'Node':
        if self.parent is None:
            raise InternalError("Don't know how to refresh a node and all its after nodes when the node's parent is none")
        else:
            node = await self.parent._insert_before_child(self, pn)
            if self.parent._can_continue_before_child(node):
                await node._refresh_me_alone()
            else:
                await node._cancel()
            await node._refresh_all_after_me()
            return node
    async def insert_before(self, step: step, pn: parsing_node) -> 'tuple[Node, bool, FailureReason | None]':
        try:
            node = self.locate_node(step)
            ret = await node.insert_before_me(pn)
            if ret.status.status == EvaluationStatus.Status.FAILURE:
                response = ret._on_edit_failure()
                if response.revert:
                    rp = ret._delete_me()
                    await rp._refresh_me_alone()
                    if rp.parent is not None:
                        await rp._refresh_all_after_me()
                return ret, response.is_error, response.failure_reason
            return ret, False, None
        except GoalIsNontrivial as e:
            raise CannotInsert_GoalIsNontrivial(e.parent)
        except NodeNotFound:
            raise CannotInsert_NodeNotFound(step)
    @abstractmethod
    async def append(self, pn: parsing_node) -> 'Node | None':
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
    async def fill(self, id: step, pn: parsing_node) -> 'tuple[Node, bool, FailureReason | None]':
        ids = id.split('.')
        node = self._locate_node(ids[:-1], id, 0)
        to_fill = node._id_of_openning_prf_to_fill()
        if to_fill is None:
            raise CannotFill_NodeNotFound(id)
        if to_fill != id:
            raise CannotFill_BadNode(id)
        try:
            ret = await node.append(pn)
        except GoalIsNontrivial as e:
            raise CannotFill_GoalIsNontrivial(e.parent)
        if ret is None:
            raise InternalError("Don't know how to fill a node when the node's append method returns None")
        if ret.status.status == EvaluationStatus.Status.FAILURE:
            response = ret._on_edit_failure()
            if response.revert:
                rp = ret._delete_me()
                await rp._refresh_me_alone()
                if rp.parent is not None:
                    await rp._refresh_all_after_me()
            return ret, response.is_error, response.failure_reason
        return ret, False, None
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
            await ret._refresh_me_alone()
            await ret._refresh_all_after_me()
    async def rename_fact(self, old_name: str, new_name: str) -> None:
        ret = self._rename_fact(old_name, new_name)
        if ret is None:
            raise CannotRename_FactNotFound(old_name, new_name)
        else:
            await ret._refresh_me_alone()
            await ret._refresh_all_after_me()
    def _print_fixed_vars_and_facts(self, indent: int, file: MyIO) -> None:
        fixed_vars = self._fixed_vars_at_me({})
        fixed_facts = self._fixed_facts_at_me({})
        if fixed_vars:
            print_indent(indent, file)
            file.write(f"variables:\n")
            for name, typ in fixed_vars.items():
                print_indent(indent+1, file)
                file.write(f"- {name}: {type}\n")
        if fixed_facts:
            print_indent(indent, file)
            file.write(f"facts:\n")
            for name, term in fixed_facts.items():
                print_indent(indent+1, file)
                file.write(f"- {name}: {term}\n")
    def _warn_discarded_nodes(self, discarded_nodes: list['Node'], msg: str, position: Warning.Position) -> None:
        def printer(indent: int, file: MyIO) -> int:
            print_indent(indent, file)
            file.write('- ')
            file.write(msg)
            file.write(':\n')
            for node in discarded_nodes:
                node.print(indent+1, file)
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
                await rp._refresh_me_alone()
                if rp.parent is not None:
                    await rp._refresh_all_after_me()
        return not_found
    async def amend_me(self, pn: parsing_node) -> 'tuple[Node, Node]':
        if self.parent is not None:
            return await self.parent._amend_child(self, pn)
        else:
            raise CannotAmend_Root()
    def _amend_from(self, old: 'Node') -> None:
        self._first_time = False
    async def amend(self, id: step, pn: parsing_node) -> 'tuple[Node, bool, FailureReason | None]':
        try:
            old_node = self.locate_node(id)
            new_node, old_node = await old_node.amend_me(pn)
            if new_node.status.status == EvaluationStatus.Status.FAILURE:
                response = new_node._on_edit_failure()
                if response.revert:
                    parent = new_node.parent
                    if parent is None:
                        raise InternalError("Cannot revert amend on root node")
                    for i, c in enumerate(parent.sub_nodes):
                        if c is new_node:
                            if isinstance(new_node, NonLeaf_Node) and isinstance(old_node, NonLeaf_Node):
                                old_node.sub_nodes[:] = new_node.sub_nodes
                                new_node.sub_nodes.clear()
                                for child in old_node.sub_nodes:
                                    child.parent = old_node
                            parent.sub_nodes[i] = old_node
                            old_node.parent = parent
                            if parent._can_continue_before_child(old_node):
                                await old_node._refresh_me_alone()
                            else:
                                await old_node._cancel()
                            await old_node._refresh_all_after_me()
                            break
                return new_node, response.is_error, response.failure_reason
            return new_node, False, None
        except GoalIsNontrivial as e:
            raise CannotAmend_GoalIsNontrivial(e.parent)
        except NodeNotFound:
            raise CannotAmend_NodeNotFound(id)

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
    async def _refresh_me_alone(self) -> None:
        now = time()
        await super()._refresh_me_alone()
        op = self.the_operation()
        if isinstance(op, FailureReason):
            self.status = EvaluationStatus.Failure(time() - now, op)
            return
        try:
            await self.ml_state.execute(op, self.resulting_state())
            self.status = EvaluationStatus.Success(time() - now)
        except IsabelleError as err:
            self.status = EvaluationStatus.Failure(time() - now, FailureReason(''.join(err.errors)))

    async def append(self, pn: parsing_node) -> 'Node | None':
        raise CannotAppend(self, "It is not a goal or a proof block")

class NonLeaf_Node(Node):
    _closed_by: Node | None # Some proof operation (e.g. Branch) may close a block, preventing all later appending to this block.
    sub_nodes: list['Node']

    def __init__(self, config: NodeConfig, thought: str, sub_nodes: list['Node']):
        super().__init__(config, thought)
        self.sub_nodes = sub_nodes
        self._closed_by = None
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
                        await child._refresh_me_alone()
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
    async def _insert_before_child(self, before: 'Node', pn: parsing_node) -> 'Node':
        """
        invalidates the status of all nodes including and after the `before`
        """
        for i, child in enumerate(self.sub_nodes):
            if child is before:
                if i == 0:
                    segs = split_id_into_segs(child.local_step)
                    if segs[-1] > 1:
                        segs[-1] -= 1
                    else:
                        segs[-1] -= 1
                        segs.append(1)
                    new_id = cat_segs_into_id(segs)
                else:
                    prev_id = split_id_into_segs(self.sub_nodes[i-1].local_step)
                    next_id = split_id_into_segs(self.sub_nodes[i].local_step)
                    if len(prev_id) > len(next_id):
                        segs = prev_id[:len(next_id) + 1]
                        segs[-1] += 1
                        new_id = cat_segs_into_id(segs)
                    else:
                        new_id = cat_segs_into_id(prev_id + [1])
                alive = self._find_alive_state(i)
                exact = child.ml_state if child.ml_state.initialized() else None
                gn = await pn(alive, exact)
                config = NodeConfig(new_id, await child.ml_state.clone(None), self)
                try:
                    node = gn(config)
                except GenNode_Error as e:
                    raise CannotInsert(before, str(e))
                for x in self.sub_nodes:
                    if x is node:
                        raise InternalError("The target node to insert is already in my children")
                self.sub_nodes.insert(i, node)
                self._is_trivial = None
                return node
        raise InternalError("Cannot find the target to insert-before in my children")
    def _remove_child(self, child: Node) -> None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                self.sub_nodes.pop(i)
                return
        raise InternalError("The target node is not my children")
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
    def _find_alive_state_among_children(self, position: int) -> 'Minilang_State | None':
        """Find the latest alive ml_state before `position` among sub_nodes.
        position = len(sub_nodes) means after all children.
        Does not cross block boundaries — does not check self.ml_state."""
        for i in range(min(position, len(self.sub_nodes)) - 1, -1, -1):
            if self.sub_nodes[i].ml_state.initialized():
                return self.sub_nodes[i].ml_state
        return None
    def _find_alive_state(self, position: int) -> Minilang_State:
        """Find an alive state: search children first, then walk up through ancestors.
        position = len(sub_nodes) means after all children.
        Always returns a non-None result (the root's ml_state should always be initialized)."""
        result = self._find_alive_state_among_children(position)
        if result is not None:
            return result
        if self.ml_state.initialized():
            return self.ml_state
        if self.parent is not None:
            for i, c in enumerate(self.parent.sub_nodes):
                if c is self:
                    return self.parent._find_alive_state(i)
        raise InternalError("No alive state found anywhere in the proof tree")
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
        for child in self.sub_nodes:
            child.quickview(indent, file)
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
    async def _amend_child(self, child: 'Node', pn: parsing_node) -> 'tuple[Node, Node]':
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                alive = self._find_alive_state(i)
                exact = child.ml_state if child.ml_state.initialized() else None
                gn = await pn(alive, exact)
                config = NodeConfig(child.local_step, await child.ml_state.clone(None), self)
                try:
                    new_node = gn(config)
                except GenNode_Error as e:
                    raise CannotAmend(self, child, str(e))
                self.sub_nodes[i] = new_node
                self._is_trivial = None
                new_node._amend_from(child)
                if self._can_continue_before_child(new_node):
                    await new_node._refresh_me_alone()
                else:
                    await new_node._cancel()
                await new_node._refresh_all_after_me()
                return new_node, child
        raise InternalError("The target node is not my children")
    def _amend_from(self, old: 'NonLeaf_Node') -> None:  # type: ignore[override]
        super()._amend_from(old)
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
    def __init__(self, config: NodeConfig, thought: str, sub_nodes: list['Node']):
        super().__init__(config, thought, sub_nodes)
        # Convention: the _state_before_ending_ should be used only when self.has_ending_opr()
        self._state_before_ending_ = Minilang_State.assign(config.ml_state)
        self._body_subnodes_succeeded = False
        self._allow_multi_goal = False
        self.open_pending_proof_line: int | None = None
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
    def _find_alive_state_among_children(self, position: int) -> 'Minilang_State | None':
        # Check _state_before_ending_ if position is at or past the end
        if position >= len(self.sub_nodes) and self._state_before_ending_.initialized():
            return self._state_before_ending_
        result = super()._find_alive_state_among_children(position)
        if result is not None:
            return result
        s = self._state_after_beginning()
        return s if s.initialized() else None
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

    async def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> 'FailureReason | None':
        try:
            await self.ml_state.execute(begin_opr, self._state_after_beginning())
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
    async def _refresh_me_alone(self):
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
            reason = await self._refresh_the_beginning_opr(begin_opr)
            if reason is not None:
                head_succeeded = False
                can_continue = False
        else:
            await self.ml_state.clone(self._state_after_beginning())
        await super()._refresh_me_alone()
        failed_child: Node | None = None
        for child in self.sub_nodes:
            if can_continue:
                await child._refresh_me_alone()
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
                # Populate _state_before_ending_ with the last successful state
                # (= the failing child's ml_state, which is the state before it ran)
                await failed_child.ml_state.clone(self._state_before_ending_)
            await self._state_after_beginning().sorry(None, self.resulting_state())
            self.status = EvaluationStatus.Success(time() - now, reason)
        else:
            self._body_subnodes_succeeded = False
            assert reason is not None
            self.status = EvaluationStatus.Failure(time() - now, reason)
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
        Returns False when prooftree is absent, has no goals,
        or only has the 'True' artifact from conjunction splitting."""
        ptree = self._state_before_ending_.prooftree
        if ptree is None:
            return False
        goals = ptree.top_goals()
        return bool(goals) and goals[0].conclusion != "True"
    def should_I_show_pending_goal(self) -> tuple[Goal, step] | None:
        if not self.has_pending_goal():
            return None
        to_fill = self._id_of_openning_prf_to_fill()
        if to_fill is None:
            return None
        ptree = self._state_before_ending_.prooftree
        assert ptree is not None  # guaranteed by has_pending_goal() above
        goals = ptree.top_goals()
        if len(goals) > 1 and not self._allow_multi_goal:
            raise InternalError("The open goals of StdBlock should not exceed one. "
            "To express multiple goals, you should use a StdBlock whose children are GoalNodes. See Rule as an example.")
        return (goals[0], to_fill)
    def _should_print_footer_pending_goal(self) -> bool:
        return True
    def _print_footer(self, indent: int, file: MyIO, show_warnings: bool = False) -> None:
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.FOOTER])
        if self.opening():
            ptree = self._state_before_ending_.prooftree
            if ptree is None:
                print_indent(indent, file)
                file.write("Error: Evaluation cancelled due to failures above\n")
            else:
                result = self.should_I_show_pending_goal()
                if result is not None:
                    goal, to_fill = result
                    self.open_pending_proof_line =\
                        print_pending_goal(goal, to_fill, indent, file, self._ctxt_of_filling(),
                                           show_goal=self._should_print_footer_pending_goal())
                else:
                    self.open_pending_proof_line = None
    def is_proof_finished(self) -> bool:
        unfinished_nodes = set()
        self.unfinished_nodes(unfinished_nodes)
        return len(unfinished_nodes) == 0
    def unfinished_nodes(self, ret: set['Node']) -> None:
        super().unfinished_nodes(ret)
        if self.opening():
            ptree = self._state_before_ending_.prooftree
            if ptree is None or self.has_pending_goal():
                ret.add(self)
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ("proof", indent+1)
    def _local_step_of_next_proof_step(self) -> local_step:
        if self.sub_nodes:
            return incr_id_major(self.sub_nodes[-1].local_step)
        else:
            return "1"
    def _id_of_openning_prf_to_fill(self) -> step | None:
        if self.opening():
            if self.id:
                return f"{self.id}.{self._local_step_of_next_proof_step()}"
            else:
                return self._local_step_of_next_proof_step()
        else:
            return None
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
            ptree = self._state_before_ending_.prooftree
            if ptree is None or self.should_I_show_pending_goal() is not None:
                return True
        return False
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.opening():
            ptree = self._state_before_ending_.prooftree
            if ptree is None:
                print_indent(indent, file)
                file.write("Error: Evaluation pending\n")
            elif self.should_I_show_pending_goal() is not None:
                print_indent(indent, file)
                if self.open_pending_proof_line is not None:
                    file.write(f"Error: Unfinished Proof (line {self.open_pending_proof_line})\n")
                else:
                    file.write("Error: Unfinished Proof\n")
        return indent
    def print_string(self, indent: int, show_warnings: bool = True) -> str:
        buffer = StringIO()
        self.print(indent, MyIO(buffer), show_warnings=show_warnings)
        return buffer.getvalue()
    def quickview_string(self, indent: int) -> str:
        buffer = StringIO()
        self.quickview(indent, MyIO(buffer))
        return buffer.getvalue()
    async def append(self, pn: parsing_node) -> 'Node | None':
        if not self.opening():
            raise CannotAppend_BlockClosed(self, self._closed_by)
        alive = self._find_alive_state(len(self.sub_nodes))
        local_step = self._local_step_of_next_proof_step()
        ml_state = await self._state_before_ending_.clone(None)
        gn = await pn(alive, ml_state if ml_state.initialized() else None)
        config = NodeConfig(local_step, ml_state, self)
        try:
            node = gn(config)
        except GenNode_Error as e:
            raise CannotAppend(self, str(e))
        if node is None:
            return None
        self.sub_nodes.append(node)
        self._is_trivial = None
        if self._can_continue_before_child(node):
            await node._refresh_me_alone()
        else:
            await node._cancel()
            return node
        if self.opening():
            ml_state = node.resulting_state()
            if await ml_state.need_intro(False):
                await self.append(_trivial_parsing(
                    lambda config: Intro(config, "", None, False)))
        # Propagate state upward via the cascade chain. Matches the behavior
        # of insert_before_me / _amend_child, which both call
        # _refresh_all_after_me after inserting. In particular this is what
        # makes GlobalEnv → GoalNode propagation fire for plain appends:
        # without it, global_env.append(Have) would never rerun GlobalEnv's
        # footer, so no SKIP from GlobalEnv's end state would ever be written
        # into the GoalNode checkpoints.
        await node._refresh_all_after_me()
        return node


class GoalContainer(NonLeaf_Node):
    def _child_has_ending_opr(self, child : Node) -> bool:
        return True
    def _ending_opr_of_child(self, child : Node) -> Minilang_Operation | None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i < len(self.sub_nodes) - 1:
                    return Minilang_Operation.NEXT(None)
                else:
                    return Minilang_Operation.END()
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
                 auto_proof: SubProof_parsed = None):
        super().__init__(config, "", [])
        self.is_single_goal = is_single_goal
        self.show_goal = show_goal
        self._allow_multi_goal = True
        self._kind = "goal"
        self.case_vars = None
        self.case_hyps = None
        if auto_proof is not None:
            local_step = self._local_step_of_next_proof_step()
            ml_state = Minilang_State.assign(self.ml_state)
            sub_config = NodeConfig(local_step, ml_state, self)
            self.sub_nodes.append(auto_proof(sub_config))
    @property
    def titled_id(self) -> str:
        return self.id
    def goal(self) -> Goal | None:
        ptree = self.ml_state.prooftree
        if ptree is None:
            return None
        return ptree.top_goal()
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
    def beginning_opr(self) -> None:
        return None
    def ending_opr(self) -> Minilang_Operation | None:
        if not isinstance(self.parent, GoalContainer):
            raise InternalError("The parent of a GoalNode is not a GoalContainer")
        return self.parent._ending_opr_of_child(self)
    def _has_ending_opr(self) -> bool:
        if not isinstance(self.parent, GoalContainer):
            raise InternalError("The parent of a GoalNode is not a GoalContainer")
        return self.parent._child_has_ending_opr(self)
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
    async def _refresh_me_alone(self):
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
        if self._first_time and not self.sub_nodes and await self.ml_state.need_intro(False):
            local_step = self._local_step_of_next_proof_step()
            ml_state = await self.ml_state.clone(None)
            config = NodeConfig(local_step, ml_state, self)
            intro = Intro(config, "", None, False)
            self.sub_nodes.append(intro)
        return await super()._refresh_me_alone()
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
            return indent
        else:
            done_mark = "done, " if self._should_print_done() else ""
            print_indent(indent, file)
            file.write(f"- {self.id} ({done_mark}line {self.line})\n")
            return indent + 1

class SubgoalMaker(GoalContainer, StdBlock):
    def _should_print_done(self) -> bool:
        return bool(self.sub_nodes) and super()._should_print_done()
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._initial_goal_index : int = 1
    @abstractmethod
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason':
        ...
    def has_ending_opr(self) -> bool:
        return True
    def _case_vars_of_child(self, child_ind: int) -> list[varname_spec] | None:
        return None
    def _new_goal_node(self, goal_index: int, ml_state: Minilang_State) -> GoalNode:
        return GoalNode(NodeConfig(str(goal_index+self._initial_goal_index), ml_state, self), False, True, None)
    def _on_regenerating_goals(self, goals: list[Goal]) -> None:
        pass
    async def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> 'FailureReason | None':
        is_init = self._first_time
        old_n_subnodes = len(self.sub_nodes)
        fail = await super()._refresh_the_beginning_opr(begin_opr)
        if fail is not None:
            return fail
        s0 = self._state_after_beginning()
        if s0.prooftree is None:
            raise InternalError("The prooftree of the state after beginning is not initialized, meaning the node is not refreshed")
        goals = s0.prooftree.top_goals()
        # TODO: try to reuse the existing subnodes instead of discarding them.
        if not self._first_time and len(goals) == len(self.sub_nodes):
            pass
        else:
            self._on_regenerating_goals(goals)
            if len(goals) <= 1:
                self.sub_nodes = []
                if self.parent is not None:
                    self.parent._open()
            else:
                if self.parent is not None:
                    self.parent._close_by(self)
                self.sub_nodes = []
                ml_state = await s0.clone(None)
                for i in range(len(goals)):
                    new_node = self._new_goal_node(i, ml_state)
                    self.sub_nodes.append(new_node)
                    ml_state = await ml_state.sorry(None, None)
        if not is_init and len(self.sub_nodes) != old_n_subnodes:
            self.changed = True
        return None
    def _id_of_openning_prf_to_fill(self) -> step | None:
        return None
    def opening(self) -> bool:
        return False


class SubgoalMaker_NoTailEnder(SubgoalMaker):
    def _child_has_ending_opr(self, child : Node) -> bool:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i < len(self.sub_nodes) - 1:
                    return True
                else:
                    return False
        raise InternalError("The given argument is not a child of this node")
    def _ending_opr_of_child(self, child : Node) -> Minilang_Operation | None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i < len(self.sub_nodes) - 1:
                    return Minilang_Operation.NEXT(self._case_vars_of_child(i+1))
                else:
                    return None
        raise InternalError("The given argument is not a child of this node")

class CaseSplit_Like(SubgoalMaker_NoTailEnder):
    case_vars: list[Var] | None
    case_hyps: list[Hyp] | None
    case_name: str | None
    _initial_proof: SubProof_parsed
    def __init__(self, *args, _initial_proof: SubProof_parsed = None, **kwargs):
        super().__init__(*args, **kwargs)
        self.case_vars = None
        self.case_hyps = None
        self._initial_proof = _initial_proof
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
        return GoalNode(NodeConfig(str(goal_index+self._initial_goal_index), ml_state, self), False, True,
                        auto_proof=self._initial_proof)
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
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False) -> None:
        if self.case_vars is not None:
            print_vars(self.case_vars, indent, file, {}, "fixing variables")
        if self.case_hyps is not None:
            print_hyps(self.case_hyps, indent, file, {}, "assuming premises")
    async def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> 'FailureReason | None':
        is_init = self._first_time
        old_case = (self.case_vars, self.case_hyps)
        fail = await super()._refresh_the_beginning_opr(begin_opr)
        if fail is None and not self.sub_nodes:
            # The case for nonempty self.sub_nodes is handled in _new_goal_node
            s = self._state_after_beginning()
            consider_case_msgs = [m for m in s.messages if isinstance(m, Consider_Case_Msg)]
            match consider_case_msgs:
                case [consider_case_msg]:
                    pass
                case _:
                    raise InternalError(f"Expected exactly one Consider_Case_Msg in Case's messages, got {len(consider_case_msgs)}")
            self.case_name = consider_case_msg.case
            self.case_vars = consider_case_msg.vars
            self.case_hyps = consider_case_msg.hyps
        if not is_init and (self.case_vars, self.case_hyps) != old_case:
            self.changed = True
        return fail
    # def _new_goal_node(self, goal_index: int, ml_state: Minilang_State) -> GoalNode:
    #     node = super()._new_goal_node(goal_index, ml_state)
    #     consider_case_msgs = [m for m in ml_state.messages if isinstance(m, Consider_Case_Msg)]
    #     match consider_case_msgs:
    #         case [consider_case_msg]:
    #             pass
    #         case _:
    #             raise InternalError(f"Expected exactly one Consider_Case_Msg in Case's messages, got {len(consider_case_msgs)}")
    #     node.local_step = consider_case_msg.case
    #     node.case_vars = consider_case_msg.vars
    #     node.case_hyps = consider_case_msg.hyps
    #     return node
    def _on_regenerating_goals(self, goals: list[Goal]) -> None:
        self.case_name = None
        self.case_vars = None
        self.case_hyps = None
    

### Operation registry for tool calls

class OperationMeta(NamedTuple):
    toolarg_typed_dict: type[Any]
    gen_func: Callable[[Any], parsing_node]

OPERATION_REGISTRY: dict[str, OperationMeta] = {}

def proof_operation(operation: str, toolarg_typed_dict: type[Any]):
    """
    Class decorator to register a tool operation and its ToolArg TypedDict.
    The operation name is given explicitly by `operation`, and the class must
    define a staticmethod `gen(arg: ToolArg) -> gen_node`.
    """
    def decorator(cls: type[Any]):
        if hasattr(cls, "interactive_gen"):
            OPERATION_REGISTRY[operation] = OperationMeta(toolarg_typed_dict, cls.interactive_gen)  # type: ignore[attr-defined]
        else:
            OPERATION_REGISTRY[operation] = OperationMeta(toolarg_typed_dict, cls.gen)  # type: ignore[attr-defined]
        return cls
    return decorator

class Statement(TypedDict):
    english: str
    isabelle: str

class NamedStatement(TypedDict):
    english: str
    isabelle: str
    name: NotRequired[str]

def print_statement(self: Statement, indent: int, file: MyIO):
    print_indent(indent, file)
    file.write(f"- english: {self["english"]}\n")
    print_indent(indent, file)
    file.write(f"  isabelle: {self["isabelle"]}\n")

### Concrete Models

def _filter_unfound(facts: list[IsabelleFact]) -> tuple[list[IsabelleFact], list[str]]:
    """Filter out IsabelleFact_Unfound from a list.
    Returns (kept_facts, warning_strings)."""
    kept: list[IsabelleFact] = []
    warnings: list[str] = []
    for f in facts:
        if isinstance(f, IsabelleFact_Unfound):
            warnings.append(f"Fact \"{f.name()}\" not found, skipped.")
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
            pit_statements.append(ascii_of_unicode(f.statement))
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
                f'{prefix}Ignored "{facts[idx].name()}" \u2014 not a known Isabelle theorem nor trivially provable. '
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


#### Obvious

class Obvious_ToolArg(TypedDict):
    facts: list[FactByName | FactByProposition]

class Obvious_InternalToolArg(NamedTuple):
    facts: list[IsabelleFact]

@proof_operation("Obvious", Obvious_ToolArg)
class Obvious(Leaf):
    def __init__(self, config: NodeConfig, arg: Obvious_InternalToolArg):
        if config.parent is not None and config.parent._is_trivial is False:
            raise GoalIsNontrivial(config.parent)
        super().__init__(config, "")
        self.fact_refs = arg.facts

    @staticmethod
    def gen(arg: Obvious_InternalToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: Obvious(config, arg))

    @staticmethod
    def interactive_gen(arg: Obvious_ToolArg) -> parsing_node:
        async def parse(alive_state: Minilang_State,
                        exact_state: Minilang_State | None = None) -> gen_node:
            if not arg["facts"]:
                return lambda config: Obvious(config, Obvious_InternalToolArg(facts=[]))
            # FactByName | FactByProposition only — no interactions possible
            fetched = cast(list[IsabelleFact], await alive_state.fetch_facts(arg["facts"]))
            facts, warnings = _filter_unfound(fetched)
            def mk(config: NodeConfig) -> 'Obvious':
                node = Obvious(config, Obvious_InternalToolArg(facts=facts))
                for w in warnings:
                    node.warnings.append(Warning(Warning.Position.FOOTER, w))
                return node
            return mk
        return parse
    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        print_indent(indent, file)
        file.write(f"operation: Obvious\n")
        if self.fact_refs:
            print_indent(indent, file)
            file.write(f"with facts:\n")
            for ref in self.fact_refs:
                ref.print(indent+1, file)
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent
    async def _refresh_me_alone(self) -> None:
        if self._first_time:
            self.fact_refs, pit_warnings = await _filter_unprovable(self.fact_refs, self.ml_state)
            for w in pit_warnings:
                self.warnings.append(Warning(Warning.Position.FOOTER, w))
        elif self.ml_state.initialized():
            self.fact_refs = await self.ml_state.refresh_facts(self.fact_refs)
        await super()._refresh_me_alone()
        if self.parent is not None:
            if self.status.status == EvaluationStatus.Status.SUCCESS:
                self.parent._is_trivial = True
            elif self.status.status == EvaluationStatus.Status.FAILURE:
                self.parent._is_trivial = False
    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        return Minilang_Operation.HAMMER(self.fact_refs, 30)
    def _on_edit_failure(self) -> EditFailureResponse:
        if self.status.status == EvaluationStatus.Status.FAILURE:
            file = MyIO(StringIO())
            if self.status.reason:
                file.write(self.status.reason.reason)
                file.write('\n')
            if self.warnings:
                self._print_warnings(0, file, list(Warning.Position))
            return EditFailureResponse(is_error=True, failure_reason=FailureReason(file.getvalue()), revert=True)
        return super()._on_edit_failure()

async def _parse_subproof(sp: SubProof, alive_state: Minilang_State | None) -> SubProof_parsed:
    """Parse a SubProof into a sync gen_node (or None for 'Given later').
    Reuses Obvious.interactive_gen for fact resolution.
    May raise NoAliveState."""
    if not _subproof_is_obvious(sp):
        return None
    return await Obvious.interactive_gen(sp)(alive_state)

def _gen_with_subproof(cls: type,
                       parent_factory: 'Callable[[NodeConfig, SubProof_parsed], Node]',
                       subproof: SubProof) -> parsing_node:
    """Build a parsing_node that parses a SubProof then creates the parent via parent_factory.
    The parent_factory receives the parsed SubProof and is responsible for adding the
    Obvious sub-node to its children."""
    async def parse(alive_state: Minilang_State | None,
                    exact_state: Minilang_State | None = None) -> gen_node:
        parsed = await _parse_subproof(subproof, alive_state)
        return lambda config: parent_factory(config, parsed)
    return parse


#### Witness

class Witness_ToolArg(TypedDict):
    thought: str
    witness: str

@proof_operation("Witness", Witness_ToolArg)
class Witness(Leaf):
    def __init__(self, config: NodeConfig, arg: Witness_ToolArg):
        super().__init__(config, arg["thought"])
        self.witness = arg["witness"]
    def quickview_title(self) -> str:
        return f"Witness {self.witness}"
    @staticmethod
    def gen(arg: Witness_ToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: Witness(config, arg))

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
        return Minilang_Operation.WITNESS([ascii_of_unicode(self.witness)])


#### Unfold

class Interaction_ChooseDef(Interaction):
    def __init__(self, constants: list[str], candidate_defs: list[IsabelleFact_Presented]):
        """
        Args:
            constants: List of constants being unfolded
            candidate_defs: List of candidate definitions
        """
        self.constants = constants
        self.candidate_defs = candidate_defs
    async def prompt(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        if len(self.constants) == 1:
            file.write(f"Multiple definitions found for {self.constants[0]}:\n")
        else:
            file.write(f"Multiple definitions found for constants {', '.join(self.constants)}:\n")
        for i, ref in enumerate(self.candidate_defs):
            print_indent(indent+1, file)
            file.write(f"{i}. {ref.full_name}: {ref.expression}\n")
        file.write("Select definition(s) to use in unfolding. Call `mcp__proof__answer` with `indexes`, or leave empty to skip.\n")
    async def answer(self, answer: answer) -> list[IsabelleFact]:
        if isinstance(answer, str):
            raise Interaction_BadAnswer("This interaction expects index selection, not text.")
        if not answer:
            return []
        for idx in answer:
            if idx < 0 or idx >= len(self.candidate_defs):
                raise Interaction_BadAnswer(
                    f"Index {idx} out of range (0–{len(self.candidate_defs) - 1}).")
        return [self.candidate_defs[idx] for idx in answer]


class Unfold_ToolArg(TypedDict):
    thought: str
    targets: list[str]  # Isabelle/HOL terms to unfold

class Unfold_ToolArg_internal(TypedDict):
    thought: str
    targets: list[str]  # Isabelle/HOL terms to unfold
    fact_refs: list[IsabelleFact]


@proof_operation("Unfold", Unfold_ToolArg)
class Unfold(Leaf):
    def __init__(self, config: NodeConfig, arg: Unfold_ToolArg_internal):
        """
        Initialize with already-resolved fact references.
        This is called after interactive_gen completes.
        """
        super().__init__(config, arg["thought"])
        self.targets = arg["targets"]
        self.fact_refs = arg["fact_refs"]
    def quickview_title(self) -> str:
        return f"Unfold {', '.join(self.targets)}"
    @staticmethod
    def gen(arg: Unfold_ToolArg_internal) -> parsing_node:
        """Simple non-interactive generation with pre-resolved fact refs."""
        return _trivial_parsing(lambda config: Unfold(config, arg))

    @staticmethod
    def interactive_gen(arg: Unfold_ToolArg) -> parsing_node:
        """
        Interactive generation that queries RPC for potential definitions.
        Raises Interaction_ChooseDef if multiple definitions exist.
        Supports multiple targets.
        """
        targets = arg["targets"]

        async def parse(alive_state: Minilang_State,
                        exact_state: Minilang_State | None = None) -> gen_node:
            # Query potential definitions for all targets via RPC
            all_defs = await alive_state.potential_defs_of(targets)

            if len(all_defs) == 0:
                raise GenNode_Error(f"No definitions found for: {', '.join(targets)}")

            elif len(all_defs) == 1:
                # Single definition - use it automatically
                def mk(config: NodeConfig) -> 'Unfold':
                    arg_internal: Unfold_ToolArg_internal = {
                        "thought": arg["thought"],
                        "targets": arg["targets"],
                        "fact_refs": [all_defs[0]]
                    }
                    return Unfold(config, arg_internal)
                return mk

            else:
                # Multiple definitions - need interaction
                async def kontinue(results: list[Any]) -> gen_node:
                    selected: list[IsabelleFact] = results[0]
                    def final_mk(cfg: NodeConfig) -> 'Unfold':
                        arg_internal: Unfold_ToolArg_internal = {
                            "thought": arg["thought"],
                            "targets": arg["targets"],
                            "fact_refs": selected
                        }
                        return Unfold(cfg, arg_internal)
                    return final_mk

                raise RaiseInteraction(
                    [Interaction_ChooseDef(targets, all_defs)],
                    kontinue
                )
        return parse

        return mk

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

    async def _refresh_me_alone(self) -> None:
        if not self._first_time and self.ml_state.initialized():
            self.fact_refs = await self.ml_state.refresh_facts(self.fact_refs)
        await super()._refresh_me_alone()

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        if not self.targets:
            return FailureReason("Unfold operation must specify at least one target.")
        if not self.fact_refs:
            return FailureReason("Unfold operation must specify at least one fact reference.")
        unfound = [f for f in self.fact_refs if isinstance(f, IsabelleFact_Unfound)]
        if unfound:
            return FailureReason("\n".join(f"Fact \"{f.name()}\" not found" for f in unfound))
        return Minilang_Operation.UNFOLD(self.fact_refs)


#### Derive

class Instantiation(TypedDict):
    name: str     # variable name (e.g., "x", "n")
    value: str    # Isabelle term string (e.g., "Suc 0")

class Derive_ToolArg(TypedDict):
    thought: str
    rule: FactByName                              # The rule to specialize
    instantiations: list[Instantiation]           # Variable instantiations
    discharging_facts: list[FactByName]           # Facts to discharge premises
    result_name: str                              # Name to bind the result under

class Derive_InternalToolArg(NamedTuple):
    thought: str
    rule: FactByName
    rule_ref: IsabelleFact
    instantiations: list[Instantiation]
    discharging_facts: list[FactByName]
    discharge_refs: list[IsabelleFact]
    result_name: str

@proof_operation("Derive", Derive_ToolArg)
class Derive(Leaf):
    def __init__(self, config: NodeConfig, arg: Derive_InternalToolArg):
        super().__init__(config, arg.thought)
        self.rule = arg.rule
        self.rule_ref = arg.rule_ref
        self.instantiations = arg.instantiations
        self.discharging_facts = arg.discharging_facts
        self.discharge_refs = arg.discharge_refs
        self.result_name = arg.result_name
        self.result_facts: list[tuple[str, str]] | None = None
        """(fact_name, pretty_expression) pairs for facts derived by SPECIALIZE,
        populated from Specialize_Result_Msg after successful execution."""

    def quickview_title(self) -> str:
        return f"Derive {self.rule_ref.name()}"

    @staticmethod
    def gen(arg: Derive_InternalToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: Derive(config, arg))

    @staticmethod
    def interactive_gen(arg: Derive_ToolArg) -> parsing_node:
        async def parse(alive_state: Minilang_State,
                        exact_state: Minilang_State | None = None) -> gen_node:
            all_facts = [arg["rule"]] + arg.get("discharging_facts", [])
            # FactByName only — no interactions possible
            fetched = cast(list[IsabelleFact], await alive_state.fetch_facts(all_facts))
            rule_ref = fetched[0]
            discharge_refs = fetched[1:]
            internal = Derive_InternalToolArg(
                thought=arg["thought"],
                rule=arg["rule"],
                rule_ref=rule_ref,
                instantiations=arg.get("instantiations", []),
                discharging_facts=arg.get("discharging_facts", []),
                discharge_refs=discharge_refs,
                result_name=arg["result_name"])
            return lambda config: Derive(config, internal)
        return parse

    async def _refresh_me_alone(self) -> None:
        if not self._first_time and self.ml_state.initialized():
            refreshed = await self.ml_state.refresh_facts(
                [self.rule_ref, *self.discharge_refs])
            self.rule_ref = refreshed[0]
            self.discharge_refs = refreshed[1:]
        await super()._refresh_me_alone()
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
        self.rule_ref.print(indent+1, file)
        if self.instantiations:
            print_indent(indent, file)
            file.write("instantiations:\n")
            for inst in self.instantiations:
                print_indent(indent+1, file)
                file.write(f"- {inst['name']} = {inst['value']}\n")
        if self.discharge_refs:
            print_indent(indent, file)
            file.write("discharging facts:\n")
            for ref in self.discharge_refs:
                ref.print(indent+1, file)
        # if self.result_name:
        #     print_indent(indent, file)
        #     file.write(f"result name: {self.result_name}\n")
        if self.result_facts is not None:
            print_indent(indent, file)
            file.write("resulting facts:\n")
            for name, expr in self.result_facts:
                print_indent(indent + 1, file)
                file.write(f"- {name}: {expr}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent

    def _on_edit_failure(self) -> EditFailureResponse:
        if self.status.status == EvaluationStatus.Status.FAILURE:
            file = MyIO(StringIO())
            if self.status.reason:
                file.write(self.status.reason.reason)
                file.write('\n')
            if self.warnings:
                self._print_warnings(0, file, list(Warning.Position))
            return EditFailureResponse(is_error=True, failure_reason=FailureReason(file.getvalue()), revert=True)
        return super()._on_edit_failure()

    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        if self.result_facts is not None:
            for name, expr in self.result_facts:
                ret[name] = expr
        return ret

    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        return self._fixed_facts_at_me(ret)

    def the_operation(self) -> 'Minilang_Operation | FailureReason':
        if isinstance(self.rule_ref, IsabelleFact_Unfound):
            return FailureReason(f"Rule fact \"{self.rule_ref.name()}\" not found")
        unfound = [f for f in self.discharge_refs if isinstance(f, IsabelleFact_Unfound)]
        if unfound:
            return FailureReason("\n".join(f"Fact \"{f.name()}\" not found" for f in unfound))
        return Minilang_Operation.SPECIALIZE(
            self.result_name,
            self.rule_ref,
            [(i["name"], i["value"]) for i in self.instantiations],
            self.discharge_refs
        )


#### Rewrite

Rewrite_ToolArg = TypedDict('Rewrite_ToolArg', {
    'thought': str,
    'using': list[FactByName | FactByProposition],
    'use system simplifiers': bool,
    'rewrite goal': bool,
    'rewrite premises': list[str]
})

class Rewrite_InternalToolArg(NamedTuple):
    thought: str
    use_system_simplifiers: bool
    rewrite_goal: bool
    rewrite_premises: list[str]
    using: list[IsabelleFact]

@proof_operation("Rewrite", Rewrite_ToolArg)
class Rewrite(Leaf):
    def __init__(self, config: NodeConfig, arg: Rewrite_InternalToolArg):
        super().__init__(config, arg.thought)
        self.use_system_simplifiers = arg.use_system_simplifiers
        self.rewrite_goal = arg.rewrite_goal
        self.rewrite_premises = arg.rewrite_premises
        self.using = arg.using
        self.bindings: Bindings | None = None
        self.running_time = 0
    def quickview_title(self) -> str:
        targets: list[str] = []
        if self.rewrite_goal:
            targets.append("goal")
        targets.extend(self.rewrite_premises)
        return f"Rewrite {', '.join(targets)}"
    @staticmethod
    def gen(arg: Rewrite_InternalToolArg) -> parsing_node:
        """Non-interactive generation with pre-resolved fact refs."""
        return _trivial_parsing(lambda config: Rewrite(config, arg))

    @staticmethod
    def interactive_gen(arg: Rewrite_ToolArg) -> parsing_node:
        """Resolve facts and create Rewrite node."""
        async def parse(alive_state: Minilang_State,
                        exact_state: Minilang_State | None = None) -> gen_node:
            # FactByName | FactByProposition only — no interactions possible
            fetched = cast(list[IsabelleFact], await alive_state.fetch_facts(arg["using"]))
            internal = Rewrite_InternalToolArg(
                thought=arg["thought"],
                use_system_simplifiers=arg["use system simplifiers"],
                rewrite_goal=arg["rewrite goal"],
                rewrite_premises=arg["rewrite premises"],
                using=fetched,
            )
            return lambda config: Rewrite(config, internal)
        return parse

    def print(self, indent: int, file: MyIO, update_line: bool = False, show_warnings: bool = False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Rewrite\n")
        if self.using or self.use_system_simplifiers:
            print_indent(indent, file)
            file.write(f"using:\n")
            for ref in self.using:
                ref.print(indent+1, file)
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
            result_goal = self.resulting_state().prooftree_of().top_goal_or_none()
            if result_goal is None:
                print_indent(indent, file)
                file.write("goal is solved.\n")
            elif result_goal.conclusion != self.ml_state.prooftree_of().top_goal().conclusion:
                print_indent(indent, file)
                file.write("goal changes into:\n")
                print_goal(result_goal, indent+1, False, file, self._ctxt_at_me())

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
        unfound = [f for f in self.using if isinstance(f, IsabelleFact_Unfound)]
        if unfound:
            return FailureReason("\n".join(f"Fact \"{f.name()}\" not found" for f in unfound))
        bindings = None
        if self.bindings is not None:
            var_bindings = [(vb.internal_varname, vb.external_varname, vb.type) for vb in self.bindings[0]]
            fact_bindings = [(fb.expr, fb.name, fb.pretty) for fb in self.bindings[1]]
            bindings = (var_bindings, fact_bindings)
        return Minilang_Operation.SIMPLIFY(
            self.using,
            self.use_system_simplifiers,
            self.rewrite_premises,
            self.rewrite_goal,
            bindings
        )

    async def _refresh_me_alone(self) -> None:
        is_init = self._first_time
        if self._first_time:
            self.using, pit_warnings = await _filter_unprovable(self.using, self.ml_state)
            for w in pit_warnings:
                self.warnings.append(Warning(Warning.Position.FOOTER, w))
        elif self.ml_state.initialized():
            self.using = await self.ml_state.refresh_facts(self.using)
        old_bindings = self.bindings
        old_goal = (self.resulting_state().prooftree_of().top_goal_or_none()
                    if self.status.status == EvaluationStatus.Status.SUCCESS
                    else None)
        # Execute the operation via parent Leaf implementation
        await super()._refresh_me_alone()

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
                            file.write(f"- {binding.external_varname}: {binding.type}\n")
                        return indent
                    self.warnings.append(Warning(Warning.Position.HEADER, print_var_warning))

                # Warn about auto-introduced premises
                if auto_facts:
                    def print_fact_warning(indent: int, file: MyIO) -> int:
                        print_indent(indent, file)
                        file.write(f"- The proof goal has changed and new premises occur:\n")
                        for binding in auto_facts:
                            print_indent(indent+1, file)
                            file.write(f"- {binding.name}\n")
                        return indent
                    self.warnings.append(Warning(Warning.Position.HEADER, print_fact_warning))

            # Check for simplify fallback (system simplifiers disabled due to timeout)
            fallback_msgs = [m for m in messages if isinstance(m, Simplify_Fallback_Nosys_Msg)]
            if fallback_msgs:
                self.use_system_simplifiers = False
                self.warnings.append(Warning(Warning.Position.HEADER,
                    "System simplifiers caused a timeout and were disabled for this step."))

        if not is_init:
            if self.bindings != old_bindings:
                self.changed = True
            if self.status.status == EvaluationStatus.Status.SUCCESS and old_goal is not None:
                new_goal = self.resulting_state().prooftree_of().top_goal_or_none()
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
                    self.bindings[1][i] = FactBinding(fact.expr, new_name, fact.pretty)
                    return self
        return super()._rename_fact(old_name, new_name)

    def _on_edit_failure(self) -> EditFailureResponse:
        if self.status.status == EvaluationStatus.Status.FAILURE:
            file = MyIO(StringIO())
            if self.status.reason:
                file.write(self.status.reason.reason)
                file.write('\n')
            if self.warnings:
                self._print_warnings(0, file, list(Warning.Position))
            return EditFailureResponse(is_error=True, failure_reason=FailureReason(file.getvalue()), revert=True)
        return super()._on_edit_failure()


#### Have

class Have_ToolArg(TypedDict):
    thought: str
    statement: Statement
    name: str
    proof: SubProof
    auto_apply: NotRequired[bool]

@proof_operation("Have", Have_ToolArg)
class Have(StdBlock):
    _changes_pending_goal = False
    def __init__(self, config: NodeConfig, arg : Have_ToolArg,
                 subproof_parsed: SubProof_parsed = None):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
        self.name = arg["name"]
        self.auto_apply = arg.get("auto_apply", False)
        # Populated from `Newly_Fixed_Vars_Msg` after the HAVE op runs.
        self.for_any: list[tuple[str, str]] = []
        if subproof_parsed is not None:
            local_step = self._local_step_of_next_proof_step()
            ml_state = Minilang_State.assign(self.ml_state)
            sub_config = NodeConfig(local_step, ml_state, self)
            self.sub_nodes.append(subproof_parsed(sub_config))
    @staticmethod
    def gen(arg : Have_ToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: Have(config, arg))
    @staticmethod
    def interactive_gen(arg : Have_ToolArg) -> parsing_node:
        return _gen_with_subproof(Have,
            lambda config, parsed: Have(config, arg, subproof_parsed=parsed),
            arg["proof"])
    def quickview_title(self) -> str:
        return f"Have {self.name}"
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Have\n")
        print_indent(indent, file)
        file.write(f"statement:\n")
        print_indent(indent+1, file)
        file.write(f"english: {self.statement['english']}\n")
        print_indent(indent+1, file)
        file.write(f"isabelle: {self.statement['isabelle']}\n")
        if self.for_any:
            print_indent(indent, file)
            file.write("for_any:\n")
            for name, typ in self.for_any:
                print_indent(indent+1, file)
                file.write(f"{name}: {typ}\n")
        print_indent(indent, file)
        file.write(f"name: {self.name}\n")
        if self.auto_apply:
            print_indent(indent, file)
            file.write("auto_apply: true\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.HAVE(self.name, self.statement['isabelle'], self.auto_apply)
    async def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> 'FailureReason | None':
        fail = await super()._refresh_the_beginning_opr(begin_opr)
        if fail is not None:
            return fail
        msgs = [m for m in self._state_after_beginning().messages
                if isinstance(m, Newly_Fixed_Vars_Msg)]
        if msgs:
            self.for_any = msgs[0].vars
        if self._first_time and not self.sub_nodes and await self._state_after_beginning().need_intro(False):
            local_step = self._local_step_of_next_proof_step()
            ml_state = await self._state_after_beginning().clone(None)
            config = NodeConfig(local_step, ml_state, self)
            intro = Intro(config, "", None, False)
            self.sub_nodes.append(intro)
        return None
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
        ret[self.name] = self.statement['isabelle']
        return ret

#### Suffices

class Suffices_ToolArg(TypedDict):
    thought: str
    statement: Statement
    proof: SubProof

@proof_operation("Suffices", Suffices_ToolArg)
class Suffices(StdBlock):
    def __init__(self, config: NodeConfig, arg : Suffices_ToolArg,
                 subproof_parsed: SubProof_parsed = None):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
        if subproof_parsed is not None:
            local_step = self._local_step_of_next_proof_step()
            ml_state = Minilang_State.assign(self.ml_state)
            sub_config = NodeConfig(local_step, ml_state, self)
            self.sub_nodes.append(subproof_parsed(sub_config))
    @staticmethod
    def gen(arg : Suffices_ToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: Suffices(config, arg))
    @staticmethod
    def interactive_gen(arg : Suffices_ToolArg) -> parsing_node:
        return _gen_with_subproof(Suffices,
            lambda config, parsed: Suffices(config, arg, subproof_parsed=parsed),
            arg["proof"])
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Suffices\n")
        print_indent(indent, file)
        file.write(f"statement:\n")
        print_indent(indent+1, file)
        file.write(f"english: {self.statement['english']}\n")
        print_indent(indent+1, file)
        file.write(f"isabelle: {self.statement['isabelle']}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
        if not self.sub_nodes:
            print_indent(indent, file)
            file.write(f"notice: Need to show the provided statement implies the goal\n")
    def beginning_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.SUFFICES(self.statement['isabelle'])
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
    constraints: list[NamedStatement]
    proof: SubProof

@proof_operation("Obtain", Obtain_ToolArg)
class Obtain(StdBlock):
    _changes_pending_goal = False
    def __init__(self, config: NodeConfig, arg : Obtain_ToolArg,
                 subproof_parsed: SubProof_parsed = None):
        super().__init__(config, arg["thought"], [])
        self.variables = arg["variables"]
        self.constraints = arg["constraints"]
        if subproof_parsed is not None:
            local_step = self._local_step_of_next_proof_step()
            ml_state = Minilang_State.assign(self.ml_state)
            sub_config = NodeConfig(local_step, ml_state, self)
            self.sub_nodes.append(subproof_parsed(sub_config))
    @staticmethod
    def gen(arg : Obtain_ToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: Obtain(config, arg))
    @staticmethod
    def interactive_gen(arg : Obtain_ToolArg) -> parsing_node:
        return _gen_with_subproof(Obtain,
            lambda config, parsed: Obtain(config, arg, subproof_parsed=parsed),
            arg["proof"])
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
            if v['type'] is not None:
                file.write(f"- {v['name']}: {v['type']}\n")
            else:
                file.write(f"- {v['name']}\n")
        match self.constraints:
            case []:
                pass
            case [constraint]:
                print_indent(indent, file)
                file.write(f"constraint:\n")
                if "name" in constraint:
                    print_indent(indent+1, file)
                    file.write(f"name: {constraint['name']}\n")
                print_indent(indent+1, file)
                file.write(f"english: {constraint['english']}\n")
                print_indent(indent+1, file)
                file.write(f"isabelle: {constraint['isabelle']}\n")
            case _:
                print_indent(indent, file)
                file.write(f"constraints:\n")
                for constraint in self.constraints:
                    print_indent(indent+1, file)
                    if "name" in constraint:
                        file.write(f"- name: {constraint['name']}\n")
                        print_indent(indent+1, file)
                        file.write(f"  english: {constraint['english']}\n")
                    else:
                        file.write(f"- english: {constraint['english']}\n")
                    print_indent(indent+1, file)
                    file.write(f"  isabelle: {constraint['isabelle']}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason | None':
        if not self.variables:
            return FailureReason("Must specify at least one variable to obtain.")
        return Minilang_Operation.OBTAIN(self.variables, [(c.get("name"), c["isabelle"]) for c in self.constraints])
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
    variable_bindings: NotRequired[list[varname]]
    fact_bindings: NotRequired[list[varname]]
    split_conj: NotRequired[bool]

@proof_operation("Intro", Intro_ToolArg)
class Intro(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, thought: str, bindings: Bindings | None, split_conj: bool,
                 _pending_bindings: tuple[list, list] | None = None):
        super().__init__(config, thought, [])
        self.bindings = bindings
        self.split_conj = split_conj
        self.running_time = 0
        self._pending_bindings = _pending_bindings
    @staticmethod
    def gen(arg: Intro_ToolArg) -> parsing_node:
        var_bindings = arg.get("variable_bindings", [])
        fact_bindings = arg.get("fact_bindings", [])
        pending = (var_bindings, fact_bindings) if var_bindings or fact_bindings else None
        split_conj = arg.get("split_conj", False)
        thought = arg["thought"]
        async def parse(alive_state: Minilang_State,
                        exact_state: Minilang_State | None = None) -> gen_node:
            if pending is not None and exact_state is not None:
                bindings = await exact_state.compute_bindings(pending[0], pending[1])
                return lambda config: Intro(config, thought, bindings, split_conj)
            return lambda config: Intro(config, thought, None, split_conj,
                                        _pending_bindings=pending)
        return parse
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
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
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    async def _refresh_me_alone(self):
        if self._pending_bindings is not None:
            var_bindings, fact_bindings = self._pending_bindings
            self.bindings = await self.ml_state.compute_bindings(var_bindings, fact_bindings)
            self._pending_bindings = None
        await super()._refresh_me_alone()
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.INTRO(self.bindings, self.split_conj)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to introduce the variables and premises because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def has_ending_opr(self) -> bool:
        return False
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("An Intro doesn't have an ending operation")
    def ending_opr(self) -> Minilang_Operation | None:
        return None
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, indent-1)
        else:
            return ("goals", indent+1)
    async def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> 'FailureReason | None':
        is_init = self._first_time
        old_bindings = self.bindings
        s = self._state_after_beginning()
        old_goals = s.prooftree.top_goals() if s.prooftree is not None else None
        fail = await super()._refresh_the_beginning_opr(begin_opr)
        if fail is None:
            self.running_time += 1
            messages = self._state_after_beginning().messages
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
                if intro_bindings_msg.auto_introduced[0]:
                    def print(indent: int, file: MyIO) -> int:
                        print_indent(indent, file)
                        file.write(f"- The proof goal has changed and new universally quantified variables occur:\n")
                        for binding in intro_bindings_msg.auto_introduced[0]:
                            print_indent(indent+1, file)
                            if binding.external_varname == binding.internal_varname:
                                file.write(f"- {binding.external_varname}\n")
                            else:
                                file.write(f"- {binding.internal_varname}, renamed to {binding.external_varname} to prevent name conflicts\n")
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
                            file.write(f"- {binding.name}\n")
                        return indent
                    self.warnings.append(Warning(Warning.Position.HEADER, print))
        if not is_init:
            if self.bindings != old_bindings:
                self.changed = True
            if fail is None and old_goals is not None:
                new_goals = self._state_after_beginning().prooftree_of().top_goals()
                if new_goals != old_goals:
                    self.changed = True
        return fail
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
        if self.sub_nodes:
            return ret
        else:
            return self._fixed_vars_at_me(ret)
    def _fixed_facts_after_me(self, ret: Hyps) -> Hyps:
        if self.sub_nodes:
            return ret
        else:
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
                    self.bindings[1][i] = FactBinding(fact.expr, new_name, fact.pretty)
                    return self
        return super()._rename_fact(old_name, new_name)


#### InferenceRule

class InferenceRule_ToolArg(TypedDict):
    thought: str
    rule: FactByName | FactByDescription | None
    # TODO: write some skills telling the agent how to associate common operations (e.g., proof by contradiction, proof by cases, etc.) with the inference rules

class InferenceRule_InternalToolArg(NamedTuple):
    thought: str
    rule: FactByName | FactByDescription | None
    rule_ref: IsabelleFact | None

@proof_operation("InferenceRule", InferenceRule_ToolArg)
class InferenceRule(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, arg: InferenceRule_InternalToolArg):
        super().__init__(config, arg.thought, [])
        self.rule = arg.rule
        self.rule_ref = arg.rule_ref
        self._opening = False

    @staticmethod
    def gen(arg: InferenceRule_InternalToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: InferenceRule(config, arg))

    @staticmethod
    def interactive_gen(arg: InferenceRule_ToolArg) -> parsing_node:
        async def parse(alive_state: Minilang_State,
                        exact_state: Minilang_State | None = None) -> gen_node:
            rule = arg["rule"]
            if rule is None:
                return lambda config: InferenceRule(config, InferenceRule_InternalToolArg(
                    thought=arg["thought"], rule=None, rule_ref=None))

            fetched = await alive_state.fetch_facts([rule])
            result = fetched[0]
            if isinstance(result, IsabelleFact):
                internal = InferenceRule_InternalToolArg(
                    thought=arg["thought"], rule=rule, rule_ref=result)
                return lambda config: InferenceRule(config, internal)

            # FactByDescription → needs interaction
            async def kontinue(results: list[Any]) -> gen_node:
                internal = InferenceRule_InternalToolArg(
                    thought=arg["thought"], rule=rule, rule_ref=results[0][0])
                return lambda config: InferenceRule(config, internal)

            raise RaiseInteraction([result], kontinue) # type: ignore
        return parse
    async def _refresh_me_alone(self) -> None:
        if (self.rule_ref is not None
                and not self._first_time
                and self.ml_state.initialized()):
            [self.rule_ref] = await self.ml_state.refresh_facts([self.rule_ref])
        await super()._refresh_me_alone()
    def quickview_title(self) -> str:
        if self.rule_ref is not None:
            return f"Inference Rule {self.rule_ref.name()}"
        return "Inference Rule"
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Inference Rule\n")
        print_indent(indent, file)
        if self.rule_ref is not None:
            file.write("rule:\n")
            self.rule_ref.print(indent+1, file)
        else:
            file.write("rule: default\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
        if len(self.sub_nodes) <= 1:
            s0 = self._state_after_beginning()
            if s0.prooftree is not None:
                goal = s0.prooftree.top_goal()
                print_indent(indent, file)
                file.write("derived goal:\n")
                print_goal(goal, indent+1, False, file, self._ctxt_before_me())
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason':
        if isinstance(self.rule_ref, IsabelleFact_Unfound):
            return FailureReason(f"Inference rule fact \"{self.rule_ref.name()}\" not found")
        return Minilang_Operation.RULE(self.rule_ref)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to apply the inference rule.{"".join(["\n"+e for e in err.errors])}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def has_ending_opr(self) -> bool:
        return False
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("An InferenceRule doesn't have an ending operation")
    def ending_opr(self) -> Minilang_Operation | None:
        return None
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, indent-1)
        else:
            return ("derived subgoals", indent+1)

### Branch

class Branch_Case_ToolArg(TypedDict):
    statement: NamedStatement
    proof: SubProof
class Branch_ToolArg(TypedDict):
    thought: str
    cases: list[Branch_Case_ToolArg]
#class Branch_ToolArg(TypedDict):
#    thought: str
#    cases: list[NamedStatement]

@proof_operation("Branch", Branch_ToolArg)
class Branch(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, arg: Branch_ToolArg,
                 parsed_cases: list[SubProof_parsed] | None = None):
        super().__init__(config, arg["thought"], [])
        self.cases = arg["cases"]
        self._parsed_cases = parsed_cases or [None] * len(arg["cases"])
        self._initial_goal_index = 0
    @staticmethod
    def gen(arg : Branch_ToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: Branch(config, arg))
    @staticmethod
    def interactive_gen(arg : Branch_ToolArg) -> parsing_node:
        async def parse(alive_state: Minilang_State | None,
                        exact_state: Minilang_State | None = None) -> gen_node:
            parsed_cases = []
            for case in arg["cases"]:
                parsed = await _parse_subproof(case["proof"], alive_state)
                parsed_cases.append(parsed)
            return lambda config: Branch(config, arg, parsed_cases=parsed_cases)
        return parse
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ('cases', indent+1)
    def _print_header(self, indent: int, file: MyIO, show_warnings: bool = False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Branch\n")
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def _new_goal_node(self, goal_index: int, ml_state: Minilang_State) -> GoalNode:
        case_index = goal_index - 1  # goal 0 = exhaustiveness, goals 1..N = cases
        if 0 <= case_index < len(self._parsed_cases):
            auto_proof = self._parsed_cases[case_index]
        else:
            auto_proof = None
        return GoalNode(NodeConfig(str(goal_index+self._initial_goal_index), ml_state, self), False, True,
                        auto_proof=auto_proof)
    def beginning_opr(self) -> 'Minilang_Operation | FailureReason':
        if not self.cases:
            return FailureReason("Must specify at least one branching case.")
        return Minilang_Operation.BRANCH([(case["statement"].get("name"), case["statement"]["isabelle"]) for case in self.cases])
    def ending_opr(self):
        return None
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Fail to anlysis the proof goal by cases because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Branch doesn't have an ending operation")
    async def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> 'FailureReason | None':
        fail = await super()._refresh_the_beginning_opr(begin_opr)
        if fail is None:
            if not self.sub_nodes[0].thought:
                self.sub_nodes[0].thought = "We first show exhaustiveness of the case split"
        return fail

### CaseSplit

class CaseSplit_ToolArg(TypedDict):
    thought: str
    target_isabelle_term: str
    proof: SubProof

@proof_operation("CaseSplit", CaseSplit_ToolArg)
class CaseSplit(CaseSplit_Like):
    def __init__(self, config: NodeConfig, arg: CaseSplit_ToolArg,
                 subproof_parsed: SubProof_parsed = None):
        super().__init__(config, arg["thought"], [], _initial_proof=subproof_parsed)
        self.target_isabelle_term = arg["target_isabelle_term"]
    def quickview_title(self) -> str:
        return f"CaseSplit {self.target_isabelle_term}"
    @staticmethod
    def gen(arg : CaseSplit_ToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: CaseSplit(config, arg))
    @staticmethod
    def interactive_gen(arg : CaseSplit_ToolArg) -> parsing_node:
        return _gen_with_subproof(CaseSplit,
            lambda config, parsed: CaseSplit(config, arg, subproof_parsed=parsed),
            arg["proof"])
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ('cases', indent+1)
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
            None)
    def ending_opr(self):
        return None
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Case analysis failed because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Branch doesn't have an ending operation")

### Induction

type Induction_Rule = str | dict[str, Any]
class Induction_ToolArg_Variable(TypedDict):
    name: str
    status: Literal["fixed", "generalized"]
class Induction_ToolArg(TypedDict):
    thought: str
    target_isabelle_term: str
    rule: NotRequired[Induction_Rule]  # default: 'default'
    variables: list[Induction_ToolArg_Variable]
    proof: SubProof

@proof_operation("Induction", Induction_ToolArg)
class Induction(CaseSplit_Like):
    # TODO: processing the rule
    def __init__(self, config: NodeConfig, arg: Induction_ToolArg,
                 subproof_parsed: SubProof_parsed = None):
        super().__init__(config, arg["thought"], [], _initial_proof=subproof_parsed)
        self.arg = arg
        self.target_isabelle_term = arg["target_isabelle_term"]
        self.rule = arg.get("rule", "default")
        self.variables = arg["variables"]
    def quickview_title(self) -> str:
        return f"Induction {self.target_isabelle_term}"
    @staticmethod
    def gen(arg : Induction_ToolArg) -> parsing_node:
        return _trivial_parsing(lambda config: Induction(config, arg))
    @staticmethod
    def interactive_gen(arg : Induction_ToolArg) -> parsing_node:
        return _gen_with_subproof(Induction,
            lambda config, parsed: Induction(config, arg, subproof_parsed=parsed),
            arg["proof"])
    async def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> 'FailureReason | None':
        is_init = self._first_time
        old_variables = list(self.variables)
        if self._first_time:
            try:
                _, frees, _ = await self.ml_state.check_term(self.target_isabelle_term)
            except InternalError_UnparsedTerm as e:
                return FailureReason(
                    f"Syntax error in induction target `{e.term}`: {e.reason}")
            # Remove free variables appearing in target_isabelle_term from variables list
            self.variables[:] = [var for var in self.variables if var["name"] not in frees]
        fail = await super()._refresh_the_beginning_opr(begin_opr)
        if fail is None:
            vars = self._all_fixed_vars_before_me({})
            _, frees, _ = await self.ml_state.check_term(self.target_isabelle_term)
            # Remove free variables appearing in target_isabelle_term from vars
            for v in frees:
                if v in vars:
                    del vars[v]
            new_var_names = [v for v in vars if v not in [var["name"] for var in self.variables]]
            if new_var_names:
                if self._first_time:
                    return FailureReason(
                        f"The {titled_string_of_and_list(new_var_names, 'variable', 'variables')} "
                        f"appear in the induction context but are not classified in the 'variables' argument. "
                        f"You should indicate whether each is 'arbitrary' (generalized during induction) or "
                        f"'fixed' (held constant).")
                else:
                    msg = (
                        f"The {titled_string_of_and_list(new_var_names, 'variable', 'variables')} are not classified "
                        "as fixed or generalized; fixed is assumed. "
                        "Change this by calling the `edit` tool with action `amend` and target step `{self.id}`"
                    )
                    self.warnings.append(Warning(Warning.Position.HEADER, msg))
            not_used_vars = [var["name"] for var in self.variables if var["name"] not in vars]
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
                self.variables.extend({"name": v, "status": "fixed"} for v in new_var_names)
        if not is_init and self.variables != old_variables:
            self.changed = True
        return fail
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ('cases', indent+1)
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
        super()._print_header(indent, file)
        self._print_evaluation_status(indent, file)
        if show_warnings: self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.INDUCT(
            self.target_isabelle_term,
            cast(list[varname_spec] | None, self._case_vars_of_child(0)),
            [var["name"] for var in self.variables if var["status"] == "generalized"],
            None)
    def ending_opr(self):
        return None
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        return FailureReason(f"Induction failed because: {"\n".join(err.errors)}")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Branch doesn't have an ending operation")

### Top Root

class GlobalEnv(StdBlock):
    def __init__(self, config: NodeConfig):
        if not isinstance(config.parent, Root):
            raise InternalError("The parent of a GlobalEnv must be a Root")
        super().__init__(config, "", [])
        self.id="$global"
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
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return (None, indent-1)
    def _print_step_id(self, indent: int, file: MyIO, update_line: bool = False) -> int:
        if update_line:
            self.line = file.current_line()
        return indent
    def _id_of_openning_prf_to_fill(self) -> step | None:
        return None
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
    def __init__(self, context_and_ptree: tuple[Context, ML_ProofTree], connection: Connection, session: 'Session'):
        (context, ptree) = context_and_ptree
        ml_state0 = Minilang_State(connection, '$init', ptree)
        super().__init__(NodeConfig("$root", ml_state0, None), "", [])
        self.context = context
        self.session = session
        self.global_env = GlobalEnv(NodeConfig("global", Minilang_State.assign(ml_state0), self))
        self.sub_nodes.append(self.global_env)
        self.final_ml_state = Minilang_State.assign(ml_state0)
    async def _refresh_me_alone(self):
        if self._first_time:
            ml_state = await self.ml_state.skip(None)
            # Get number of goals from prooftree
            if ml_state.prooftree is None:
                raise ValueError("Root: ml_state.prooftree is None, cannot get top_goals")
            self.num_goals = len(ml_state.prooftree.top_goals())
            is_single_goal = self.num_goals == 1
            for i in range(self.num_goals):
                if is_single_goal:
                    goal_id = ""
                else:
                    goal_id = f"goal{i+1}"
                goal_node = GoalNode(NodeConfig(goal_id, ml_state, self), is_single_goal, True, None)
                goal_node.id = goal_id
                self.sub_nodes.append(goal_node)
                ml_state = await ml_state.sorry(None, None)
            #self.final_ml_state = ml_state
        await super()._refresh_me_alone()
    async def _refresh_all_children_after(self, after: 'Node | Literal["end"]', can_continue_i: bool) -> None:
        # GoalContainer blocks cross-child propagation because each subgoal is
        # independent in AoA — that's correct for changes initiated *from* a
        # GoalNode (a change inside one goal must not ripple into siblings).
        # But GlobalEnv sits before all GoalNodes and its declarations affect
        # every goal, so a change *from* GlobalEnv must propagate forward to
        # all GoalNodes. Override to allow that one direction only.
        if after is self.global_env:
            for child in self.sub_nodes[1:]:
                await child._refresh_me_alone()
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
        return None
    def has_ending_opr(self) -> bool:
        return False
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Root doesn't have a beginning operation")
    def _child_refresh_failure_err_msgs(self, child : Node) -> FailureReason:
        return FailureReason("") # This suppresses the error message printing on Root
    def _ending_opr_err_msgs(self, err : IsabelleError) -> FailureReason:
        raise InternalError("A Root doesn't have an ending operation")
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
                    file.write("proof:\n")
                    self.sub_nodes[1].quickview(indent+1, file)
                else:
                    self.sub_nodes[1].quickview(indent, file)
            case _:
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
def Parse_Node(data: ToolCall_arg) -> parsing_node:
    operation = data.get("operation")
    if operation is None:
        raise ArgumentError_MissingRequiredKeys(data, "<tool call>", ["operation"])
    meta = OPERATION_REGISTRY.get(operation)
    if meta is None:
        raise ArgumentError_UnknownProofOperation(data)
    toolarg_typed_dict, gen_func = meta
    _check_tool_arg_keys(toolarg_typed_dict, data, operation)
    return gen_func(cast(Any, data))

## Session

import contextvars

_session_var: contextvars.ContextVar['Session'] = contextvars.ContextVar('_session_var')

def the_session() -> 'Session':
    return _session_var.get()


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
        self.working_interactions: list[Working_Interactions] = []
        self.warnings: list[str] = []
        self.total_cost_usd: float = 0.0
        self.total_input_tokens: int = 0
        self.total_output_tokens: int = 0
        self.total_cache_creation_input_tokens: int = 0
        self.total_cache_read_input_tokens: int = 0
        self.retrieval_forking_mode: ForkingMode = (
            parent.retrieval_forking_mode if parent is not None
            else retrieval_forking_mode)
        self.interactive_retrieval: InteractiveRetrievalMode = (
            parent.interactive_retrieval if parent is not None
            else interactive_retrieval)
        self.seen_entities: set[str] = (
            set(parent.seen_entities) if parent is not None else set())
        self.seen_commands: dict[IsabellePosition, str] = (
            dict(parent.seen_commands) if parent is not None else {})
        self.seen_opaque_note: bool = (
            parent.seen_opaque_note if parent is not None else False)
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

    def _internal_tool_name(self, t: tool) -> str:
        """Translate abstract tool id to driver-specific internal name."""
        raise NotImplementedError("subclass must override _internal_tool_name")

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
        await root._refresh_me_alone()

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
        """Log an AoA warning to interaction.yaml."""
        self._log(self.interaction_log_file, "AOA_WARNING",
                  lambda: [f"[AOA_WARN] {message}"], message=message)

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
                  lambda: [f"[PROOF_OP] Step {step}: {operation} - {details}"],
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
            f"cost=${self.total_cost_usd:.4f}")

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
                  lambda: [f"[PROOF_OP_ERROR] {error_message}"],
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
        """Interrupt the agent's processing immediately."""
        raise NotImplementedError("`interrupt` must be implemented by subclass")

    def refresh_YAML(self):
        """Refresh the YAML file with current proof state. Must be implemented by subclass."""
        raise NotImplementedError("`refresh_YAML` must be implemented by subclass")

    def _launch_forks(self, forking: list[tuple[int, Interaction]],
                      wi: Working_Interactions) -> None:
        """Launch forking interactions as background tasks. Must be implemented by subclass."""
        raise NotImplementedError("`_launch_forks` must be implemented by subclass")

    def on_log(self, event_type: str, data: dict[str, Any]):
        """Called on every _log invocation. Override to push logs externally."""
        pass

    def on_operation_start(self, step_id: str, operation: str, args: Any):
        """Called before a Minilang operation executes."""
        pass

    def on_operation_end(self, step_id: str, operation: str, args: Any, status: 'EvaluationStatus'):
        """Called after a Minilang operation completes (success or failure)."""
        pass


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


# ============================================================================
# Interaction Dispatch Helpers
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
) -> _Prompt | _Result:
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
