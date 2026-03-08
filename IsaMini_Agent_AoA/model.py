from time import time
from datetime import datetime
from pathlib import Path
from .helper import split_id_into_segs, cat_segs_into_id, incr_id_major, incr_id_minor, MyIO
from typing import Any, Iterable, NamedTuple, Sequence, TypedDict, Callable, cast, Type, Literal, NotRequired
from Isabelle_RPC_Host import Connection, IsabelleError
from enum import Enum
from IsaREPL import Client as IsaREPL
import logging
import yaml
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
type FactRef = str # i.e., the (full) name

class Explicit_Var(TypedDict):
    name: varname
    type: str | None

class FactByExpr(TypedDict):
    refer_by: Literal["expr"]
    english: str
    isabelle_expression: term
    for_any: list[Explicit_Var]

def print_fact_by_expr(fact: FactByExpr, indent: int, file: MyIO):
    print_indent(indent, file)
    file.write(f"- english: {fact["english"]}\n")
    print_indent(indent, file)
    file.write(f"  isabelle: {fact["isabelle_expression"]}\n")

class FactByName(TypedDict):
    refer_by: Literal["name"]
    name: str

def print_fact_by_name(fact: FactByName, indent: int, file: MyIO):
    print_indent(indent, file)
    file.write(f"- {fact["name"]}\n")

type Fact = FactByExpr | FactByName

def print_fact(fact: Fact, indent: int, file: MyIO):
    if fact["refer_by"] == "name":
        print_fact_by_name(cast(FactByName, fact), indent, file)
    else:
        print_fact_by_expr(cast(FactByExpr, fact), indent, file)


class Context(NamedTuple):
    vars: Vars
    hyps: Hyps

    @classmethod
    def unpack(cls, data) -> 'Context':
        (vars, hyps) = data
        vars = {IsaREPL.pretty_unicode(k): IsaREPL.pretty_unicode(v) for k, v in vars.items()}
        hyps = {IsaREPL.pretty_unicode(k): IsaREPL.pretty_unicode(v) for k, v in hyps.items()}
        return cls(vars, hyps)
    def __str__(self) -> str:
        return f"{self.vars}, {self.hyps}"

class Goal(NamedTuple):
    context: Context
    conclusion: term

    @classmethod
    def unpack(cls, data) -> 'Goal':
        (context, conclusion) = data
        conclusion = IsaREPL.pretty_unicode(conclusion)
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

def print_paragraph(indent: int, file: MyIO, para: str):
    lines = para.strip().split("\n")
    match lines:
        case [line]:
            file.write(" ")
            file.write(f"{line}\n")
        case lines:
            file.write(" |\n")
            for line in lines:
                print_indent(indent+1, file)
                file.write(line)
                file.write("\n")

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

def print_hyps(hyps: Iterable[tuple[str, term]], indent: int, file, suppressed: Hyps, banner='premises'):
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

def print_pending_goal(goal: Goal, step: step, indent: int, file : MyIO, suppressed: Context):
    print_indent(indent, file)
    file.write(f"Error: Unfinished Proof! Call command `edit` with action `fill` and target step `{step}`"
        " to provide the proof for the following goal.\n")
    print_indent(indent, file)
    file.write("pending proof goal:\n")
    print_goal(goal, indent+1, False, file, suppressed)

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
type failure_reason = str | None
        # None means internal error
        # "" means to suppress the error message printing

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
class CannotInsert_EvaluationFailed(CannotInsert):
    def __init__(self, insert_into: 'Node', reason : failure_reason):
        reason_str = "Proof operation failed."
        if reason is not None:
            reason_str = f"{reason_str}\n{reason}"
        super().__init__(insert_into, reason_str)

class CannotAppend(OprError):
    def __init__(self, target : 'Node', reason : failure_reason):
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

class NodeNotFound(OprError):
    def __init__(self, id: step):
        self.id = id
    def __str__(self) -> str:
        return f"Step with id {self.id} is not found"

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

class ArgumentError_RewriteNoTargets(ArgumentError):
    def __init__(self, arg: ToolCall_arg):
        super().__init__(
            arg,
            "Rewrite operation must target at least one of: the goal or some premises. " +
            "Set 'rewrite goal' to true or provide at least one premise name in 'rewrite premises'."
        )

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
    reason: failure_reason

    @staticmethod
    def success(time: timedelta, reason: failure_reason = None) -> 'EvaluationStatus':
        return EvaluationStatus(EvaluationStatus.Status.SUCCESS, time, reason)
    @staticmethod
    def failure(time: timedelta, reason: failure_reason) -> 'EvaluationStatus':
        return EvaluationStatus(EvaluationStatus.Status.FAILURE, time, reason)
EVALUATION_CACNCELLED = EvaluationStatus(EvaluationStatus.Status.CANCELLED, 0.0, None)
EVALUATION_NOT_YET = EvaluationStatus.failure(0.0, None)

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
                type=IsaREPL.pretty_unicode(v[2])
            ) for v in var_names
        ]
        fact_bindings = [
            FactBinding(
                expr=p[0],
                name=p[1],
                pretty=IsaREPL.pretty_unicode(p[2])
            ) for p in prem_names
        ]
        return (var_bindings, fact_bindings)

def unpack_message(data) -> Message:
    (kind, x) = data
    match kind:
        case 0:
            return New_Item_Msg.unpack(x)
        case 1:
            return Goals_Msg.unpack(x)
        case 2:
            return Consider_Case_Msg.unpack(x)
        case 3:
            return Intro_Bindings_Msg.unpack(x)
        case _:
            raise Exception(f"BUG bad message kind: {kind}")

### Minilang Proof Tree

class ML_ProofTree:
    def children(self) -> list['ML_ProofTree']:
        raise NotImplementedError("children must be implemented by subclass")
    def top_goal(self) -> Goal:
        raise NotImplementedError("top_goal must be implemented by subclass")
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
    def top_goals(self) -> list[Goal]:
        return [self.goal]
    def __str__(self) -> str:
        return str(self.goal)

class MLPT_Bundle(ML_ProofTree):
    def __init__(self, context : Context, subs : list[ML_ProofTree]):
        self.context = context
        self.subs = subs
    def children(self) -> list[ML_ProofTree]:
        return self.subs
    def top_goal(self) -> Goal:
        return self.subs[0].top_goal()
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

class MLPT_Block(ML_ProofTree):
    def __init__(self, sub : ML_ProofTree):
        self.sub = sub
    def children(self) -> list[ML_ProofTree]:
        return [self.sub]
    def top_goal(self) -> Goal:
        return self.sub.top_goal()
    def top_goals(self) -> list[Goal]:
        return self.sub.top_goals()
    def __str__(self) -> str:
        return f"{{{self.sub}}}"

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
    def HAVE(statement: term) -> 'Minilang_Operation':
        return Minilang_Operation("HAVE", [IsaREPL.ascii_of_unicode(statement)])
    @staticmethod
    def SUFFICES(statement: term) -> 'Minilang_Operation':
        return Minilang_Operation("SUFFICES", IsaREPL.ascii_of_unicode(statement))
    @staticmethod
    def OBTAIN(variables: list[Explicit_Var], constraints: list[term]) -> 'Minilang_Operation':
        vars = [(v["name"], IsaREPL.ascii_of_unicode(v["type"]) if "type" in v else None) for v in variables]
        return Minilang_Operation("OBTAIN", (vars, [IsaREPL.ascii_of_unicode(c) for c in constraints]))
    @staticmethod
    def RULE(rule_ref: FactRef | None) -> 'Minilang_Operation':
        return Minilang_Operation("RULE", [rule_ref] if rule_ref is not None else [])
    @staticmethod
    def HAMMER(fact_refs: list[FactRef]) -> 'Minilang_Operation':
        return Minilang_Operation("HAMMER", fact_refs)
    @staticmethod
    def INTRO(bindings: Bindings | None) -> 'Minilang_Operation':
        return Minilang_Operation("INTRO", bindings)
    @staticmethod
    def SIMPLIFY(fact_refs: list[FactRef], use_system_simps: bool, premise_names: list[str], simplify_goal: bool, bindings: tuple[list[tuple[str, str, str]], list[tuple[lambda_term, str, str]]] | None) -> 'Minilang_Operation':
        return Minilang_Operation("SIMPLIFY", (fact_refs, use_system_simps, premise_names, simplify_goal, bindings))
    @staticmethod
    def UNFOLD(consts: list[str]) -> 'Minilang_Operation':
        return Minilang_Operation("UNFOLD", consts)
    @staticmethod
    def WITNESS(terms: list[term]) -> 'Minilang_Operation':
        return Minilang_Operation("WITNESS", terms)
    @staticmethod
    def BRANCH(cases: list[term]) -> 'Minilang_Operation':
        return Minilang_Operation("BRANCH", cases)
    @staticmethod
    def CASE_SPLIT(target: term, vars: list[varname_spec] | None, rule: FactRef | None) -> 'Minilang_Operation':
        return Minilang_Operation("CASE_SPLIT", (IsaREPL.ascii_of_unicode(target), vars, rule))
    @staticmethod
    def INDUCT(target: term, vars: list[varname_spec] | None, arbitrary: list[varname], rule: FactRef | None) -> 'Minilang_Operation':
        return Minilang_Operation("INDUCT", (IsaREPL.ascii_of_unicode(target), vars, [IsaREPL.ascii_of_unicode(t) for t in arbitrary], rule))
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
    def execute(self, opr: Extended_Minilang_Operation, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        if assign_to is None:
            assign_to = Minilang_State(self.connection, type(self).assign_name(), None)
        if isinstance(opr, Minilang_Operation):
            dest_name = assign_to.name
            self.connection.write((1, (self.name, dest_name, (opr.command, opr.arg))))
            # Log proof operation
            the_session().log_proof_operation(
                step="execute",
                operation=opr.command,
                details={
                    "from_state": self.name,
                    "to_state": dest_name,
                    "operation": str(opr),
                }
            )
            try:
                (msgs, tree) = self.connection.read()
            except IsabelleError as err:
                the_session().log_proof_operation_error(
                    error_message=str(err),
                    errors=err.errors,
                    operation=str(opr)
                )
                if err.errors == ["beginning_state_not_found"]:
                    raise InternalError("The beginning state of the execution is not initialized!")
                raise
            msgs = [unpack_message(msg) for msg in msgs]
            assign_to.prooftree = unpack_MLPT(tree)
            assign_to.messages = msgs
        else:
            raise NotImplementedError("Here we should implement the execution of a list of Minilang operations")
            #msgs = opr(self, assign_to)
        return assign_to
    def sorry(self, varnames: list[varname_spec] | None, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        return self.execute(Minilang_Operation.SORRY(varnames), assign_to)
    def skip(self, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        return self.execute(Minilang_Operation.SKIP(), assign_to)
    def clone(self, assign_to: 'Minilang_State | None') -> 'Minilang_State':
        ret = self.execute(Minilang_Operation.SKIP(), assign_to)
        ret.messages = self.messages
        return ret
    def search_fact(self, dnf_criterions: list[list[Search_Criterion]]) -> FactRef:
        self.connection.write((2, (self.name, dnf_criterions)))
        fact_ref_and_props = self.connection.read()
        match fact_ref_and_props:
            case []:
                raise FactNotFound(dnf_criterions)
            case [single]:
                ref, _ = single
                return ref
            case _:
                raise NotImplementedError("Here we should list all the options and ask the LLM to choose which one does it mean")
    def fetch_rule_fact(self, rule: Fact) -> FactRef:
        if rule["refer_by"] == "expr":
            rule_ref = self.search_fact([
                [ Criterion_Intro(True)
                , Criterion_XPattern(True, rule["isabelle_expression"], rule["for_any"])],
                [ Criterion_Elim(True)
                , Criterion_XPattern(True, rule["isabelle_expression"], rule["for_any"])]
            ])
            return rule_ref
        else:
            rule_ref = self.retrieve_fact(rule["name"])
            if rule_ref is None:
                raise FactNotFound_ByName(rule["name"])
            return rule_ref
    def compute_bindings(self, var_names: list[str], fact_names: list[str]) -> Bindings:
        """
        Compute bindings for the leading proof goal by binding provided names in order.
        var_names[i] is bound to the i-th quantified variable in the goal.
        fact_names[j] is bound to the j-th premise in the goal.
        Raises IsabelleError if the lengths don't match the goal structure.
        """
        self.connection.write((3, (self.name, var_names, fact_names)))
        bindings_data = self.connection.read()
        return Intro_Bindings_Msg._unpack_bindings(bindings_data)
    def need_intro(self) -> bool:
        """
        Check if the leading proof goal needs INTRO (i.e., has quantified variables or premises).
        Returns True if the goal has quantifiers or premises that need to be introduced.
        """
        self.connection.write((4, self.name))
        result = self.connection.read()
        return result
    def retrieve_fact(self, name: str) -> str | None:
        """
        Retrieve the full name of a fact by its short name.
        Uses Facts.intern to get the complete fact reference.
        Returns the full name if the fact exists, None otherwise.
        """
        self.connection.write((5, (self.name, name)))
        result = self.connection.read()
        return result
    def check_term(self, term_str: str) -> tuple[typ, Vars, Vars]:
        """
        Parse and check a term string using Syntax.read_term.
        Returns a tuple of (term_type, frees, vars) where:
        - term_type: pretty-printed type of the term
        - frees: dict of {name: type} for free variables
        - vars: dict of {name: type} for schematic variables (names formatted as ?name.idx)
        Raises InternalError_UnparsedTerm if parsing fails.
        """
        self.connection.write((6, (self.name, term_str)))
        try:
            term_type, frees_list, vars_list = self.connection.read()
            frees = dict(frees_list)
            vars = dict(vars_list)
            return (term_type, frees, vars)
        except IsabelleError as e:
            if len(e.errors) >= 2 and e.errors[0] == "Unparsed":
                raise InternalError_UnparsedTerm(term_str, e.errors[1])
            else:
                raise

    def schematic_variables_of(self) -> Vars:
        """
        Get all schematic variables from the leading proof goal.
        Returns a dict of {varname: type} where varnames are formatted as ?name.idx.
        """
        self.connection.write((7, self.name))
        try:
            vars_list = self.connection.read()
            return dict(vars_list)
        except IsabelleError as e:
            raise

### The Abstract Model

type gen_node = Callable[[NodeConfig], 'Node']
type may_gen_node = Callable[[NodeConfig], 'Node | None']
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

class Node:
    parent: 'NonLeaf_Node | None'
    id: 'step'
    line: int

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
        self.status : EvaluationStatus = EVALUATION_NOT_YET
        self.warnings : list[Warning] = []
        self._kind : str = "step"
        self.age = the_session().age
        self.line = 0
    def _reset_local_step(self, new_local_step: str) -> None:
        self.local_step = new_local_step
        if self.parent is not None and self.parent.id:
            self.id = f"{self.parent.id}.{self.local_step}"
        else:
            self.id = self.local_step
    def _print_step_id(self, indent: int, file: MyIO) -> int:
        self.line = file.current_line()
        print_indent(indent, file)
        file.write(f"- {self._kind} id: {self.id}\n")
        return indent + 1
    def print(self, indent: int, file : MyIO) -> int:
        return self._print_step_id(indent, file)
    def display_operation(self) -> str:
        return type(self).__name__
    def quickview_header(self, indent: int, file: MyIO) -> int:
        print_indent(indent, file)
        file.write(f"- {self._kind} {self.id}: {self.display_operation()}, line {self.line}\n")
        self._print_evaluation_status_quickview(indent+1, file)
        return indent + 1
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
                if reason is None:
                    raise InternalError("The reason cannot be None when the status is failure")
                print_paragraph(indent, file, reason)
            case EvaluationStatus.Status.CANCELLED:
                print_indent(indent, file)
                file.write("Error: the evaluation is cancelled due to failures in preceding nodes")
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

    def assemble(self, output: list[Minilang_Operation] | None = None) -> list[Minilang_Operation]:
        """
        Assembling all the abstract tree model into the final sequence of Minilang operations
        """
        raise NotImplementedError('`assemble` must be implemented by subclass')
    def _refresh_me_alone(self, first_time: bool) -> None:
        """
        must update self.status
        Convention: Any node must be up to date after calling any public Node method
        first_time: if True, the node is being refreshed for the first time since its creation.
        """
        self.warnings.clear()
    def refresh_all_after_me(self) -> None:
        """
        refreshing the status of all the nodes excluding and after the `self`
        """
        if self.parent is None:
            raise InternalError("Don't know how to refresh a node and all its after nodes when the node's parent is none")
        else:
            self.parent._refresh_all_children_after(self)
    def insert_before(self, gen_node: gen_node) -> None:
        if self.parent is None:
            raise InternalError("Don't know how to refresh a node and all its after nodes when the node's parent is none")
        else:
            node = self.parent._insert_before_child(self, gen_node)
            try:
                node._refresh_me_alone(True)
                if node.status.status == EvaluationStatus.Status.FAILURE:
                    raise CannotInsert_EvaluationFailed(self, node.status.reason)
            except AoA_Error:
                self.parent._remove_child(node)
                raise
            node.refresh_all_after_me()
    def append(self, gen_node: may_gen_node) -> 'Node | None':
        raise NotImplementedError("`append` must be implemented by subclass")
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
    def fill(self, id: step, gen_node: gen_node) -> 'Node':
        ids = id.split('.')
        node = self._locate_node(ids[:-1], id, 0)
        to_fill = node._id_of_openning_prf_to_fill()
        if to_fill is None:
            raise CannotFill_NodeNotFound(id)
        if to_fill != id:
            raise CannotFill_BadNode(id)
        ret = node.append(gen_node)
        if ret is None:
            raise InternalError("Don't know how to fill a node when the node's append method returns None")
        return ret
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
    def _ctxt_beofre_me(self) -> Context:
        vars = self._all_fixed_vars_before_me({})
        hyps = self._all_fixed_facts_before_me({})
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
    def rename_var(self, old_name: varname, new_name: varname) -> None:
        ret = self._rename_var(old_name, new_name)
        if ret is None:
            raise CannotRename_VariableNotFound(old_name, new_name)
        else:
            ret._refresh_me_alone(False)
            ret.refresh_all_after_me()
    def rename_fact(self, old_name: str, new_name: str) -> None:
        ret = self._rename_fact(old_name, new_name)
        if ret is None:
            raise CannotRename_FactNotFound(old_name, new_name)
        else:
            ret._refresh_me_alone(False)
            ret.refresh_all_after_me()
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
    def _append_all_open_ends(self, gen_node: may_gen_node) -> None:
        raise NotImplementedError("`_append_all_open_ends` must be implemented by subclass")

# abstract base class
class Leaf(Node):
    def __init__(self, config: NodeConfig, thought: str):
        super().__init__(config, thought)
    def the_operation(self):
        raise NotImplementedError("`the_operation` must be implemented by subclass")
    def assemble(self, output: list[Minilang_Operation] | None = None) -> list[Minilang_Operation]:
        if output is None:
            output = []
        output.append(self.the_operation())
        return output
    def _refresh_me_alone(self, first_time: bool) -> None:
        now = time()
        super()._refresh_me_alone(first_time)
        try:
            self.ml_state.execute(self.the_operation(), self.resulting_state())
            self.status = EvaluationStatus.success(time() - now)
        except IsabelleError as err:
            self.status = EvaluationStatus.failure(time() - now, ''.join(err.errors))
    def append(self, gen_node: may_gen_node) -> 'Node | None':
        raise CannotAppend(self, "It is not a goal or a proof block")
    def _append_all_open_ends(self, gen_node: may_gen_node) -> None:
        raise InternalError("Don't know how to append all open ends of this node")

# abstract base class
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
    def _refresh_all_children_after(self, after: 'Node', can_continue_i: bool = True) -> None:
        """
        refreshing the status of all the nodes excluding and after the `after`
        """
        can_continue : bool | None = None
        for child in self.sub_nodes: 
            if can_continue is None:
                if child is after:
                    can_continue = can_continue_i
            else:
                if can_continue:
                    child._refresh_me_alone(False)
                    can_continue = child.status.status == EvaluationStatus.Status.SUCCESS
                else:
                    child.status = EVALUATION_CACNCELLED
        if can_continue is None:
            raise InternalError("Cannot find the target to refresh in my children")
        elif can_continue:
            if self.parent is not None:
                self.parent._refresh_all_children_after(self, can_continue)
    def _insert_before_child(self, before: 'Node', gen_node: Callable[[NodeConfig], 'Node']) -> 'Node':
        """
        invalidates the status of all nodes including and after the `before`
        """
        for i, child in enumerate(self.sub_nodes):
            if child is before:
                if i == 0:
                    segs = split_id_into_segs(child.local_step)
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
                node = gen_node(NodeConfig(new_id, child.ml_state.clone(None), self))
                for x in self.sub_nodes:
                    if x is node:
                        raise InternalError("The target node to insert is already in my children")
                self.sub_nodes.insert(i, node)
                return node
        raise InternalError("Cannot find the target to insert-before in my children")
    def _remove_child(self, child: Node) -> None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                self.sub_nodes.pop(i)
                return
        raise InternalError("The target node is not my children")
    def _resulting_state_of_all_children(self):
        raise NotImplementedError("`_resulting_state_of_all_children` must be implemented by sub-classes")
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
    def quickview(self, indent: int, file: MyIO) -> int:
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



# abstract base class
class StdBlock(NonLeaf_Node):
    def __init__(self, config: NodeConfig, thought: str, sub_nodes: list['Node']):
        super().__init__(config, thought, sub_nodes)
        # Convention: the _state_before_ending_ should be used only when self.has_ending_opr()
        self._state_before_ending_ = Minilang_State.assign(config.ml_state)
        self._body_subnodes_succeeded = False
        self._allow_multi_goal = False
    def beginning_opr(self) -> Minilang_Operation | None:
        raise NotImplementedError("`beginning_opr` must be implemented by subclass")
    def ending_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.END()
    def has_ending_opr(self) -> bool:
        return self.ending_opr() is not None
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise NotImplementedError("`_beginning_opr_err_msgs` must be implemented by subclass")
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        raise NotImplementedError("`_child_refresh_failure_err_msgs` must be implemented by subclass")
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise NotImplementedError("`_ending_opr_err_msgs` must be implemented by subclass")
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
    def _state_after_beginning(self) -> Minilang_State:
        if self.sub_nodes:
            return self.sub_nodes[0].ml_state
        else:
            return self._state_before_ending_
    def assemble(self, output: list[Minilang_Operation] | None = None) -> list[Minilang_Operation]: 
        if output is None:
            output = []
        opr = self.beginning_opr()
        if opr is not None:
            output.append(opr)
        for child in self.sub_nodes:
            child.assemble(output)
        opr = self.ending_opr()
        if opr is not None:
            output.append(opr)
        return output

    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation, first_time: bool) -> tuple[bool, failure_reason]:
        try:
            self.ml_state.execute(begin_opr, self._state_after_beginning())
            return (True, None)
        except IsabelleError as err:
            return (False, self._beginning_opr_err_msgs(err))
    def _refresh_me_alone(self, first_time: bool):
        super()._refresh_me_alone(first_time)
        begin_opr = self.beginning_opr()
        now = time()
        reason : failure_reason = None
        head_succeeded = True
        can_continue : bool = True
        if begin_opr is not None:
            ret, reason = self._refresh_the_beginning_opr(begin_opr, first_time)
            if not ret:
                head_succeeded = False
                can_continue = False
        for child in self.sub_nodes:
            if can_continue:
                child._refresh_me_alone(first_time)
                can_continue = child.status.status == EvaluationStatus.Status.SUCCESS
                if not can_continue:
                    reason = self._child_refresh_failure_err_msgs(child)
            else:
                child.status = EVALUATION_CACNCELLED
        if not self.sub_nodes and begin_opr is None:
            self.ml_state.clone(self._state_before_ending_)
        if can_continue:
            ending_opr = self.ending_opr()
            if ending_opr is None:
                self._state_before_ending_.clone(self.resulting_state())
            else:
                try:
                    self._state_before_ending_.execute(ending_opr, self.resulting_state())
                except IsabelleError as err:
                    reason = self._ending_opr_err_msgs(err)
                    can_continue = False
        if can_continue:
            self._body_subnodes_succeeded = True
            self.status = EvaluationStatus.success(time() - now)
        elif head_succeeded:
            self._body_subnodes_succeeded = False
            self._state_after_beginning().sorry(None, self.resulting_state())
            self.status = EvaluationStatus.success(time() - now, reason)
        else:
            self._body_subnodes_succeeded = False
            self.status = EvaluationStatus.failure(time() - now, reason)
    def _ctxt_of_filling(self) -> Context:
        vars = self._all_fixed_vars_before_me({})
        hyps = self._all_fixed_facts_before_me({})
        self._fixed_vars_at_me(vars)
        self._fixed_facts_at_me(hyps)
        for child in self.sub_nodes:
            child._fixed_vars_after_me(vars)
            child._fixed_facts_after_me(hyps)
        return Context(vars, hyps)
    def _print_header(self, indent: int, file: MyIO) -> None:
        raise NotImplementedError("`_print_header` must be implemented by subclass")
    def _print_footer(self, indent: int, file: MyIO) -> None:
        self._print_warnings(indent, file, [Warning.Position.FOOTER])
        if self.opening():
            ptree = self._state_before_ending_.prooftree
            if ptree is None:
                raise InternalError("The state before ending is not initialized, meaning the node is not refreshed, "
                "meaning the convention that all nodes should be freshed is broken.")
            goals = ptree.top_goals()
            match goals:
                case []:
                    pass
                case [goal]:
                    to_fill = self._id_of_openning_prf_to_fill()
                    if to_fill is not None:
                        print_pending_goal(goal, to_fill, indent, file, self._ctxt_of_filling())
                case _:
                    to_fill = self._id_of_openning_prf_to_fill()
                    if to_fill is not None:
                        if self._allow_multi_goal:
                            goal = goals[0]
                            print_pending_goal(goal, to_fill, indent, file, self._ctxt_of_filling())
                        else:
                            raise InternalError("The open goals of StdBlock should not exceed one. "
                            "To express multiple goals, you should use a StdBlock whose children are GoalNodes. See Rule as an example.")
    def is_proof_finished(self) -> bool:
        unfinished_nodes = set()
        self.unfinished_nodes(unfinished_nodes)
        return len(unfinished_nodes) == 0
    def unfinished_nodes(self, ret: set['Node']) -> None:
        super().unfinished_nodes(ret)
        if self.opening():
            ptree = self._state_before_ending_.prooftree
            if ptree is None:
                raise InternalError("The state before ending is not initialized, meaning the node is not refreshed, "
                "meaning the convention that all nodes should be freshed is broken.")
            if ptree.top_goals():
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
    def print(self, indent: int, file: MyIO):
        indent = super().print(indent, file)
        self._print_header(indent, file)
        title, child_indent = self._title_of_children(indent)
        if title is None:
            for step in self.sub_nodes:
                step.print(child_indent, file)
        else:
            if self.sub_nodes:
                print_indent(indent, file)
                file.write(title)
                file.write(":\n")
                for step in self.sub_nodes:
                    step.print(child_indent, file)
            else:
                print_indent(indent, file)
                file.write(title)
                file.write(": empty\n")
        self._print_footer(indent, file)
        return indent
    def quickview(self, indent: int, file: MyIO) -> int:
        indent = super().quickview(indent, file)
        if self.opening():
            ptree = self._state_before_ending_.prooftree
            if ptree is None:
                raise InternalError("The state before ending is not initialized, meaning the node is not refreshed, "
                "meaning the convention that all nodes should be freshed is broken.")
            if ptree.top_goals() and self._id_of_openning_prf_to_fill() is not None:
                print_indent(indent, file)
                file.write("Error: Unfinished Proof\n")
        return indent
    def print_string(self, indent: int) -> str:
        buffer = StringIO()
        self.print(indent, MyIO(buffer))
        return buffer.getvalue()
    def quickview_string(self, indent: int) -> str:
        buffer = StringIO()
        self.quickview(indent, MyIO(buffer))
        return buffer.getvalue()
    def append(self, gen_node: may_gen_node) -> 'Node | None':
        if not self.opening():
            raise CannotAppend_BlockClosed(self, self._closed_by)
        local_step = self._local_step_of_next_proof_step()
        ml_state = self._state_before_ending_.clone(None)
        config = NodeConfig(local_step, ml_state, self)
        node = gen_node(config)
        if node is None:
            return None
        self.sub_nodes.append(node)
        try:
            node._refresh_me_alone(True)
            if node.status.status == EvaluationStatus.Status.FAILURE:
                raise CannotAppend(node, node.status.reason)
        except AoA_Error:
            self.sub_nodes.pop()
            raise
        if self.opening():
            def my_gen_node(config: NodeConfig) -> Node | None:
                if config.ml_state.need_intro():
                    return Intro(config, "", None)
                else:
                    return None
            ml_state = node.resulting_state()
            if ml_state.need_intro():
                self.append(my_gen_node)
        return node


#abstract base class
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
    def _refresh_all_children_after(self, after: 'Node', can_continue_i: bool = True) -> None:
        # Each subgoal in AoA is independent, so we don't need to refresh the children after the current node.
        return None

class GoalNode(StdBlock):
    """
    GoalNode is a container that stores the proofs of a single goal.
    When executing a Node produces multiple subgoals, each child of that Node
    is a GoalNode corresponding to one of the subgoals, and the children of each
    GoalNode are the proof steps for its corresponding subgoal.
    """
    case_vars: list[Var] | None
    case_hyps: list[Hyp] | None

    def __init__(self, config: NodeConfig, is_single_goal: bool, show_goal: bool):
        # """
        # goal_index: starting from 0
        # """
        # if single_mode:
        #     id = f"$goal"
        # else:
        #     id = f"proof of goal{goal_index}"
        super().__init__(config, "", [])
        # self.id = id
        self.is_single_goal = is_single_goal
        self.show_goal = show_goal
        self._allow_multi_goal = True
        self._kind = "goal"
        self.case_vars = None
        self.case_hyps = None
        # self.goal_index = goal_index
    def goal(self) -> Goal:
        ptree = self.ml_state.prooftree
        if ptree is None:
            raise InternalError("The prooftree of the state is not initialized, meaning the node is not refreshed")
        return ptree.top_goal()
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
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A GoalNode doesn't have a beginning operation")
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return "Fail to prove the goal because one of the following proof steps fails."
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        if self.sub_nodes:
            return "The goal is nontrivial. Detailed proofs are required to prove it."
        else:
            return "Each of the following proof steps above is valid, but the goal doesn't trivially follow from these steps. Please provide more detailed proof steps."
    def _print_header(self, indent: int, file: MyIO):
        self._print_thought(indent, file)
        if self.show_goal:
            goal = self.goal()
            if self.case_vars or self.case_hyps:
                merged_vars = {v[0]: v[1] for v in (self.case_vars or [])} | goal.context.vars
                merged_hyps = {h[0]: h[1] for h in (self.case_hyps or [])} | goal.context.hyps
                goal = Goal(Context(merged_vars, merged_hyps), goal.conclusion)
            print_goal(goal, indent, True, file, self._ctxt_beofre_me())
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])
    def _print_step_id(self, indent: int, file: MyIO) -> int:
        if self.is_single_goal:
            return indent
        else:
            return super()._print_step_id(indent, file)
    def _refresh_me_alone(self, first_time: bool):
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
        if first_time and not self.sub_nodes and self.ml_state.need_intro():
            local_step = self._local_step_of_next_proof_step()
            ml_state = self.ml_state.clone(None)
            config = NodeConfig(local_step, ml_state, self)
            intro = Intro(config, "", None)
            self.sub_nodes.append(intro)
        return super()._refresh_me_alone(first_time)
    def _fixed_vars_at_me(self, ret: Vars) -> Vars:
        goal = self.goal()
        ret.update(goal.context.vars)
        return ret
    def _fixed_facts_at_me(self, ret: Hyps) -> Hyps:
        goal = self.goal()
        ret.update(goal.context.hyps)
        return ret
    def quickview_header(self, indent: int, file: MyIO) -> int:
        if self.is_single_goal:
            return indent
        else:
            print_indent(indent, file)
            file.write(f"- {self._kind} {self.id}, line {self.line}\n")
            return indent + 1

#abstract base class
class SubgoalMaker(GoalContainer, StdBlock):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._initial_goal_index : int = 1
    def beginning_opr(self) -> Minilang_Operation:
        raise NotImplementedError("`beginning_opr` must be implemented by subclass")
    def has_ending_opr(self) -> bool:
        return True
    def _case_vars_of_child(self, child_ind: int) -> list[varname_spec] | None:
        return None
    def _new_goal_node(self, goal_index: int, ml_state: Minilang_State) -> GoalNode:
        return GoalNode(NodeConfig(str(goal_index+self._initial_goal_index), ml_state, self), False, True)
    def _on_regenerating_goals(self, goals: list[Goal]) -> None:
        pass
    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation, first_time: bool) -> tuple[bool, failure_reason]:
        (success, reason) = super()._refresh_the_beginning_opr(begin_opr, first_time)
        if success:
            s0 = self._state_after_beginning()
            if s0.prooftree is None:
                raise InternalError("The prooftree of the state after beginning is not initialized, meaning the node is not refreshed")
            goals = s0.prooftree.top_goals()
            # TODO: try to reuse the existing subnodes instead of discarding them.
            if not first_time and len(goals) == len(self.sub_nodes):
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
                    ml_state = s0.clone(None)
                    for i in range(len(goals)):
                        new_node = self._new_goal_node(i, ml_state)
                        self.sub_nodes.append(new_node)
                        ml_state = ml_state.sorry(None, None)
            return (True, None)
        else:
            return (False, reason)
    def _id_of_openning_prf_to_fill(self) -> step | None:
        return None
    def _append_all_open_ends(self, gen_node: may_gen_node) -> None:
        for child in self.sub_nodes:
            child.append(gen_node)
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
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.case_vars = None
        self.case_hyps = None
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
    def _print_header(self, indent: int, file: MyIO) -> None:
        if self.case_vars is not None:
            print_vars(self.case_vars, indent, file, {}, "fixing variables")
        if self.case_hyps is not None:
            print_hyps(self.case_hyps, indent, file, {}, "assuming premises")
    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation, first_time: bool) -> tuple[bool, failure_reason]:
        (success, reason) = super()._refresh_the_beginning_opr(begin_opr, first_time)
        if success and not self.sub_nodes:
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
        return (success, reason)
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
    





### Concrete Models

#### Arguments of Concrete Operations

### Operation registry for tool calls

class OperationMeta(NamedTuple):
    toolarg_typed_dict: type[Any]
    gen_func: Callable[[Any], gen_node]

OPERATION_REGISTRY: dict[str, OperationMeta] = {}

def proof_operation(operation: str, toolarg_typed_dict: type[Any]):
    """
    Class decorator to register a tool operation and its ToolArg TypedDict.
    The operation name is given explicitly by `operation`, and the class must
    define a staticmethod `gen(arg: ToolArg) -> gen_node`.
    """
    def decorator(cls: type[Any]):
        OPERATION_REGISTRY[operation] = OperationMeta(toolarg_typed_dict, cls.gen)  # type: ignore[attr-defined]
        return cls
    return decorator

class Statement(TypedDict):
    english: str
    isabelle: str

def print_statement(self: Statement, indent: int, file: MyIO):
    print_indent(indent, file)
    file.write(f"- english: {self["english"]}\n")
    print_indent(indent, file)
    file.write(f"  isabelle: {self["isabelle"]}\n")

#### Obvious

class Obvious_ToolArg(TypedDict):
    thought: str
    facts: list[Fact]

@proof_operation("Obvious", Obvious_ToolArg)
class Obvious(Leaf):
    def __init__(self, config: NodeConfig, arg : Obvious_ToolArg):
        super().__init__(config, arg["thought"])
        self.facts = arg["facts"]
        self.fact_refs = [self.ml_state.fetch_rule_fact(fact) for fact in self.facts]
    @staticmethod
    def gen(arg : Obvious_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Obvious':
            return Obvious(config, arg)
        return mk
    def print(self, indent: int, file: MyIO) -> int:
        indent = super().print(indent, file)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Obvious\n")
        if self.facts:
            print_indent(indent, file)
            file.write(f"with facts:\n")
            for fact in self.facts:
                print_fact(fact, indent+1, file)
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent
    def the_operation(self) -> Minilang_Operation:
        return Minilang_Operation.HAMMER(self.fact_refs)


#### Rewrite

Rewrite_ToolArg = TypedDict('Rewrite_ToolArg', {
    'thought': str,
    'using': list[Fact],
    'use system simplifiers': bool,
    'rewrite goal': bool,
    'rewrite premises': list[str]
})

@proof_operation("Rewrite", Rewrite_ToolArg)
class Rewrite(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, arg: Rewrite_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.using = arg["using"]
        self.use_system_simplifiers = arg["use system simplifiers"]
        self.rewrite_goal = arg["rewrite goal"]
        self.rewrite_premises = arg["rewrite premises"]

        # Validate that at least one target is specified
        if not self.rewrite_goal and not self.rewrite_premises:
            raise ArgumentError_RewriteNoTargets(cast(ToolCall_arg, arg))

        self.fact_refs = [self.ml_state.fetch_rule_fact(fact) for fact in self.using]
        self.bindings: Bindings | None = None
        self.running_time = 0

    @staticmethod
    def gen(arg: Rewrite_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Rewrite':
            return Rewrite(config, arg)
        return mk

    def _print_header(self, indent: int, file: MyIO):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Rewrite\n")
        if self.using or self.use_system_simplifiers:
            print_indent(indent, file)
            file.write(f"using:\n")
            for fact in self.using:
                print_fact(fact, indent+1, file)
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
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])

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

    def beginning_opr(self) -> Minilang_Operation:
        bindings = None
        if self.bindings is not None:
            var_bindings = [(vb.internal_varname, vb.external_varname, vb.type) for vb in self.bindings[0]]
            fact_bindings = [(fb.expr, fb.name, fb.pretty) for fb in self.bindings[1]]
            bindings = (var_bindings, fact_bindings)
        return Minilang_Operation.SIMPLIFY(
            self.fact_refs,
            self.use_system_simplifiers,
            self.rewrite_premises,
            self.rewrite_goal,
            bindings
        )

    def _beginning_opr_err_msgs(self, err: IsabelleError) -> failure_reason:
        return f"Fail to rewrite because: {"\n".join(err.errors)}"

    def _child_refresh_failure_err_msgs(self, child: Node) -> failure_reason:
        return f"Subgoal {child.id} fails to be proven."

    def has_ending_opr(self) -> bool:
        return False

    def _ending_opr_err_msgs(self, err: IsabelleError) -> failure_reason:
        raise InternalError("A Rewrite doesn't have an ending operation")

    def ending_opr(self) -> Minilang_Operation | None:
        return None

    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, indent-1)
        else:
            return ("goals", indent+1)

    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation, first_time: bool) -> tuple[bool, failure_reason]:
        (success, reason) = super()._refresh_the_beginning_opr(begin_opr, first_time)
        if success:
            self.running_time += 1
            messages = self._state_after_beginning().messages
            intro_bindings_msgs = [m for m in messages if isinstance(m, Intro_Bindings_Msg)]
            match intro_bindings_msgs:
                case [intro_bindings_msg]:
                    pass
                case _:
                    raise InternalError(
                        f"Expected exactly one Intro_Bindings_Msg in Rewrite's messages, got {len(intro_bindings_msgs)}"
                    )
            self.bindings = intro_bindings_msg.final
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
        return (success, reason)

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


#### So

#### Have

class Have_ToolArg(TypedDict):
    thought: str
    statement: Statement

@proof_operation("Have", Have_ToolArg)
class Have(StdBlock):
    def __init__(self, config: NodeConfig, arg : Have_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
    @staticmethod
    def gen(arg : Have_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Have':
            return Have(config, arg)
        return mk
    def _print_header(self, indent: int, file: MyIO):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Have\n")
        print_indent(indent, file)
        file.write(f"statement:\n")
        print_indent(indent+1, file)
        file.write(f"english: {self.statement['english']}\n")
        print_indent(indent+1, file)
        file.write(f"isabelle: {self.statement['isabelle']}\n")
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.HAVE(self.statement['isabelle'])
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Fail to claim the intermediate subgoal because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return "Fail to prove this statement because one of the following proof steps fails."
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        if self.sub_nodes:
            return "Each of the following proof steps above is valid, but the target statement doesn't trivially follow from these steps. Please provide more detailed proof steps."
        else:
            return "The statement is nontrivial. Detailed proofs are required to establish this statement."

#### Suffices

class Suffices_ToolArg(TypedDict):
    thought: str
    statement: Statement

@proof_operation("Suffices", Suffices_ToolArg)
class Suffices(StdBlock):
    def __init__(self, config: NodeConfig, arg : Suffices_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
    @staticmethod
    def gen(arg : Suffices_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Suffices':
            return Suffices(config, arg)
        return mk
    def _print_header(self, indent: int, file: MyIO):
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
        self._print_warnings(indent, file, [Warning.Position.HEADER])
        if not self.sub_nodes:
            print_indent(indent, file)
            file.write(f"notice: Need to show the provided statement implies the goal\n")
    def beginning_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.SUFFICES(self.statement['isabelle'])
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Fail to apply 'it suffices to show' because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return "Fail to prove the implication (sufficient condition implies goal) because one of the following proof steps fails."
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        if self.sub_nodes:
            return "Each of the following proof steps above is valid, but the implication doesn't trivially follow from these steps. Please provide more detailed proof steps."
        else:
            return "The implication is nontrivial. Detailed proofs are required to establish that the sufficient condition implies the goal."

#### Obtain

class Obtain_ToolArg(TypedDict):
    thought: str
    variables: list[Explicit_Var]
    constraints: list[Statement]

@proof_operation("Obtain", Obtain_ToolArg)
class Obtain(StdBlock):
    def __init__(self, config: NodeConfig, arg : Obtain_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.variables = arg["variables"]
        self.constraints = arg["constraints"]
    @staticmethod
    def gen(arg : Obtain_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Obtain':
            return Obtain(config, arg)
        return mk
    def _print_header(self, indent: int, file: MyIO):
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
                print_indent(indent+1, file)
                file.write(f"english: {constraint['english']}\n")
                print_indent(indent+1, file)
                file.write(f"isabelle: {constraint['isabelle']}\n")
            case _:
                print_indent(indent, file)
                file.write(f"constraints:\n")
                for constraint in self.constraints:
                    print_indent(indent+1, file)
                    file.write(f"- english: {constraint['english']}\n")
                    print_indent(indent+1, file)
                    file.write(f"  isabelle: {constraint['isabelle']}\n")
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.OBTAIN(self.variables, [c["isabelle"] for c in self.constraints])
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Fail to claim the existential subgoal because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return "Fail to prove the existence of such variables because one of the following proof steps fails."
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        if self.sub_nodes:
            return "The statement is nontrivial. Detailed proofs are required to establish this statement."
        else:
            return "Each of the following proof steps above is valid, but the target statement doesn't trivially follow from these steps. Please provide more detailed proof steps."

#### INTRO

class Intro_ToolArg(TypedDict):
    thought: str
    variable_bindings: list[varname]
    fact_bindings: list[varname]

@proof_operation("Intro", Intro_ToolArg)
class Intro(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, thought: str, bindings: Bindings | None):
        super().__init__(config, thought, [])
        self.bindings = bindings
        self.running_time = 0
    @staticmethod
    def gen(arg: Intro_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Intro':
            bindings = config.ml_state.compute_bindings(arg["variable_bindings"], arg["fact_bindings"])
            return Intro(config, arg["thought"], bindings)
        return mk
    def _print_header(self, indent: int, file: MyIO):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Intro\n")
        if self.bindings is not None:
            print_var_bindings(self.bindings[0], indent, file, "fixing variables")
            print_fact_bindings(self.bindings[1], indent, file, "assuming premises")
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.INTRO(self.bindings)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Fail to introduce the variables and premises because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return f"Subgoal {child.id} fails to be proven."
    def has_ending_opr(self) -> bool:
        return False
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("An Intro doesn't have an ending operation")
    def ending_opr(self) -> Minilang_Operation | None:
        return None
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, indent-1)
        else:
            return ("goals", indent+1)
    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation, first_time: bool) -> tuple[bool, failure_reason]:
        (success, reason) = super()._refresh_the_beginning_opr(begin_opr, first_time)
        if success:
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
                                file.write(f"- {binding.external_varname}")
                            else:
                                file.write(f"- {binding.internal_varname}, renamed to {binding.external_varname} to prevent name conflicts")
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
        return (success, reason)
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
    rule: Fact | None
    # TODO: write some skills telling the agent how to associate common operations (e.g., proof by contradiction, proof by cases, etc.) with the inference rules

@proof_operation("InferenceRule", InferenceRule_ToolArg)
class InferenceRule(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, arg : InferenceRule_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.rule = arg["rule"]
        self.rule_ref = self.ml_state.fetch_rule_fact(self.rule) if self.rule is not None else None
        self._opening = False
    @staticmethod
    def gen(arg : InferenceRule_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'InferenceRule':
            return InferenceRule(config, arg)
        return mk
    def display_operation(self) -> str:
        return "Inference Rule"
    def _print_header(self, indent: int, file: MyIO):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Inference Rule\n")
        print_indent(indent, file)
        file.write(f"rule: {self.rule_ref if self.rule_ref is not None else 'default'}\n")
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])
        if len(self.sub_nodes) <= 1:
            s0 = self._state_after_beginning()
            if s0.prooftree is None:
                raise InternalError("The prooftree of the state after beginning is not initialized, meaning the node is not refreshed")
            goal = s0.prooftree.top_goal()
            print_indent(indent, file)
            file.write("derived goal:\n")
            print_goal(goal, indent+1, False, file, self._ctxt_beofre_me())
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.RULE(self.rule_ref)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Fail to apply the inference rule.{"".join(["\n"+e for e in err.errors])}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return f"Subgoal {child.id} fails to be proven."
    def has_ending_opr(self) -> bool:
        return False
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("An InferenceRule doesn't have an ending operation")
    def ending_opr(self) -> Minilang_Operation | None:
        return None
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, indent-1)
        else:
            return ("derived subgoals", indent+1)

### Branch

class Branch_ToolArg(TypedDict):
    thought: str
    cases: list[Statement]

@proof_operation("Branch", Branch_ToolArg)
class Branch(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, arg: Branch_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.cases = arg["cases"]
        self._initial_goal_index = 0
    @staticmethod
    def gen(arg : Branch_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Branch':
            return Branch(config, arg)
        return mk
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ('cases', indent+1)
    def _print_header(self, indent: int, file: MyIO):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Branch\n")
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.BRANCH([case['isabelle'] for case in self.cases])
    def ending_opr(self):
        return None
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Fail to anlysis the proof goal by cases because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return f"Subgoal {child.id} fails to be proven."
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A Branch doesn't have an ending operation")
    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation, first_time: bool) -> tuple[bool, failure_reason]:
        (success, reason) = super()._refresh_the_beginning_opr(begin_opr, first_time)
        if success:
            if not self.sub_nodes[0].thought:
                self.sub_nodes[0].thought = "We first show exhaustiveness of the case split"
        return (success, reason)

### CaseSplit

class CaseSplit_ToolArg(TypedDict):
    thought: str
    target_isabelle_term: str

@proof_operation("CaseSplit", CaseSplit_ToolArg)
class CaseSplit(CaseSplit_Like):
    def __init__(self, config: NodeConfig, arg: CaseSplit_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.target_isabelle_term = arg["target_isabelle_term"]
    @staticmethod
    def gen(arg : CaseSplit_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'CaseSplit':
            return CaseSplit(config, arg)
        return mk
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ('cases', indent+1)
    def _print_header(self, indent: int, file: MyIO):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: CaseSplit\n")
        print_indent(indent, file)
        file.write(f"target term: {self.target_isabelle_term}\n")
        super()._print_header(indent, file)
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.CASE_SPLIT(
            self.target_isabelle_term,
            cast(list[varname_spec] | None, self._case_vars_of_child(0)),
            None)
    def ending_opr(self):
        return None
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Case analysis failed because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return f"Subgoal {child.id} fails to be proven."
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
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

class Induction_ArgumentError_MissingVars(ArgumentError):
    def __init__(self, arg: Induction_ToolArg, missing: list[varname]):
        msg = (
            "In the argument `variables`, you should additionally indicate whether the "
            f"{titled_string_of_and_list(missing, 'variable', 'variables')} is fixed or generalized."
        )
        super().__init__(cast(ToolCall_arg, arg), msg)
        self.missing = missing

@proof_operation("Induction", Induction_ToolArg)
class Induction(CaseSplit_Like):
    # TODO: processing the rule
    def __init__(self, config: NodeConfig, arg: Induction_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.arg = arg
        self.target_isabelle_term = arg["target_isabelle_term"]
        self.rule = arg.get("rule", "default")
        self.variables = arg["variables"]
    @staticmethod
    def gen(arg : Induction_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Induction':
            return Induction(config, arg)
        return mk
    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation, first_time: bool) -> tuple[bool, failure_reason]:
        if first_time:
            try:
                _, frees, _ = self.ml_state.check_term(self.target_isabelle_term)
            except InternalError_UnparsedTerm as e:
                raise ArgumentError_UnparsedTerm.from_internal_error(cast(ToolCall_arg, self.arg), e)
            # Remove free variables appearing in target_isabelle_term from variables list
            self.variables[:] = [var for var in self.variables if var["name"] not in frees]
        success, reason = super()._refresh_the_beginning_opr(begin_opr, first_time)
        if success:
            vars = self._all_fixed_vars_before_me({})
            _, frees, _ = self.ml_state.check_term(self.target_isabelle_term)
            # Remove free variables appearing in target_isabelle_term from vars
            for v in frees:
                if v in vars:
                    del vars[v]
            new_var_names = [v for v in vars if v not in [var["name"] for var in self.variables]]
            if new_var_names:
                if first_time:
                    raise Induction_ArgumentError_MissingVars(self.arg, new_var_names)
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
        return success, reason
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return ('cases', indent+1)
    def _print_header(self, indent: int, file: MyIO):
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
        self._print_warnings(indent, file, [Warning.Position.HEADER])
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.INDUCT(
            self.target_isabelle_term,
            cast(list[varname_spec] | None, self._case_vars_of_child(0)),
            [var["name"] for var in self.variables if var["status"] == "generalized"],
            None)
    def ending_opr(self):
        return None
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Induction failed because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return f"Subgoal {child.id} fails to be proven."
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A Branch doesn't have an ending operation")

### Top Root

class GlobalEnv(StdBlock):
    def __init__(self, config: NodeConfig):
        if not isinstance(config.parent, Root):
            raise InternalError("The parent of a GlobalEnv must be a Root")
        super().__init__(config, "", [])
        self.id="$global"
    def beginning_opr(self) -> None:
        return None
    def ending_opr(self) -> Minilang_Operation | None:
        return None
    def has_ending_opr(self) -> bool:
        return False
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A GlobalEnv doesn't have a beginning operation")
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return "" # This suppresses the error message printing on GlobalEnv
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("Internal Bug: Failed to apply INTRO on the proof goal")
    def _print_header(self, indent: int, file: MyIO):
        pass
    def _title_of_children(self, indent: int) -> tuple[str | None, int]:
        return (None, indent-1)
    def _print_step_id(self, indent: int, file: MyIO) -> int:
        return indent
    def _id_of_openning_prf_to_fill(self) -> step | None:
        return None
    def _print_footer(self, indent: int, file: MyIO) -> None:
        print_indent(indent, file)
        file.write(f"You could add global declarations by calling command `edit` with action `fill` and target step `{self.id}.{len(self.sub_nodes)+1}`\n")
    def unfinished_nodes(self, ret: set['Node']) -> None:
        for child in self.sub_nodes:
            child.unfinished_nodes(ret)

class Root(GoalContainer, StdBlock):
    def __init__(self, context_and_ptree: tuple[Context, ML_ProofTree], connection: Connection):
        (context, ptree) = context_and_ptree
        self.context = context
        ml_state0 = Minilang_State(connection, '$init', ptree)
        super().__init__(NodeConfig("$root", ml_state0, None), "", [])
        self.global_env = GlobalEnv(NodeConfig("global", ml_state0, self))
        self.sub_nodes.append(self.global_env)
        ml_state = ml_state0.skip(None)
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
            goal_node = GoalNode(NodeConfig(goal_id, ml_state, self), is_single_goal, True)
            goal_node.id = goal_id
            self.sub_nodes.append(goal_node)
            ml_state = ml_state.sorry(None, None)
        self.final_ml_state = ml_state
        self._refresh_me_alone(True)
    def resulting_state(self) -> Minilang_State:
        return self.final_ml_state
    def _print_step_id(self, indent: int, file: MyIO) -> int:
        return indent
    def beginning_opr(self) -> Minilang_Operation | None:
        return None
    def ending_opr(self) -> Minilang_Operation | None:
        return None
    def has_ending_opr(self) -> bool:
        return False
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A Root doesn't have a beginning operation")
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return "" # This suppresses the error message printing on Root
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A Root doesn't have an ending operation")
    def print(self, indent: int, file: MyIO) -> int:
        print_vars(self.context.vars.items(), indent, file, {})
        print_hyps(self.context.hyps.items(), indent, file, {})
        self._print_evaluation_status(indent, file)
        self._print_warnings(indent, file, [Warning.Position.HEADER])
        self.sub_nodes[0].print(indent, file)
        match self.num_goals:
            case 1:
                self.sub_nodes[1].print(indent, file)
            case _:
                file.write("proof goals:\n")
                for i in range(self.num_goals):
                    print_indent(indent+1, file)
                    file.write(f"- goal index: {i+1}\n")
                    self.sub_nodes[i+1].print(indent+2, file)
        self._print_warnings(indent, file, [Warning.Position.FOOTER])
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
                    print_indent(indent+1, file)
                    file.write(f"- goal index: {i+1}\n")
                    self.sub_nodes[i+1].quickview(indent+2, file)
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
def Parse_Node(data: ToolCall_arg) -> gen_node:
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

import threading, tempfile, os

class LocalSession(threading.local):
    session: 'Session'
_local_store = LocalSession()

def the_session() -> 'Session':
    return _local_store.session


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
    Driver: dict[str, Type['Session']] = {}

    def __init__(self, logger: logging.Logger | None = None, log_dir: str | Path = ""):
        # if hasattr(_local_store, 'session'):
        #     raise InternalError("The session has already been set in this thread.")
        _local_store.session = self
        self.age = 0
        self.logger = logger
        self.log_dir = None
        self.interaction_log_path = None
        self.proofs_log_path = None
        self.proof_oprs_log_path = None
        self.interaction_log_file = None
        self.proofs_log_file = None
        self.proof_oprs_log_file = None
        if log_dir != "":
            self._setup_log_directory(log_dir)

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

        # Open log files in append mode, keep them open
        self.interaction_log_file = open(self.interaction_log_path, 'a', encoding='utf-8')
        self.proofs_log_file = open(self.proofs_log_path, 'a', encoding='utf-8')
        self.proof_oprs_log_file = open(self.proof_oprs_log_path, 'a', encoding='utf-8')

        # Write initial session start markers
        session_start = {
            "event": "SESSION_START",
            "timestamp": datetime.now().isoformat(),
        }
        self._append_yaml(self.interaction_log_file, session_start)
        self._append_yaml(self.proofs_log_file, session_start)
        self._append_yaml(self.proof_oprs_log_file, session_start)

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

    def __enter__(self) -> 'Session':
        """Enter the runtime context for this session."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Exit the runtime context and clean up the session."""
        self.close()
        # Don't suppress exceptions
        return False

    def close(self):
        """Clean up the session and release resources."""
        # Write session end markers and close log files
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

        # Clean up the thread-local session reference
        if hasattr(_local_store, 'session') and _local_store.session is self:
            delattr(_local_store, 'session')

    def initialize(self, root: Root):
        if hasattr(self, 'root'):
            raise InternalError("The 'root' field has already been assigned.")
        self.root = root

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

    def log_proof(self):
        """
        Log the current proof tree to proof.yaml in the log directory.
        """
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

    def debug_info(self, msg: str, *args, **kwargs):
        """Legacy debug logging method. Prefer using log_error for errors."""
        if self.logger is not None:
            self.logger.debug(msg, *args, **kwargs)
    def run(self):
        raise NotImplementedError("`run` must be implemented by subclass")


def agent_driver(name : str):
    def decorator(cls : Type[Session]) -> Type[Session]:
        Session.Driver[name] = cls
        return cls
    return decorator
