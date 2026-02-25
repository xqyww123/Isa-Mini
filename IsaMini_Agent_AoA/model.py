from time import time
from .helper import split_id_into_segs, cat_segs_into_id, incr_id_major, incr_id_minor
from typing import Any, NamedTuple, Sequence, TypedDict, Callable, TextIO, cast
from Isabelle_RPC_Host import Connection, IsabelleError
from enum import Enum
from IsaREPL import Client as IsaREPL

type varname = str
type varname_spec = varname | None # underscore '_' is represented as None
type typ = str
type term = str
type step = str
type local_step = str
type Vars = dict[varname, typ]
type Hyps = dict[varname, term]
type FactRef = str # i.e., the (full) name

class Explicit_Var(TypedDict):
    name: varname
    type: str | None

class Fact(NamedTuple):
    english: str
    isabelle_expression: term
    for_any: list[Explicit_Var]

    def print(self, ident: int, file: TextIO):
        print_indent(ident, file)
        file.write(f"- english: {self.english}\n")
        print_indent(ident, file)
        file.write(f"  isabelle: {self.isabelle_expression}\n")


class Context(NamedTuple):
    vars: Vars
    hyps: Hyps

    @classmethod
    def unpack(cls, data) -> 'Context':
        (vars, hyp) = data
        vars = {IsaREPL.pretty_unicode(k): IsaREPL.pretty_unicode(v) for k, v in vars.items()}
        hyp = {}
        for k, vs in hyp.items():
            if len(vs) == 1:
                hyp[IsaREPL.pretty_unicode(k)] = IsaREPL.pretty_unicode(vs[0])
            else:
                for i, v in enumerate(vs):
                    hyp[f"{IsaREPL.pretty_unicode(k)}({i+1})"] = IsaREPL.pretty_unicode(v)
        return cls(vars, hyp)
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

def print_indent(ident: int, file):
    for _ in range(ident):
        file.write("  ")

def print_multiline_kv(ident: int, file: TextIO, key: str, val: str):
    lines = val.strip().split("\n")
    match lines:
        case [line]:
            print_indent(ident, file)
            file.write(key)
            file.write(": ")
            file.write(f"{line}\n")
        case lines:
            print_indent(ident, file)
            file.write(key)
            file.write(": |\n")
            for line in lines:
                print_indent(ident+1, file)
                file.write(line)
                file.write("\n")

def print_vars(vars: Vars, ident: int, file):
    if vars:
        print_indent(ident, file)
        file.write("variables:\n")
        for (name, type) in vars.items():
            print_indent(ident+1, file)
            file.write(f"- {name}: {type}\n")

def print_hyps(hyps: Hyps, ident: int, file):
    if hyps:
        print_indent(ident, file)
        file.write("hypotheses:\n")
        for (name, term) in hyps.items():
            print_indent(ident+1, file)
            file.write(f"- {name}: {term}\n")

def print_goal(goal: Goal, ident: int, show_header: bool, file):
    print_vars(goal.context.vars, ident, file)
    print_hyps(goal.context.hyps, ident, file)
    print_indent(ident, file)
    if goal.context.vars or goal.context.hyps:
        file.write(f"conclusion: {goal.conclusion}\n")
    else:
        if show_header:
            file.write("goal: ")
        file.write(goal.conclusion)
        file.write("\n")

def print_pending_goal(goal: Goal, step: step, ident: int, file : TextIO):
    print_indent(ident, file)
    file.write(f"Error: Unfinished Proof! Call command `edit` with action `fill` and target step `{step}`"
        " to provide the proof for the following goal.\n")
    print_indent(ident, file)
    file.write("pending proof goal:\n")
    print_goal(goal, ident+1, False, file)

## Errors
type timedelta = float # in seconds
type failure_reason = str | None
        # None means internal error
        # "" means to suppress the error message printing

def print_failure_reason(ident: int, file: TextIO, reason: failure_reason):
    if reason is None:
        raise InternalError("A failure reason is not provided")
    lines = reason.strip().split("\n")
    match lines:
        case []:
            pass
        case [line]:
            print_indent(ident, file)
            file.write("Error: ")
            file.write(f"{line}\n")
        case lines:
            print_indent(ident, file)
            file.write("Error: |\n")
            for line in lines:
                print_indent(ident+1, file)
                file.write(line)
                file.write("\n")


class OprError(Exception):
    pass
class CannotInsert_EvaluationFailedInPlace(OprError):
    def __init__(self, insert_into: 'Node', target: 'Node', reason : failure_reason):
        self.reason = reason
        self.insert_into = insert_into
        self.target = target
    def __str__(self) -> str:
        return f"Cannot insert before the node {self.insert_into.id} because {self.reason}"
class CannotAppend(OprError):
    def __init__(self, target : 'Node', reason : failure_reason):
        self.reason = reason
        self.target = target
    def __str__(self) -> str:
        return f"Cannot append on node {self.target.id} because {self.reason}"
class FactNotFound(OprError):
    def __init__(self, criterions: list[list['Search_Criterion']]):
        self.criterions = criterions
    def __str__(self) -> str:
        return f"No fact found for the following criteria: {self.criterions}"
class InternalError(OprError):
    pass
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


## Minilang Runtime

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
    def __init__(self, goals : list[Goal] | None) -> None:
        super().__init__()
        self.goals = goals
    @classmethod
    def unpack(cls, data) -> 'Goals_Msg':
        return cls([Goal.unpack(goal) for goal in data] if data is not None else None)

class Consider_Case_Msg(Message):
    def __init__(self, case: str) -> None:
        self.case = case
    @classmethod
    def unpack(cls, data) -> 'Consider_Case_Msg':
        return cls(data)

def unpack_message(data) -> Message:
    (kind, x) = data
    match kind:
        case 0:
            return New_Item_Msg.unpack(x)
        case 1:
            return Goals_Msg.unpack(x)
        case 2:
            return Consider_Case_Msg.unpack(x)
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

    @staticmethod
    def SORRY(varnames : list[varname_spec] | None):
        return Minilang_Operation("SORRY", varnames)
    @staticmethod
    def NEXT(varnames : list[varname_spec] | None):
        return Minilang_Operation("NEXT", ([], varnames))
    @staticmethod
    def END():
        return Minilang_Operation("END", [])
    @staticmethod
    def HAVE(statement: term):
        return Minilang_Operation("HAVE", [IsaREPL.ascii_of_unicode(statement)])
    @staticmethod
    def OBTAIN(variables: list[Explicit_Var], constraints: list[term]):
        vars = [(v["name"], IsaREPL.ascii_of_unicode(v["type"]) if "type" in v else None) for v in variables]
        return Minilang_Operation("OBTAIN", (vars, [IsaREPL.ascii_of_unicode(c) for c in constraints]))
    @staticmethod
    def SKIP():
        return Minilang_Operation("SKIP", None)
    @staticmethod
    def RULE(rule_ref: FactRef | None) -> 'Minilang_Operation':
        return Minilang_Operation("RULE", [rule_ref] if rule_ref is not None else [])
    @staticmethod
    def HAMMER(fact_refs: list[FactRef]) -> 'Minilang_Operation':
        return Minilang_Operation("HAMMER", fact_refs)
    @staticmethod
    def BRANCH(cases: list[term]) -> 'Minilang_Operation':
        return Minilang_Operation("BRANCH", cases)

type Extended_Minilang_Operation = Minilang_Operation | list[Minilang_Operation]

class Minilang_State:
    def __init__(self, connection: Connection, name: str, prooftree : ML_ProofTree | None):
        self.connection = connection
        self.name = name
        self.prooftree = prooftree
    def initialized(self) -> bool:
        return self.prooftree is not None
    def __str__(self) -> str:
        return f"Minilang_State({self.name})"
    def __repr__(self) -> str:
        return self.__str__()
    state_counter = 0
    @classmethod
    def assign_name(cls) -> str:
        cls.state_counter += 1
        return f"${cls.state_counter}"
    @classmethod
    def assign(cls, connection : 'Connection | Minilang_State'):
        if isinstance(connection, Minilang_State):
            connection = connection.connection
        return Minilang_State(connection, cls.assign_name(), None)
    def execute(self, opr: Extended_Minilang_Operation, assign_to: 'Minilang_State | None') -> tuple[list[Message], 'Minilang_State']:
        if assign_to is None:
            assign_to = Minilang_State(self.connection, type(self).assign_name(), None)
        if isinstance(opr, Minilang_Operation):
            dest_name = assign_to.name
            self.connection.write((1, (self.name, dest_name, (opr.command, opr.arg))))
            try:
                (msgs, tree) = self.connection.read()
            except IsabelleError as err:
                if err.errors == ["beginning_state_not_found"]:
                    raise InternalError("The beginning state of the execution is not initialized!")
                raise
            msgs = [unpack_message(msg) for msg in msgs]
            assign_to.prooftree = unpack_MLPT(tree)
        else:
            raise NotImplementedError("Here we should implement the execution of a list of Minilang operations")
            #msgs = opr(self, assign_to)
        return (msgs, assign_to)
    def sorry(self, varnames: list[varname_spec] | None, assign_to: 'Minilang_State | None') -> tuple[list[Message], 'Minilang_State']:
        return self.execute(Minilang_Operation.SORRY(varnames), assign_to)
    def skip(self, assign_to: 'Minilang_State | None') -> tuple[list[Message], 'Minilang_State']:
        return self.execute(Minilang_Operation.SKIP(), assign_to)
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
        rule_ref = self.search_fact([
            [ Criterion_Intro(True)
            , Criterion_XPattern(True, rule.isabelle_expression, rule.for_any)],
            [ Criterion_Elim(True)
            , Criterion_XPattern(True, rule.isabelle_expression, rule.for_any)]
        ])
        return rule_ref
### The Abstract Model

type gen_node = Callable[[NodeConfig], 'Node']

# abstract base class
class NodeConfig(NamedTuple):
    local_step: local_step
    ml_state: Minilang_State
    parent: 'NonLeaf_Node | None'

class Node:
    def __init__(self, config: NodeConfig, thought: str):
        """
        ml_state: the state before executing the Node. This field is mutable!!
        """
        self.local_step = config.local_step # immutable
        self.thought = thought
        self.ml_state = config.ml_state
        self.parent = config.parent
        if self.parent is not None and self.parent.id:
            self.id = f"{self.parent.id}.{self.local_step}"
        else:
            self.id : step = self.local_step
        self.status : EvaluationStatus = EVALUATION_NOT_YET
        self.messages : list[Message] = []
    @classmethod
    def new(cls, *args):
        node = cls(*args)
        node._refresh_me_alone()
        return node
    def _print_step_id(self, ident: int, file: TextIO) -> int:
        print_indent(ident, file)
        file.write(f"- step id: {self.id}\n")
        return ident + 1
    def print(self, ident: int, file : TextIO) -> int:
        return self._print_step_id(ident, file)
    def _print_thought(self, ident: int, file: TextIO) -> None:
        lines = self.thought.strip().split("\n")
        match lines:
            case []:
                pass
            case [line]:
                print_indent(ident, file)
                file.write(f"thought: {line}\n")
            case _:
                print_indent(ident, file)
                file.write(f"thought: |\n")
                for line in lines:
                    print_indent(ident+1, file)
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
    def _refresh_me_alone(self) -> None:
        """
        must update self.status
        Convention: Any node must be up to date after calling any public Node method
        Convention: any __init__ must refresh the Minilang state
        """
        raise NotImplementedError("`_refresh_me_alone` must be implemented by subclass")
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
            def my_gen_node(config: NodeConfig) -> 'Node':
                node = gen_node(config)
                if node.status.status == EvaluationStatus.Status.FAILURE:
                    raise CannotInsert_EvaluationFailedInPlace(self, node, node.status.reason)
                return node
            node = self.parent._insert_before_child(self, my_gen_node)
            node.refresh_all_after_me()
    def append(self, gen_node: gen_node) -> None:
        raise NotImplementedError("`append` must be implemented by subclass")
    def _locate_node(self, ids: Sequence[local_step], id: step, pos: int = 0) -> 'Node':
        if pos == len(ids):
            return self
        raise NodeNotFound(id)
    def locate_node(self, id: step) -> 'Node':
        parts = id.split('.')
        return self._locate_node(parts, id)
    def is_proof_finished(self) -> bool:
        return self.status.status == EvaluationStatus.Status.SUCCESS
    def fill(self, id: step, gen_node: gen_node) -> None:
        ids = id.split('.')
        node = self._locate_node(ids[:-1], id, 0)
        to_fill = node._id_of_openning_prf_to_fill()
        if to_fill is None:
            raise CannotFill_NodeNotFound(id)
        if to_fill != id:
            raise CannotFill_BadNode(id)
        node.append(gen_node)
    def _id_of_openning_prf_to_fill(self) -> step | None:
        return None




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
    def _refresh_me_alone(self) -> None:
        now = time()
        try:
            self.messages, _ = self.ml_state.execute(self.the_operation(), self.resulting_state())
            self.status = EvaluationStatus.success(time() - now)
        except IsabelleError as err:
            self.status = EvaluationStatus.failure(time() - now, ''.join(err.errors))
    def append(self, gen_node: gen_node) -> None:
        raise CannotAppend(self, "It is not a goal or subgoal")


# abstract base class
class NonLeaf_Node(Node):
    def __init__(self, config: NodeConfig, thought: str, sub_nodes: list['Node']):
        super().__init__(config, thought)
        self.sub_nodes = sub_nodes
    def _refresh_all_children_after(self, after: 'Node') -> None:
        """
        refreshing the status of all the nodes excluding and after the `after`
        """
        can_continue : bool | None = None
        for child in self.sub_nodes: 
            if can_continue is None:
                if child is after:
                    can_continue = True
            else:
                if can_continue:
                    child._refresh_me_alone()
                    can_continue = child.status.status == EvaluationStatus.Status.SUCCESS
                else:
                    child.status = EVALUATION_CACNCELLED
        if can_continue is None:
            raise InternalError("Cannot find the target to refresh in my children")
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
                node = gen_node(NodeConfig(new_id, child.ml_state, self))
                for x in self.sub_nodes:
                    if x is node:
                        raise InternalError("The target node to insert is already in my children")
                child.ml_state = Minilang_State.assign(child.ml_state)
                self.sub_nodes.insert(i, node)
                return node
        raise InternalError("Cannot find the target to insert-before in my children")
    def _resulting_state_of_all_children(self):
        raise NotImplementedError("`_resulting_state_of_all_children` must be implemented by sub-classes")
    def _resulting_state_of_child(self, node: Node) -> Minilang_State:
        for i, child in enumerate(self.sub_nodes):
            if child is node:
                if i < len(self.sub_nodes) - 1:
                    return self.sub_nodes[i+1].ml_state
        return self._resulting_state_of_all_children()
    def _locate_node(self, ids: Sequence[local_step], id: step, pos: int = 0) -> 'Node':
        if pos == len(ids):
            return self
        local_step = ids[pos]
        for child in self.sub_nodes:
            if child.local_step == local_step:
                return child._locate_node(ids, id, pos + 1)
        raise NodeNotFound(id)
    def is_proof_finished(self) -> bool:
        for child in self.sub_nodes:
            if not child.is_proof_finished():
                return False
        return self.status.status == EvaluationStatus.Status.SUCCESS



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
    def _state_before_ending(self) -> Minilang_State:
        if self.has_ending_opr():
            return self._state_before_ending_
        else:
            raise InternalError("The node doesn't have an ending operation, but the method `_state_before_ending` is called")
    def _resulting_state_of_all_children(self) -> Minilang_State:
        if self.has_ending_opr():
            return self._state_before_ending()
        else:
            return self.resulting_state()
    def _state_after_beginning(self) -> Minilang_State:
        if self.sub_nodes:
            return self.sub_nodes[0].ml_state
        else:
            return self._resulting_state_of_all_children()
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

    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> tuple[bool, failure_reason]:
        try:
            msgs, _ = self.ml_state.execute(begin_opr, self._state_after_beginning())
            self.messages.extend(msgs)
            return (True, None)
        except IsabelleError as err:
            return (False, self._beginning_opr_err_msgs(err))
    def _refresh_me_alone(self):
        begin_opr = self.beginning_opr()
        now = time()
        reason : failure_reason = None
        head_succeeded = True
        can_continue : bool = True
        if begin_opr is not None:
            ret, reason = self._refresh_the_beginning_opr(begin_opr)
            if not ret:
                head_succeeded = False
                can_continue = False
        for child in self.sub_nodes:
            if can_continue:
                child._refresh_me_alone()
                can_continue = child.status.status == EvaluationStatus.Status.SUCCESS
                if not can_continue:
                    reason = self._child_refresh_failure_err_msgs(child)
            else:
                child.status = EVALUATION_CACNCELLED
        if can_continue:
            ending_opr = self.ending_opr()
            if ending_opr is not None:
                if not self.sub_nodes and begin_opr is None:
                    self.ml_state.skip(self._state_before_ending_)
                try:
                    msgs, _ = self._state_before_ending_.execute(ending_opr, self.resulting_state())
                    self.messages.extend(msgs)
                except IsabelleError as err:
                    reason = self._ending_opr_err_msgs(err)
                    can_continue = False
            if can_continue and begin_opr is None and ending_opr is None and not self.sub_nodes:
                self.ml_state.skip(self.resulting_state())
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
    def _print_header(self, ident: int, file: TextIO) -> None:
        raise NotImplementedError("`_print_header` must be implemented by subclass")
    def _title_of_children(self, ident: int) -> tuple[str | None, int]:
        return ("proof", ident+1)
    def _local_step_of_next_proof_step(self) -> local_step:
        if self.sub_nodes:
            return incr_id_major(self.sub_nodes[-1].local_step)
        else:
            return "1"
    def _id_of_openning_prf_to_fill(self) -> step | None:
        if self.id:
            return f"{self.id}.{self._local_step_of_next_proof_step()}"
        else:
            return self._local_step_of_next_proof_step()
    def print(self, ident: int, file: TextIO):
        ident = super().print(ident, file)
        self._print_header(ident, file)
        status = self.status
        if status.status == EvaluationStatus.Status.FAILURE:
            print_failure_reason(ident, file, status.reason)
        title, child_ident = self._title_of_children(ident)
        if title is None:
            for step in self.sub_nodes:
                step.print(child_ident, file)
        else:
            if self.sub_nodes:
                print_indent(ident, file)
                file.write(title)
                file.write(":\n")
                for step in self.sub_nodes:
                    step.print(child_ident, file)
            else:
                print_indent(ident, file)
                file.write(title)
                file.write(": empty!\n")
        if self.has_ending_opr():
            ptree = self._state_before_ending().prooftree
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
                        print_pending_goal(goal, to_fill, ident, file)
                case _:
                    if self._allow_multi_goal:
                        goal = goals[0]
                        to_fill = self._id_of_openning_prf_to_fill()
                        if to_fill is not None:
                            print_pending_goal(goal, to_fill, ident, file)
                    else:
                        raise InternalError("The open goals of StdBlock should not exceed one. "
                        "To express multiple goals, you should use a StdBlock whose children are GoalNodes. See Rule as an example.")
        return ident
    def append(self, gen_node: gen_node) -> None:
        if not self.has_ending_opr():
            raise InternalError("The node doesn't have an ending operation. Don't know how to append a node to it.")
        local_step = self._local_step_of_next_proof_step()
        (_, ml_state) = self._state_before_ending_.skip(None)
        config = NodeConfig(local_step, ml_state, self)
        node = gen_node(config)
        if node.status.status == EvaluationStatus.Status.FAILURE:
            raise CannotAppend(node, node.status.reason)
        self.sub_nodes.append(node)
    def is_proof_finished(self) -> bool:
        return self._body_subnodes_succeeded and super().is_proof_finished()


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

class GoalNode(StdBlock):
    """
    GoalNode is a container that stores the proofs of a single goal.
    When executing a Node produces multiple subgoals, each child of that Node
    is a GoalNode corresponding to one of the subgoals, and the children of each
    GoalNode are the proof steps for its corresponding subgoal.
    """
    def __init__(self, config: NodeConfig, goal: Goal, is_single_goal: bool, show_goal: bool):
        # """
        # goal_index: starting from 0
        # """
        # if single_mode:
        #     id = f"$goal"
        # else:
        #     id = f"proof of goal{goal_index}"
        super().__init__(config, "", [])
        # self.id = id
        self.goal = goal
        self.is_single_goal = is_single_goal
        self.show_goal = show_goal
        self._allow_multi_goal = True
        # self.goal_index = goal_index
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
    def _print_header(self, ident: int, file: TextIO):
        if self.show_goal:
            print_goal(self.goal, ident, True, file)
    def _print_step_id(self, ident: int, file: TextIO) -> int:
        if self.is_single_goal:
            return ident
        else:
            return super()._print_step_id(ident, file)

#abstract base class
class SubgoalMaker(GoalContainer, StdBlock):
    def beginning_opr(self) -> Minilang_Operation:
        raise NotImplementedError("`beginning_opr` must be implemented by subclass")
    def has_ending_opr(self) -> bool:
        return True
    def _refresh_the_beginning_opr(self, begin_opr: Minilang_Operation) -> tuple[bool, failure_reason]:
        (success, reason) = super()._refresh_the_beginning_opr(begin_opr)
        if success:
            s0 = self._state_after_beginning()
            if s0.prooftree is None:
                raise InternalError("The prooftree of the state after beginning is not initialized, meaning the node is not refreshed")
            goals = s0.prooftree.top_goals()
            if len(goals) == len(self.sub_nodes):
                pass
            elif len(goals) <= 1:
                self.sub_nodes = []
            else:
                self.sub_nodes = []
                ml_state = s0
                for i, goal in enumerate(goals):
                    self.sub_nodes.append(GoalNode(NodeConfig(str(i+1), ml_state, self), goal, False, True))
                    (_, ml_state) = ml_state.sorry(None, None)
            return (True, None)
        else:
            return (False, reason)

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
                    return Minilang_Operation.NEXT(None)
                else:
                    return None
        raise InternalError("The given argument is not a child of this node")


### Concrete Models

#### Arguments of Concrete Operations

class Statement(TypedDict):
    english: str
    isabelle: str

def print_statement(self: Statement, ident: int, file: TextIO):
    print_indent(ident, file)
    file.write(f"- english: {self["english"]}\n")
    print_indent(ident, file)
    file.write(f"  isabelle: {self["isabelle"]}\n")

#### Obvious

class Obvious_ToolArg(TypedDict):
    thought: str
    facts: list[Fact]

class Obvious(Leaf):
    def __init__(self, config: NodeConfig, arg : Obvious_ToolArg):
        super().__init__(config, arg["thought"])
        self.facts = arg["facts"]
        self.fact_refs = [
            self.ml_state.search_fact([
                [Criterion_XPattern(True, fact.isabelle_expression, fact.for_any)]
            ]) for fact in self.facts]
    @staticmethod
    def gen(arg : Obvious_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Obvious':
            return Obvious.new(config, arg)
        return mk
    def print(self, ident: int, file: TextIO) -> int:
        self._print_step_id(ident, file)
        ident += 1
        self._print_thought(ident, file)
        print_indent(ident, file)
        file.write("operation: Obvious\n")
        if self.facts:
            print_indent(ident, file)
            file.write(f"with facts:\n")
            for fact in self.facts:
                fact.print(ident+1, file)
        return ident
    def the_operation(self) -> Minilang_Operation:
        return Minilang_Operation.HAMMER(self.fact_refs)


#### So

#### Have

class Have_ToolArg(TypedDict):
    thought: str
    statement: Statement
class Have(StdBlock):
    def __init__(self, config: NodeConfig, arg : Have_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
    @staticmethod
    def gen(arg : Have_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Have':
            return Have.new(config, arg)
        return mk
    def _print_header(self, ident: int, file: TextIO):
        print_indent(ident, file)
        file.write("operation: Have\n")
        self._print_thought(ident, file)
        print_indent(ident, file)
        file.write(f"statement:\n")
        print_indent(ident+1, file)
        file.write(f"english: {self.statement['english']}\n")
        print_indent(ident+1, file)
        file.write(f"isabelle: {self.statement['isabelle']}\n")
    def beginning_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.HAVE(self.statement['isabelle'])
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Fail to claim the intermediate subgoal because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return "Fail to prove this statement because one of the following proof steps fails."
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        if self.sub_nodes:
            return "The statement is nontrivial. Detailed proofs are required to establish this statement."
        else:
            return "Each of the following proof steps above is valid, but the target statement doesn't trivially follow from these steps. Please provide more detailed proof steps."

#### Obtain

class Obtain_ToolArg(TypedDict):
    thought: str
    variables: list[Explicit_Var]
    constraints: list[Statement]

class Obtain(StdBlock):
    def __init__(self, config: NodeConfig, arg : Obtain_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.variables = arg["variables"]
        self.constraints = arg["constraints"]
    @staticmethod
    def gen(arg : Obtain_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Obtain':
            return Obtain.new(config, arg)
        return mk
    def _print_header(self, ident: int, file: TextIO):
        print_indent(ident, file)
        file.write("operation: obtain\n")
        self._print_thought(ident, file)
        print_indent(ident, file)
        file.write(f"variables:\n")
        for v in self.variables:
            print_indent(ident+1, file)
            if v['type'] is not None:
                file.write(f"- {v['name']}: {v['type']}\n")
            else:
                file.write(f"- {v['name']}\n")
        match self.constraints:
            case []:
                pass
            case [constraint]:
                print_indent(ident, file)
                file.write(f"constraint:\n")
                print_indent(ident+1, file)
                file.write(f"english: {constraint['english']}\n")
                print_indent(ident+1, file)
                file.write(f"isabelle: {constraint['isabelle']}\n")
            case _:
                print_indent(ident, file)
                file.write(f"constraints:\n")
                for constraint in self.constraints:
                    print_indent(ident+1, file)
                    file.write(f"- english: {constraint['english']}\n")
                    print_indent(ident+1, file)
                    file.write(f"  isabelle: {constraint['isabelle']}\n")
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

#### InferenceRule

class InferenceRule_ToolArg(TypedDict):
    thought: str
    rule: Fact | None
    # TODO: write some skills telling the agent how to associate common operations (e.g., proof by contradiction, proof by cases, etc.) with the inference rules

class InferenceRule(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, arg : InferenceRule_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.rule = arg["rule"]
        self.rule_ref = self.ml_state.fetch_rule_fact(self.rule) if self.rule is not None else None
    @staticmethod
    def gen(arg : InferenceRule_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'InferenceRule':
            return InferenceRule.new(config, arg)
        return mk
    def _print_header(self, ident: int, file: TextIO):
        print_indent(ident, file)
        file.write("operation: setting inference rule\n")
        self._print_thought(ident, file)
        print_indent(ident, file)
        file.write(f"rule: {self.rule_ref if self.rule_ref is not None else 'default'}\n")
        if len(self.sub_nodes) <= 1:
            s0 = self._state_after_beginning()
            if s0.prooftree is None:
                raise InternalError("The prooftree of the state after beginning is not initialized, meaning the node is not refreshed")
            goal = s0.prooftree.top_goal()
            print_indent(ident, file)
            file.write("derived goal:\n")
            print_goal(goal, ident+1, False, file)
    def beginning_opr(self) -> Minilang_Operation:
        return Minilang_Operation.RULE(self.rule_ref)
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        return f"Fail to apply the inference rule because: {"\n".join(err.errors)}"
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return f"Subgoal {child.id} fails to be proven."
    def has_ending_opr(self) -> bool:
        return False
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("An InferenceRule doesn't have an ending operation")
    def ending_opr(self) -> Minilang_Operation | None:
        return None
    def _title_of_children(self, ident: int) -> tuple[str | None, int]:
        if len(self.sub_nodes) <= 1:
            return (None, ident-1)
        else:
            return ("derived subgoals", ident+1)

### Branch

class Branch_ToolArg(TypedDict):
    thought: str
    cases: list[Statement]

class Branch(SubgoalMaker_NoTailEnder):
    def __init__(self, config: NodeConfig, arg: Branch_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.cases = arg["cases"]
    @staticmethod
    def gen(arg : Branch_ToolArg) -> gen_node:
        def mk(config: NodeConfig) -> 'Branch':
            return Branch.new(config, arg)
        return mk
    def _title_of_children(self, ident: int) -> tuple[str | None, int]:
        return ('cases', ident+1)
    def _print_header(self, ident: int, file: TextIO):
        print_indent(ident, file)
        file.write("operation: Branch\n")
        self._print_thought(ident, file)
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
    


### Top Root

class GlobalEnv(StdBlock):
    def __init__(self, config: NodeConfig):
        if not isinstance(config.parent, Root):
            raise InternalError("The parent of a GlobalEnv must be a Root")
        super().__init__(config, "", [])
    def beginning_opr(self) -> None:
        return None
    def ending_opr(self) -> None:
        return None
    def has_ending_opr(self) -> bool:
        return False
    def _beginning_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A GlobalEnv doesn't have a beginning operation")
    def _child_refresh_failure_err_msgs(self, child : Node) -> failure_reason:
        return "" # This suppresses the error message printing on GlobalEnv
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A GlobalEnv doesn't have an ending operation")
    def _print_header(self, ident: int, file: TextIO):
        pass
    def _title_of_children(self, ident: int) -> tuple[str | None, int]:
        return (None, ident-1)
    def _print_step_id(self, ident: int, file: TextIO) -> int:
        return ident

class Root(GoalContainer, StdBlock):
    def __init__(self, goals_and_ptree: tuple[Goals, ML_ProofTree], connection: Connection):
        (goals, ptree) = goals_and_ptree
        self.context = goals.context
        self.goals = goals.goals
        ml_state0 = Minilang_State(connection, '$init', ptree)
        super().__init__(NodeConfig("$root", ml_state0, None), "", [])
        self.sub_nodes.append(GlobalEnv(NodeConfig("global", ml_state0, self)))
        _, ml_state = ml_state0.skip(None)
        is_single_goal = len(self.goals) == 1
        for i, goal in enumerate(self.goals):
            if is_single_goal:
                goal_id = ""
            else:
                goal_id = f"goal{i+1}"
            goal_node = GoalNode(NodeConfig(goal_id, ml_state, self), goal, is_single_goal, True)
            goal_node.id = goal_id
            self.sub_nodes.append(goal_node)
            (_, ml_state) = ml_state.sorry(None, None)
        self.final_ml_state = ml_state
    def resulting_state(self) -> Minilang_State:
        return self.final_ml_state
    def _print_step_id(self, ident: int, file: TextIO) -> int:
        return ident
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
    def print(self, ident: int, file: TextIO) -> int:
        match len(self.goals):
            case 1:
                print_vars({**self.context.vars, **self.goals[0].context.vars}, ident, file)
                print_hyps({**self.context.hyps, **self.goals[0].context.hyps}, ident, file)
                self.sub_nodes[0].print(ident, file)
                self.sub_nodes[1].print(ident, file)
            case _:
                print_vars(self.context.vars, ident, file)
                print_hyps(self.context.hyps, ident, file)
                self.sub_nodes[0].print(ident, file)
                file.write("proof goals:\n")
                for i, goal in enumerate(self.goals):
                    print_indent(ident+1, file)
                    file.write(f"- goal index: {i+1}\n")
                    self.sub_nodes[i+1].print(ident+2, file)
        return ident
    def refresh_goals(self):
        pass
    def _locate_node(self, ids: Sequence[local_step], id: step, pos: int = 0) -> 'Node':
        if pos != 0:
            raise InternalError("pos should be 0 when locating a node in a Root")
        if not ids:
            if len(self.goals) == 1:
                return self.sub_nodes[1]
            else:
                raise InternalError(f"Bad id, {id}")
        if ids[0] == "global":
            return self.sub_nodes[0]._locate_node(ids, id, 1)
        else:
            if len(self.goals) <= 1:
                return self.sub_nodes[1]._locate_node(ids, id, 0)
            else:
                for node in self.sub_nodes:
                    if node.local_step == ids[0]:
                        return node._locate_node(ids, id, 1)
                raise NodeNotFound(id)
    # def _locate_node(self, ids: Sequence[local_step], id: step, pos: int = 0) -> 'Node':
    #     local_step = ids[pos]
    #     for child in self.sub_nodes:
    #         if child.local_step == local_step:
    #             return child._locate_node(ids, id, pos+1)
    #     raise NodeNotFound(id)
    # def _child_has_ending_opr(self, child : Node) -> bool:
    #     return False
    # def _ending_opr_of_child(self, child : Node) -> Minilang_Operation | None:
    #     return None



#class 


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