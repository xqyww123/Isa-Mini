from time import time
from helper import split_id_into_segs, cat_segs_into_id, incr_id_major, incr_id_minor
from typing import Any, NamedTuple, Sequence, TypedDict, Callable, TextIO, cast
from Isabelle_RPC_Host import Connection, IsabelleError
from enum import Enum

type varname = str
type varname_spec = varname | None # underscore '_' is represented as None
type typ = str
type term = str
type step = str
type local_step = str
type Vars = dict[varname, typ]
type Hyps = dict[varname, term]
type FactRef = str

class Explicit_Var(TypedDict):
    name: varname
    type: str | None

class Fact(NamedTuple):
    name: str
    term: term
    english: str

class Context(NamedTuple):
    vars: Vars
    hyps: Hyps

    @classmethod
    def unpack(cls, data) -> 'Context':
        (vars, hyp) = data
        return cls(vars, hyp)

class Goal(NamedTuple):
    context: Context
    conclusion: term

    @classmethod
    def unpack(cls, data) -> 'Goal':
        (context, conclusion) = data
        return cls(Context.unpack(context), conclusion)

class Goals(NamedTuple):
    context: Context
    goals: list[Goal]
    
    @classmethod
    def unpack(cls, data) -> 'Goals':
        (context, goals) = data
        return cls(Context.unpack(context), [Goal.unpack(goal) for goal in goals])

def print_indent(ident: int, file):
    for _ in range(ident):
        file.write("  ")

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

def print_goal(goal: Goal, ident: int, file):
    print_vars(goal.context.vars, ident, file)
    print_hyps(goal.context.hyps, ident, file)
    print_indent(ident, file)
    file.write(f"conclusion: {goal.conclusion}\n")

def print_pending_goal(goal: Goal, step: step, ident: int, file : TextIO):
    print_indent(ident, file)
    file.write(f"Error: Unfinished Proof! Call command `edit` with action `fill` and target step `{step}`"
        " to provide the proof for the following goal.\n")
    print_indent(ident, file)
    file.write("pending proof goal:\n")
    print_goal(goal, ident+1, file)

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
    def __init__(self, goals : list[Goals] | None) -> None:
        super().__init__()
        self.goals = goals
    @classmethod
    def unpack(cls, data) -> 'Goals_Msg':
        return cls([Goals.unpack(goal) for goal in data] if data is not None else None)

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

class MLPT_Block(ML_ProofTree):
    def __init__(self, sub : ML_ProofTree):
        self.sub = sub
    def children(self) -> list[ML_ProofTree]:
        return [self.sub]
    def top_goal(self) -> Goal:
        return self.sub.top_goal()
    def top_goals(self) -> list[Goal]:
        return self.sub.top_goals()

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

#### Minilang Runtime

class Minilang_Operation(NamedTuple):
    command: str
    arg: Any

    def pack(self):
        return (self.command, self.arg)

    @staticmethod
    def SORRY(varnames : list[varname_spec] | None):
        return Minilang_Operation("SORRY", varnames)
    @staticmethod
    def NEXT(facts : list[FactRef], varnames : list[varname_spec] | None):
        return Minilang_Operation("NEXT", (facts, varnames))
    @staticmethod
    def END(facts : list[FactRef]):
        return Minilang_Operation("END", facts)
    @staticmethod
    def IDENTITY():
        return Minilang_Operation("IDENTITY", None)
    @staticmethod
    def HAVE(statement: term):
        return Minilang_Operation("HAVE", statement)
    @staticmethod
    def OBTAIN(variables: list[Explicit_Var], constraints: list[term]):
        vars = [(v["name"], v["type"] if "type" in v else None) for v in variables]
        return Minilang_Operation("OBTAIN", (vars, constraints))
    @staticmethod
    def SKIP():
        return Minilang_Operation("SKIP", None)

class Minilang_State:
    def __init__(self, connection: Connection, name: str, prooftree : ML_ProofTree | None):
        self.connection = connection
        self.name = name
        self.prooftree = prooftree
    def initialized(self) -> bool:
        return self.prooftree is not None
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
    def execute(self, opr: Minilang_Operation, assign_to: 'Minilang_State | None') -> tuple[list[Message], 'Minilang_State']:
        if assign_to is None:
            assign_to = Minilang_State(self.connection, type(self).assign_name(), None)
        dest_name = assign_to.name
        self.connection.write((1, (self.name, dest_name, (opr.command, opr.arg))))
        (msgs, tree) = self.connection.read()
        msgs = [msg.unpack(msg) for msg in msgs]
        assign_to.prooftree = tree
        return (msgs, assign_to)
    def sorry(self, varnames: list[varname_spec] | None, assign_to: 'Minilang_State | None') -> tuple[list[Message], 'Minilang_State']:
        return self.execute(Minilang_Operation.SORRY(varnames), assign_to)
    def skip(self, assign_to: 'Minilang_State | None') -> tuple[list[Message], 'Minilang_State']:
        return self.execute(Minilang_Operation.SKIP(), assign_to)

### Errors
type timedelta = float # in seconds
type failure_reason = str | None # a list of lines
        # None means internal error
        # [] means to suppress the error message printing

class OprError(Exception):
    pass
class CannotInsert_EvaluationFailedInPlace(OprError):
    def __init__(self, reason : failure_reason):
        self.reason = reason
class CannotAppend(OprError):
    def __init__(self, target : 'Node', reason : failure_reason):
        self.reason = reason
        self.target = target
    def __str__(self) -> str:
        return f"Cannot append on node {self.target.id} because {self.reason}"
class InternalError(Exception):
    pass

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
        self.id : step = f"{config.parent.id}.{config.local_step}" if config.parent is not None else config.local_step
        self.status : EvaluationStatus = EVALUATION_NOT_YET
    def _print_step_id(self, ident: int, file: TextIO) -> int:
        print_indent(ident, file)
        file.write(f"- step id: {self.id}\n")
        return ident + 1
    def print(self, ident: int, file : TextIO) -> int:
        return self._print_step_id(ident, file)
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
                    raise CannotInsert_EvaluationFailedInPlace(node.status.reason)
                return node
            node = self.parent._insert_before_child(self, my_gen_node)
            node.refresh_all_after_me()
    def append(self, gen_node: gen_node) -> None:
        raise NotImplementedError("`append` must be implemented by subclass")

# abstract base class
class Leaf(Node):
    def __init__(self, config: NodeConfig, thought: str):
        super().__init__(config, thought)
        self._refresh_me_alone()
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
            self.ml_state.execute(self.the_operation(), self.resulting_state())
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


# abstract base class
class StdBlock(NonLeaf_Node):
    def __init__(self, config: NodeConfig, thought: str, sub_nodes: list['Node']):
        super().__init__(config, thought, sub_nodes)
        self._state_before_ending_ = Minilang_State.assign(config.ml_state)
        self._refresh_me_alone()
    def beginning_opr(self) -> Minilang_Operation | None:
        raise NotImplementedError("`beginning_opr` must be implemented by subclass")
    def ending_opr(self) -> Minilang_Operation | None:
        return Minilang_Operation.END([])
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
    def _resulting_state_of_all_children(self):
        if self.has_ending_opr():
            return self._state_before_ending()
        else:
            return self.resulting_state()
    def _state_after_beginning(self):
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
    def _refresh_me_alone(self):
        begin_opr = self.beginning_opr()
        now = time()
        reason = None
        head_succeeded = True
        can_continue = True
        if begin_opr is not None:
            try:
                self.ml_state.execute(begin_opr, self._state_after_beginning())
            except IsabelleError as err:
                reason = self._beginning_opr_err_msgs(err)
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
                try:
                    self._state_before_ending().execute(ending_opr, self.resulting_state())
                except IsabelleError as err:
                    reason = self._ending_opr_err_msgs(err)
                    can_continue = False
            if can_continue and begin_opr is None and ending_opr is None and not self.sub_nodes:
                self.ml_state.skip(self.resulting_state())
        if can_continue is None:
            self.status = EvaluationStatus.success(time() - now)
        elif head_succeeded:
            self._state_after_beginning().sorry(None, self.resulting_state())
            self.status = EvaluationStatus.success(time() - now, reason)
        else:
            self.status = EvaluationStatus.failure(time() - now, reason)
    def _print_header(self, ident: int, file: TextIO) -> None:
        raise NotImplementedError("`_print_header` must be implemented by subclass")
    def _title_of_children(self) -> str | None:
        return "proof"
    def _local_step_of_next_proof_step(self) -> local_step:
        if self.sub_nodes:
            return incr_id_minor(self.sub_nodes[-1].local_step)
        else:
            return "1"
    def _id_of_openning_prf_to_fill(self) -> step:
        return f"{self.id}.{self._local_step_of_next_proof_step()}"
    def print(self, ident: int, file: TextIO):
        ident = super().print(ident, file)
        self._print_header(ident, file)
        status = self.status
        if status.status == EvaluationStatus.Status.FAILURE:
            reason = status.reason
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
        if self.sub_nodes:
            title = self._title_of_children()
            if title is None:
                for step in self.sub_nodes:
                    step.print(ident, file)
            else:
                print_indent(ident, file)
                file.write(title)
                file.write(":\n")
                for step in self.sub_nodes:
                    step.print(ident+1, file)
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
                    print_pending_goal(goal, self._id_of_openning_prf_to_fill(), ident, file)
                case _:
                    raise InternalError("The open goals of StdBlock should not exceed one. "
                        "To express multiple goals, you should use a StdBlock whose children are GoalNodes. See Rule as an example.")
        return ident

# abstract base class
class GoalContainer(NonLeaf_Node):
    def _child_has_ending_opr(self, child : Node) -> bool:
        return True
    def _ending_opr_of_child(self, child : Node) -> Minilang_Operation | None:
        for i, c in enumerate(self.sub_nodes):
            if c is child:
                if i < len(self.sub_nodes) - 1:
                    return Minilang_Operation.NEXT([], None)
                else:
                    return Minilang_Operation.END([])
        raise InternalError("The given argument is not a child of this node")

class GoalNode(StdBlock):
    """
    Children: the proof steps for the goal
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
            print_goal(self.goal, ident, file)
    def _print_step_id(self, ident: int, file: TextIO) -> int:
        if self.is_single_goal:
            return ident
        else:
            return super()._print_step_id(ident, file)

### Concrete Models

#### Arguments of Concrete Operations

class Statement(TypedDict):
    english: str
    isabelle: str

#### Have

class Have_ToolArg(TypedDict):
    thought: str
    statement: Statement
class Have(StdBlock):
    def __init__(self, config: NodeConfig, arg : Have_ToolArg):
        super().__init__(config, arg["thought"], [])
        self.statement = arg["statement"]
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
    def _title_of_children(self) -> str | None:
        return None
    def _print_step_id(self, ident: int, file: TextIO) -> int:
        return ident

class Root(StdBlock):
    def __init__(self, goals_and_ptree: tuple[Goals, ML_ProofTree], connection: Connection):
        (goals, ptree) = goals_and_ptree
        self.context = goals.context
        self.goals = goals.goals
        ml_state0 = Minilang_State(connection, '$init', ptree)
        super().__init__(NodeConfig("$root", ml_state0, None), "", [])
        self.sub_nodes.append(GlobalEnv(NodeConfig("$global_env", ml_state0, self)))
        ml_state = ml_state0
        is_single_goal = len(self.goals) == 1
        for i, goal in enumerate(self.goals):
            goal_id = f"goal{i}"
            goal_node = GoalNode(NodeConfig(goal_id, ml_state, self), goal, is_single_goal, False)
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
        return [] # This suppresses the error message printing on Root
    def _ending_opr_err_msgs(self, err : IsabelleError) -> failure_reason:
        raise InternalError("A Root doesn't have an ending operation")
    def print(self, ident: int, file: TextIO) -> int:
        match len(self.goals):
            case 1:
                print_vars({**self.context.vars, **self.goals[0].context.vars}, ident, file)
                print_hyps({**self.context.hyps, **self.goals[0].context.hyps}, ident, file)
            case _:
                print_vars(self.context.vars, ident, file)
                print_hyps(self.context.hyps, ident, file)
                file.write("proof goals:\n")
                for i, goal in enumerate(self.goals):
                    print_indent(ident+1, file)
                    file.write(f"- goal index: {i+1}\n")
                    print_goal(goal, ident+2, file)
        return ident
    def refresh_goals(self):
        pass



#class 
