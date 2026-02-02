from optparse import Option
import stat
from time import time
from typing import Any, NamedTuple, Sequence, Optional
from Isabelle_RPC_Host import Connection, IsabelleError
import io
from enum import Enum

type varname = str
type varname_spec = Optional[varname] # underscore '_' is represented as None
type typ = str
type term = str
type local_step = str
type Vars = dict[varname, typ]
type Hyps = dict[varname, term]
type FactRef = str


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

def print_pending_goal(goal: Goal, step: step, ident: int, file):
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
    def __init__(self, goals : Optional[list[Goals]]) -> None:
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

class MLPT_Goal(ML_ProofTree):
    def __init__(self, context : Context, conclusion: term):
        self.context = context
        self.conclusion = conclusion
    def children(self) -> list[ML_ProofTree]:
        return []

class MLPT_Bundle(ML_ProofTree):
    def __init__(self, context : Context, subs : list[ML_ProofTree]):
        self.context = context
        self.subs = subs
    def children(self) -> list[ML_ProofTree]:
        return self.subs

class MLPT_Block(ML_ProofTree):
    def __init__(self, sub : ML_ProofTree):
        self.sub = sub
    def children(self) -> list[ML_ProofTree]:
        return [self.sub]

def unpack_MLPT(data) -> ML_ProofTree:
    (kind, x) = data
    match kind:
        case 0:
            return MLPT_Goal(Context.unpack(x), x[1])
        case 1:
            return MLPT_Bundle(Context.unpack(x), [unpack_MLPT(sub) for sub in x[1]])
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
    def SORRY(varnames : Optional[list[varname_spec]]):
        return Minilang_Operation("SORRY", varnames)
    @staticmethod
    def NEXT(facts : list[FactRef], varnames : Optional[list[varname_spec]]):
        return Minilang_Operation("NEXT", (facts, varnames))
    @staticmethod
    def END(facts : list[FactRef]):
        return Minilang_Operation("END", facts)
    @staticmethod
    def IDENTITY():
        return Minilang_Operation("IDENTITY", None)

class Minilang_State:
    def __init__(self, connection: Connection, name: str):
        self.connection = connection
        self.name = name
    state_counter = 0
    @classmethod
    def assign_name(cls) -> str:
        cls.state_counter += 1
        return f"${cls.state_counter}"
    @classmethod
    def assign(cls, connection : 'Connection | Minilang_State'):
        if isinstance(connection, Minilang_State):
            connection = connection.connection
        return Minilang_State(connection, cls.assign_name())
    def execute(self, opr: Minilang_Operation, assign_to: Optional['Minilang_State']) -> tuple[list[Message], ML_ProofTree, 'Minilang_State']:
        if assign_to is None:
            assign_to = Minilang_State(self.connection, type(self).assign_name())
        dest_name = assign_to.name
        self.connection.write((1, (self.name, dest_name, (opr.command, opr.arg))))
        (msgs, tree) = self.connection.read()
        msgs = [msg.unpack(msg) for msg in msgs]
        tree = unpack_MLPT(tree)
        return (msgs, tree, assign_to)
    def sorry(self, varnames: Optional[list[varname_spec]], assign_to: Optional['Minilang_State']) -> tuple[list[Message], ML_ProofTree, 'Minilang_State']:
        return self.execute(Minilang_Operation.SORRY(varnames), assign_to)

### Errors

class OprError(Exception):
    pass
class InternalError(Exception):
    pass

type timedelta = float # in seconds
class EvaluationStatus:
    def __init__(self, time: timedelta) -> None:
        self.time = time
class EvaluationSuccess(EvaluationStatus):
    pass
class EvaluationCancelled(EvaluationStatus):
    """
    Cancelled due to failures in evaluating the previous steps
    """
    pass
EVALUATION_CACNCELLED = EvaluationCancelled(0)
class EvaluationFailure(EvaluationStatus):
    def __init__(self, time: timedelta, reason: list[str]) -> None:
        super().__init__(time)
        self.reason = reason
class EvaluationUnknown(EvaluationStatus):
    pass
EVALUATION_UNKNOWN = EvaluationUnknown(0.0)

### The Abstract Model

PRESERVED_NAMES = set(["global"])

# abstract base class
class Node:
    def __init__(self, local_step: local_step, thought: str, ml_state: Minilang_State, parent: Optional['NonLeaf_Node']):
        """
        ml_state: the state before executing the Node
        """
        self.local_step = local_step # immutable
        self.thought = thought
        self.ml_state = ml_state
        self.parent = parent
        self.id = f"{parent.id}.{local_step}" if parent is not None else local_step
        self.status : EvaluationStatus = EVALUATION_UNKNOWN
    def print(self, ident: int, file):
        print_indent(ident, file)
        file.write(f"- step id: {self.id}\n")
    def resulting_state(self):
        """
        The resulting state after executing the node
        """
        if self.parent is None:
            raise InternalError("Don't know how to get the resulting state of a node when its parent is none")
        else:
            self.parent._resulting_state_of_child(self)

    def assemble(self, output: Optional[list[Minilang_Operation]] = None) -> list[Minilang_Operation]:
        """
        Assembling all the abstract tree model into the final sequence of Minilang operations
        """
        raise NotImplementedError('`assemble` must be implemented by subclass')
    def _refresh_me_alone(self) -> None:
        """
        must update self.status
        """
        raise NotImplementedError("`_refresh_me_alone` must be implemented by subclass")
    def refresh_me_and_all_after(self):
        if self.parent is None:
            raise InternalError("Don't know how to refresh a node and all its after nodes when the node's parent is none")
        else:
            self.parent._refresh_all_children_after(self)
    def insert_before(self, node: 'Node') -> None:
        if self.parent is None:
            raise InternalError("Don't know how to refresh a node and all its after nodes when the node's parent is none")
        else:
            self.parent._insert_before_child(self, node)
            node.refresh_me_and_all_after()

# abstract base class
class Leaf(Node):
    def __init__(self, local_step: local_step, thought: str, ml_state: Minilang_State, parent: Optional['NonLeaf_Node']):
        super().__init__(local_step, thought, ml_state, parent)
    def the_operation(self):
        raise NotImplementedError("`the_operation` must be implemented by subclass")
    def assemble(self, output: Optional[list[Minilang_Operation]] = None) -> list[Minilang_Operation]:
        if output is None:
            output = []
        output.append(self.the_operation())
        return output
    def _refresh_me_alone(self):
        now = time()
        try:
            self.ml_state.execute(self.the_operation(), self.resulting_state())
            self.status = EvaluationSuccess(time() - now)
        except IsabelleError as err:
            self.status = EvaluationFailure(time() - now, err.messages)


# abstract base class
class NonLeaf_Node(Node):
    def __init__(self, local_step: local_step, thought: str, sub_nodes: list['Node'],
                 ml_state: Minilang_State, parent: Optional['NonLeaf_Node']):
        super().__init__(local_step, thought, ml_state, parent)
        self.sub_nodes = sub_nodes
    def _refresh_all_children_after(self, starting: 'Node'):
        status = None
        for child in self.sub_nodes: 
            if isinstance(status, EvaluationFailure):
                status = EVALUATION_CACNCELLED
            if isinstance(status, EvaluationCancelled):
                child.status = status
            if status is None and child is starting or isinstance(status, EvaluationSuccess):
                status = child._refresh_me_alone()
        if status is None:
            raise InternalError("Cannot find the target to refresh in my children")
    def _insert_before_child(self, before: 'Node', node: Node):
        found = False
        for i, child in enumerate(self.sub_nodes):
            if child is before:
                found = True
                self.sub_nodes.insert(i, node)
                #node.
        if not found:
            raise InternalError("Cannot find the target to insert-before in my children")
    def _resulting_state_of_children(self):
        raise NotImplementedError("`_resulting_state_of_children` must be implemented by sub-classes")
    def _resulting_state_of_child(self, node: Node) -> Minilang_State:
        for i, child in enumerate(self.sub_nodes):
            if child is node:
                if i < len(self.sub_nodes) - 1:
                    return self.sub_nodes[i+1].ml_state
        return self._resulting_state_of_children()


# abstract base class
class NodeBlock(NonLeaf_Node):
    def __init__(self, local_step: local_step, thought: str, sub_nodes: list['Node'],
                 ml_state: Minilang_State, parent: Optional['NonLeaf_Node']):
        super().__init__(local_step, thought, sub_nodes, ml_state, parent)
        self._state_before_ending = Minilang_State.assign(ml_state)
    def beginning_opr(self) -> Optional[Minilang_Operation]:
        raise NotImplementedError("`beginning_opr` must be implemented by subclass")
    def ending_opr(self) -> Optional[Minilang_Operation]:
        return Minilang_Operation.END([])
    def _state_after_beginning(self):
        if self.sub_nodes:
            return self.sub_nodes[0].ml_state
        else:
            return self._state_before_ending
    def _resulting_state_of_children(self):
        return self._state_before_ending
    def assemble(self, output: Optional[list[Minilang_Operation]] = None) -> list[Minilang_Operation]: 
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
        opr = self.beginning_opr()
        now = time()
        err_msgs = None
        if opr is not None:
            try:
                self.ml_state.execute(opr, self._state_after_beginning())
            except IsabelleError as err:
                err_msgs = err.messages
        status : EvaluationStatus = EvaluationSuccess(0.0)
        for child in self.sub_nodes:
            if isinstance(status, EvaluationSuccess) and err_msgs is None:
                child._refresh_me_alone()
                status = child.status
                if isinstance(status, EvaluationFailure):
                    err_msgs = status.reason
            else:
                child.status = EVALUATION_CACNCELLED
                status = EVALUATION_CACNCELLED
        if isinstance(status, EvaluationSuccess) and err_msgs is None:
            opr = self.ending_opr()
            if opr is not None:
                try:
                    self._state_before_ending.execute(opr, self.resulting_state())
                except IsabelleError as err:
                    err_msgs = err.messages
        if err_msgs is None:
            self.status = EvaluationSuccess(time() - now)
        else:
            self.status = EvaluationFailure(time() - now, err_msgs)

class SubgoalBlock(NodeBlock):
    def _refresh_me_alone(self):
        opr = self.beginning_opr()
        if opr is not None:
            self.ml_state.execute(opr, self._state_after_beginning())
        try:
            for child in self.sub_nodes:
                child._refresh_me_alone()
            opr = self.ending_opr()
            if opr is not None:
                self._state_before_ending.execute(opr, self.resulting_state())
        except IsabelleError:
            self._state_after_beginning().execute(Minilang_Operation.SORRY(None), self.resulting_state())
            pass
    

class Have(NodeBlock):
    def beginning_opr(self) -> Minilang_Operation:
        raise NotImplementedError("`beginning_opr` must be implemented by subclass")
    def ending_opr(self) -> Minilang_Operation:
        return Minilang_Operation.END([])


        

class GoalNode(NonLeaf_Node):
    def __init__(self, goal: Goal, single_mode: bool, goal_index: int, ml_state: Minilang_State, parent: 'Root'):
        """
        goal_index: starting from 0
        """
        if single_mode:
            id = f"$goal"
        else:
            id = f"proof of goal{goal_index}"
        super().__init__(id, "", [], ml_state, parent)
        self.id = id
        self.goal = goal
        self.single_mode = single_mode
        self.goal_index = goal_index
    def print(self, ident: int, file):
        if self.single_mode:
            if self.sub_nodes:
                for node in self.sub_nodes:
                    node.print(ident+1, file)
            else:
                print_pending_goal(self.goal, self.id, ident, file)
        else:
           super().print(ident, file)
           ident += 1
        if self.sub_nodes:
            print_indent(ident, file)
            file.write("proof:\n")
            for node in self.sub_nodes:
                node.print(ident, file)
        else:
            print_pending_goal(self.goal, self.id, ident, file)

class GlobalEnv(NodeBlock):
    def __init__(self, ml_state: Minilang_State, parent: 'Root'):
        super().__init__("global_env", "", [], ml_state, parent)
        self.id = "global_env"
    def print(self, ident: int, file):
        for node in self.sub_nodes:
            node.print(ident, file)
        print_indent(ident, file)
        file.write("- notice: You can declare global lemmas and definitions available by"
            "the following proofs for all the goals, "
            "by calling the command `edit` with action `fill` and target step `global`.\n")

class Root(NonLeaf_Node):
    def __init__(self, goals: Goals, connection: Connection):
        self.context = goals.context
        self.goals = goals.goals
        ml_state0 = Minilang_State(connection, '$init')
        super().__init__("$root", "", [], ml_state0, None)
        if len(self.goals) == 1:
            self.sub_nodes = [GoalNode(self.goals[0], True, 0, ml_state0, self)]
        else:
            self.sub_nodes : list[Node] = [GlobalEnv(ml_state0, self)]
            ml_state = ml_state0
            for i, goal in enumerate(self.goals):
                self.sub_nodes.append(GoalNode(goal, False, i, ml_state, self))
                (_, _, ml_state) = ml_state.sorry(None)
    def print(self, ident: int, file):
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
    def refresh_goals(self):
        pass



#class 
