"""The Python half of the test suite's sample plugin (Sample_Plugin.thy): one
node class per user operation, written as docs/USER_OPERATIONS.md section 4.1
describes.  Importing this package registers the four classes."""
from typing import NotRequired, TypedDict

from Isabelle_RPC_Host import ascii_of_unicode

from IsaMini.AoA.model import (
    EvaluationStatus, FailureReason, Leaf, Message, StdBlock, SubgoalMaker, UserNode,
    Warning, print_indent, proof_operation, raw_proof)


class Applied_Msg(Message):
    """Apply's own message (tag 21): the method text, as the ML half reported it."""
    def __init__(self, method: str):
        self.method = method


class Apply_ToolArg(TypedDict):
    thought: NotRequired[str]
    method: str


@proof_operation("Apply", Apply_ToolArg)
class Apply(UserNode, SubgoalMaker):
    """Apply an Isabelle proof method; each subgoal it leaves becomes a child goal."""
    construct_schema = {
        "type": "object", "additionalProperties": False,
        "description": "apply an Isabelle proof method to the current goal; each subgoal "
                       "the method leaves becomes a goal to prove",
        "properties": {
            "operation": {"const": "Apply", "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"},
            "method": {"type": "string",
                       "description": "Isabelle method text, e.g. `(simp add: foo)`"}},
        "required": ["operation", "thought", "method"]}

    def __init__(self, config, arg: Apply_ToolArg):
        super().__init__(config, arg.get("thought", ""), [])
        self.method = arg["method"]

    def payload(self):
        return ascii_of_unicode(self.method)

    @classmethod
    def unpack_own_message(cls, value):
        return Applied_Msg(value)

    def quickview_title(self) -> str:
        return f"Apply {self.method}"

    def _print_header(self, indent, file, show_warnings=False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Apply\n")
        print_indent(indent, file)
        file.write(f"method: {self.method}\n")
        if self.status.status is EvaluationStatus.Status.SUCCESS:
            for m in self._state_after_beginning().messages:
                if isinstance(m, Applied_Msg):
                    print_indent(indent, file)
                    file.write(f"applied: {m.method}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file, [Warning.Position.HEADER])

    def _beginning_opr_err_msgs(self, err) -> FailureReason:
        return FailureReason("Fail to apply the method.\n" + "\n".join(err.errors))

    def _child_refresh_failure_err_msgs(self, child) -> FailureReason:
        return FailureReason(f"Subgoal {child.id} fails to be proven.")

    def _title_of_children(self, indent):
        return (None, indent - 1) if len(self.sub_nodes) <= 1 else ("derived subgoals", indent + 1)


class HaveText_ToolArg(TypedDict):
    thought: NotRequired[str]
    name: str
    statement: str
    proof: NotRequired[raw_proof | None]


@proof_operation("HaveText", HaveText_ToolArg)
class HaveText(UserNode, StdBlock):
    """Claim a statement given as Isabelle text, proved by the sub-proof; a block.
    The sub-proof field is named `proof`, as every sub-proof field is (`proof` or
    `proofs`) and no other field is: the DeepSeek form of the schema removes
    fields by these names."""
    construct_schema = {
        "type": "object", "additionalProperties": False,
        "description": "claim an intermediate statement, written as an Isabelle proposition",
        "properties": {
            "operation": {"const": "HaveText", "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"},
            "name": {"type": "string", "description": "the name of the claimed fact"},
            "statement": {"type": "string", "description": "the Isabelle proposition"},
            "proof": {"$ref": "#/$defs/Proof"}},
        "required": ["operation", "thought", "name", "statement"]}

    def __init__(self, config, arg: HaveText_ToolArg, parsed_proof):
        super().__init__(config, arg.get("thought", ""), [])
        self.name = arg["name"]
        self.statement = arg["statement"]
        self._proof = parsed_proof

    def payload(self):
        return (self.name, ascii_of_unicode(self.statement))

    def quickview_title(self) -> str:
        return f"HaveText {self.name}"

    def _print_header(self, indent, file, show_warnings=False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: HaveText\n")
        print_indent(indent, file)
        file.write(f"name: {self.name}\n")
        print_indent(indent, file)
        file.write(f"statement: {self.statement}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file, [Warning.Position.HEADER])

    def _beginning_opr_err_msgs(self, err) -> FailureReason:
        return FailureReason("Fail to claim the statement because: " + "\n".join(err.errors))

    def _child_refresh_failure_err_msgs(self, child) -> FailureReason:
        return FailureReason("Fail to prove the statement because one of the following proof steps fails.")

    def _ending_opr_err_msgs(self, err) -> FailureReason:
        return FailureReason("The statement does not follow from the proof steps above.")


class TwoGoals_ToolArg(TypedDict):
    thought: NotRequired[str]


@proof_operation("TwoGoals", TwoGoals_ToolArg)
class TwoGoals(UserNode, Leaf):
    """A Leaf whose operation leaves two subgoals (rule conjI): the one-subgoal rule refuses it."""
    construct_schema = {
        "type": "object", "additionalProperties": False,
        "description": "split a conjunction (a sample that breaks the one-subgoal rule of a Leaf)",
        "properties": {
            "operation": {"const": "TwoGoals", "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"}},
        "required": ["operation", "thought"]}

    def __init__(self, config, arg: TwoGoals_ToolArg):
        super().__init__(config, arg.get("thought", ""))

    def payload(self):
        return None

    def quickview_title(self) -> str:
        return "TwoGoals"

    def print(self, indent, file, update_line=False, show_warnings=False) -> int:
        indent = super().print(indent, file, update_line, show_warnings=show_warnings)
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: TwoGoals\n")
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file, [Warning.Position.HEADER, Warning.Position.FOOTER])
        return indent


class Consider_ToolArg(TypedDict):
    thought: NotRequired[str]
    first: str
    second: str


@proof_operation("Consider", Consider_ToolArg)
class Consider(UserNode, SubgoalMaker):
    """Case analysis on two statements given as text (composes BRANCH); a SubgoalMaker,
    so the input gate refuses a goal with schematic variables."""
    construct_schema = {
        "type": "object", "additionalProperties": False,
        "description": "case analysis on two Isabelle propositions",
        "properties": {
            "operation": {"const": "Consider", "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"},
            "first": {"type": "string", "description": "the first case, an Isabelle proposition"},
            "second": {"type": "string", "description": "the second case"}},
        "required": ["operation", "thought", "first", "second"]}

    def __init__(self, config, arg: Consider_ToolArg):
        super().__init__(config, arg.get("thought", ""), [])
        self.first = arg["first"]
        self.second = arg["second"]
        self._initial_goal_index = 0   # the first child is the exhaustiveness goal, as Branch's is

    def payload(self):
        return (ascii_of_unicode(self.first), ascii_of_unicode(self.second))

    def quickview_title(self) -> str:
        return "Consider"

    def _print_header(self, indent, file, show_warnings=False):
        self._print_thought(indent, file)
        print_indent(indent, file)
        file.write("operation: Consider\n")
        print_indent(indent, file)
        file.write(f"first: {self.first}\n")
        print_indent(indent, file)
        file.write(f"second: {self.second}\n")
        self._print_evaluation_status(indent, file)
        if show_warnings:
            self._print_warnings(indent, file, [Warning.Position.HEADER])

    def _beginning_opr_err_msgs(self, err) -> FailureReason:
        return FailureReason("Fail to open the cases.\n" + "\n".join(err.errors))

    def _child_refresh_failure_err_msgs(self, child) -> FailureReason:
        return FailureReason(f"Case {child.id} fails to be proven.")

    def _title_of_children(self, indent):
        return (None, indent - 1) if len(self.sub_nodes) <= 1 else ("cases", indent + 1)
