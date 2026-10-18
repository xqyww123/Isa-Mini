"""Unit tests of the post-instantiation probe (docs/TACTIC_DESIGN.md section
13, C24): `SubgoalMaker._refresh_the_beginning_opr` runs `_run_the_probe` after
`StdBlock._refresh_the_beginning_opr` executed round 0 into the destination
state; every later round executes into it again, the convergence check reads
it, the converged round's state is the node's result, and any failing round is
the node's failure.  A real `InferenceRule` with its real convergence check,
over stand-in states.  No REPL, no RPC."""
import asyncio
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from Isabelle_RPC_Host import IsaTerm                                        # noqa: E402
from IsaMini.AoA.model import (                                              # noqa: E402
    FailureReason, InferenceRule, Interaction_InstantiatePostSchematics, IsabelleError,
    Minilang_Operation, _MAX_POST_INST_ROUNDS)
from IsaMini.AoA.test_user_operations import bare_session                    # noqa: E402

X, NAT = IsaTerm.from_isabelle("?x"), IsaTerm.from_isabelle("nat")
R0, R1 = [("?x", "0")], [("?x", "1")]
FAILED = "Fail to apply the inference rule.\nthe op failed"


def rule(*rounds):
    """The beginning op of `rule_node()` carrying `rounds`."""
    return Minilang_Operation.RULE(None, list(rounds))


class State:
    """A stand-in Minilang_State for a RULE that leaves ?x until it carries
    `converges_at` rounds (None: never).  `execute` records (op, destination,
    log) and raises on the calls numbered in `fails` (from 0); the server-side
    prerun puts ?x in both derived subgoals, or in one when not `shared`, and
    raises when `prerun_fails`."""
    def __init__(self, converges_at: 'int | None' = 0, fails=(), shared=True, prerun_fails=False):
        self.converges_at, self.fails, self.shared = converges_at, set(fails), shared
        self.prerun_fails = prerun_fails
        self.runs: list = []
        self.preruns = 0
        self.rounds: 'int | None' = None
        self.leading_goal = None
        self.new_subgoals_count = None
        self.messages: list = []
        self._initialized = False
    def initialized(self) -> bool:
        return self._initialized
    def _left(self, n: int) -> bool:
        return self.converges_at is None or n < self.converges_at
    async def execute(self, opr, dest, *, log=True):
        self.runs.append((opr, dest, log))
        if len(self.runs) - 1 in self.fails:
            raise IsabelleError(["the op failed"], None)
        dest.rounds, dest._initialized = len(opr.arg[1]), True
        return dest
    async def schematic_variables_of(self, whole=False):
        assert self.rounds is not None, "the whole scan reads an executed state"
        return ({X: NAT} if self._left(self.rounds) else {}), {}
    async def schematic_vars_of_derived_subgoals(self, opr):
        self.preruns += 1
        if self.prerun_fails:
            raise IsabelleError(["the prerun failed"], None)
        left = ({X: NAT} if self._left(len(opr.arg[1])) else {}), {}
        return [left, left if self.shared else ({}, {})]
    async def reset(self):
        self.rounds, self._initialized = None, False
        self.leading_goal, self.new_subgoals_count, self.messages = None, None, []


def rule_node(src: State, dest: State, post_insts=None):
    """A bare InferenceRule whose beginning op is a RULE with no rule, with
    `src` as its ml_state and `dest` as its after-beginning state."""
    node = object.__new__(InferenceRule)
    node.rule_ref, node._post_insts = None, post_insts
    node.ml_state, node.sub_nodes, node._state_before_ending_ = src, [], dest
    node._first_time, node._supplied_proofs = True, None
    return node


def probe(converges_at: 'int | None' = 0, fails=(), shared=True, prerun_fails=False, post_insts=None):
    """A from_state, a destination state, and the node over them."""
    src = State(converges_at, fails, shared, prerun_fails)
    dest = State(converges_at)
    return src, dest, rule_node(src, dest, post_insts)


def agent(*answers) -> list:
    """Bind a bare session whose agent answers the k-th interaction with
    `answers[k]`; returns the interactions asked."""
    asked: list = []
    async def launch_interaction(interaction):
        assert isinstance(interaction, Interaction_InstantiatePostSchematics)
        asked.append(interaction)
        return answers[len(asked) - 1]
    bare_session().launch_interaction = launch_interaction
    return asked


def refresh(node) -> 'FailureReason | None':
    return asyncio.run(node._refresh_the_beginning_opr())


def test_the_common_case_is_one_execution_into_dest():
    src, dest, node = probe(converges_at=0)
    asked = agent()
    assert refresh(node) is None
    assert src.runs == [(rule(), dest, True)] and src.preruns == 0
    assert node._post_insts == [] and asked == []
    assert node.beginning_opr() == src.runs[0][0]      # round 0 is the op assemble packs


def test_a_confined_variable_converges_after_one_prerun():
    src, dest, node = probe(converges_at=1, shared=False)
    asked = agent()
    assert refresh(node) is None
    assert src.runs == [(rule(), dest, True)] and src.preruns == 1
    assert node._post_insts == [] and asked == []


def test_k_rounds_are_k_plus_1_executions_into_dest():
    src, dest, node = probe(converges_at=2)
    asked = agent(R0, R1)
    assert refresh(node) is None
    assert src.runs == [(rule(), dest, True), (rule(R0), dest, True), (rule(R0, R1), dest, True)]
    assert src.preruns == 2 and node._post_insts == [R0, R1]
    assert len(asked) == 2 and all(i.state is dest and i.kind == "term" for i in asked)
    assert node.beginning_opr() == src.runs[-1][0]


def test_a_failing_first_round_runs_once():
    src, dest, node = probe(fails={0, 1})
    asked = agent()
    assert refresh(node) == FailureReason(FAILED)
    assert len(src.runs) == 1 and not dest.initialized() and node._post_insts is None
    assert asked == []


def test_a_failing_later_round_is_the_failure():
    src, dest, node = probe(converges_at=1, fails={1})
    asked = agent(R0)
    assert refresh(node) == FailureReason(FAILED)
    assert src.runs == [(rule(), dest, True), (rule(R0), dest, True)] and len(asked) == 1
    # D7: no reset -- dest keeps round 0's state (a reset would flip this line)
    assert node._post_insts is None and dest.initialized() and dest.rounds == 0


def test_a_failing_convergence_check_in_round_0_is_the_failure():
    src, dest, node = probe(converges_at=1, prerun_fails=True)
    asked = agent()
    assert refresh(node) == FailureReason("Fail to apply the inference rule.\nthe prerun failed")
    assert src.runs == [(rule(), dest, True)] and asked == []
    assert node._post_insts is None and dest.initialized() and dest.rounds == 0


def test_the_round_cap():
    src, dest, node = probe(converges_at=None)
    asked = agent(*[R0] * _MAX_POST_INST_ROUNDS)
    assert refresh(node) == FailureReason(
        f"Fail to apply the inference rule.\nCould not eliminate the residual schematic "
        f"variables of this RULE operation within {_MAX_POST_INST_ROUNDS} rounds of instantiation.")
    assert len(src.runs) == len(asked) == _MAX_POST_INST_ROUNDS
    assert all(d is dest for _, d, _ in src.runs) and node._post_insts is None


def test_a_probed_node_executes_its_op_once():
    src, dest, node = probe(converges_at=None, post_insts=[R0])
    asked = agent()
    assert refresh(node) is None
    assert src.runs == [(rule(R0), dest, True)] and asked == []


def test_each_builder_packs_the_rounds_it_is_given():
    """The builders of the four probing classes: the op carries exactly the
    rounds passed in, `beginning_opr()` passes `_post_insts`, and Tactic's
    assembled op differs from the live op only in its fifth slot.  The fields
    each builder reads are set and nothing else."""
    from IsaMini.AoA.model import CaseSplit, Induction, Tactic, Tactic_Times_Msg
    def bare(cls, **fields):
        node = object.__new__(cls)
        for name, value in fields.items():
            setattr(node, name, value)
        return node
    cases = [
        (bare(InferenceRule, rule_ref=None, _post_insts=[R0]),
         lambda insts: Minilang_Operation.RULE(None, insts)),
        (bare(CaseSplit, target_isabelle_term="t", _resolved_rule_str=None, no_simp=False,
              _post_insts=[R0], _case_vars_of_child=lambda i: None),
         lambda insts: Minilang_Operation.CASE_SPLIT("t", None, None, False, insts)),
        (bare(Induction, target_isabelle_term="t", variables=[], fact_refs_to_generalize=[],
              _resolved_rule_str=None, no_simp=False, _post_insts=[R0],
              _case_vars_of_child=lambda i: None),
         lambda insts: Minilang_Operation.INDUCT("t", None, [], [], None, False, insts)),
        (bare(Tactic, tactic_full="HOL.simp", arguments="", fact_refs=[], _post_insts=[R0]),
         lambda insts: Minilang_Operation.TACTIC("HOL.simp", "", [], insts, None)),
    ]
    for node, factory in cases:
        assert node._beginning_opr_with_insts([R0, R1]) == factory([R0, R1])
        assert node.beginning_opr() == node._beginning_opr_with_insts([R0])
    tactic = cases[-1][0]
    tactic.sub_nodes, tactic._state_before_ending_ = [], State()
    tactic._state_before_ending_.messages = [Tactic_Times_Msg((1, 2))]
    assert tactic.assembled_beginning_opr() == Minilang_Operation.TACTIC("HOL.simp", "", [], [R0], (1, 2))
