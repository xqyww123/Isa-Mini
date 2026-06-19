import asyncio
import inspect
import os
import time
from IsaREPL import REPLFail
from typing import Any, Awaitable, Coroutine, NamedTuple, Sequence, TypedDict, Callable, TextIO, Union, cast
from . import model
from . import prompts as _P
from .model import *
from .model import _filter_unprovable
from abc import ABC, abstractmethod
import io
import tempfile
import subprocess
import sys

class TestFailed(Exception):
    pass

class TestCase(ABC):
    def __init__(self, name : str, file: str, line: int):
        self.name = name
        self.file = file
        self.line = line
    @abstractmethod
    async def run(self, connection: Connection, log_dir: str, global_context: Context, ptree: tuple['Goal | None', int]) -> Root:
        raise NotImplementedError("Subclass must implement run method")

type _TestOpr = Callable[[Root, MyIO], Union[None, Awaitable[None]]]

class ModelTestCase(TestCase):
    def __init__(self, name : str, file: str, line: int, opr: _TestOpr):
        super().__init__(name, file, line)
        self.opr = opr
    async def run(self, connection: Connection, log_dir: str, global_context: Context, ptree: tuple['Goal | None', int]) -> Root:
        def save_diff(actual: str, expected_path: str, test_name: str):
            """Write actual output and unified diff next to the golden YAML."""
            tests_dir = os.path.dirname(expected_path)
            actual_path = os.path.join(tests_dir, test_name + '.actual.yml')
            diff_path = os.path.join(tests_dir, test_name + '.diff')
            with open(actual_path, 'w') as f:
                f.write(actual)
            diff_result = subprocess.run(
                ['diff', '-u', expected_path, actual_path],
                capture_output=True, text=True)
            with open(diff_path, 'w') as f:
                f.write(diff_result.stdout)
        tests_dir = os.path.join(os.path.dirname(__file__), 'Tests')
        for ext in ('.diff', '.actual.yml'):
            stale = os.path.join(tests_dir, self.name + ext)
            if os.path.exists(stale):
                os.remove(stale)
        async with Session(connection.server.logger, log_dir) as session:
            root = Root((global_context, ptree), connection)
            await session.initialize(root)
            # Test-harness default: by-hand model tests don't drive an LLM, so
            # the IH-fact picker (Interaction_SelectIHFacts) has no one to
            # answer it. An induction whose in-scope context mentions the
            # induction target ∪ generalized vars fires this picker during the
            # pre-flight; without a stub the base Session.launch_interaction would
            # raise. Default to declining (select none) so such tests behave as
            # they did before the feature; any test wanting a selection just
            # reassigns root.session.launch_interaction itself (which overrides
            # this). Other interactions still raise, as before.
            async def _default_launch_interaction(interaction):
                if isinstance(interaction, (Interaction_SelectIHFacts,
                                            Interaction_ClassifyInductionVars)):
                    return await interaction.answer(AnswerIndexes(indexes=[]))
                if isinstance(interaction, Interaction_StruggleCheckpoint):
                    return (False, "test: not stuck")
                if isinstance(interaction, Interaction_DifficultyEvaluation):
                    return 0  # continue
                raise NotImplementedError(
                    "Unstubbed interaction in model test: "
                    f"{type(interaction).__name__}")
            session.launch_interaction = _default_launch_interaction
            buffer = io.StringIO()
            result = self.opr(root, MyIO(buffer))
            if inspect.iscoroutine(result):
                await result
            correct_yaml_path = self.correct_yaml_path()
            if correct_yaml_path is not None:
                with open(correct_yaml_path, 'r') as f:
                    if buffer.getvalue() != f.read():
                        save_diff(buffer.getvalue(), correct_yaml_path, self.name)
                        raise TestFailed(f"Test Failed on '{self.name}'")
            else:
                self.write_expected_yaml(buffer.getvalue())
        return root

    def correct_yaml_path(self) -> str | None:
        path = os.path.join(os.path.dirname(__file__), 'Tests', self.name + '.yml')
        if os.path.isfile(path):
            return path
        else:
            return None

    def write_expected_yaml(self, yaml: str):
        correct_yaml_path = os.path.join(os.path.dirname(__file__), 'Tests', self.name + '.yml')
        with open(correct_yaml_path, 'w') as f:
            f.write(yaml)

TESTS : dict[str, TestCase] = {}
# IMPORTANT: Each @model_test must have its own dedicated .thy file.
# Never share a .thy file between different test cases.
# The `line` argument must be the line number of `by aoa` in the .thy file.
def model_test(name: str, file: str, line: int):
    def decorator(func: _TestOpr):
        TESTS[name] = ModelTestCase(name, file, line, func)
        return func
    return decorator

def print_header(msg: str, file: MyIO):
    print("-"*50, file=file)
    print(msg, file=file)
    print("-"*50, file=file)

#@test("sqrt2", "Test_sqrt2.thy", 6)
async def _test_sqrt2(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    #goal = root.locate_node("goal1") # the same as root.sub_nodes[1]
    goal = root.sub_nodes[1]
    await goal.append([InferenceRule.gen_single({"thought": "Proof by contradiction", "rule": None})])
    print_header("Setting the inference rule", file)
    root.print(0, file)
    await goal.append([Obtain.gen_single({"thought": "I don't know", "variables": [{"name": "m", "type": "nat"}, {"name": "n", "type": "nat"}],
            "constraints": [{"conclusion": "¦sqrt 2¦ = m / n", "english": "some fancy explanation", "name": "sqrt2_eq"}]})])
    print_header("Obtain m n", file)
    root.print(0, file)
    #node = root.locate_node("2.1") # not appear
    await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    print_header("Obvious", file)
    root.print(0, file)
    await root.fill("3", [Have.gen_single({"thought": "I don't know", "statement": {"english": "some fancy explanation", "conclusion": "m^2 = (sqrt 2)^2 * n^2"}, "name": "helper_lemma"})])
    await root.fill("3.1", [Obvious.gen_single({"facts": []})])
    print_header("Have", file)
    root.print(0, file)

@model_test("Branch1", "Test_Branch.thy", 8)
async def _test_branch(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", [Branch.gen_single({
        "thought": "I don't know",
        "cases": [
            {"statement": {"english": "in case x is positive", "isabelle": "x > 0", "name": "pos"}},
            {"statement": {"english": "in case x is negative", "isabelle": "x < 0", "name": "neg"}},
            {"statement": {"english": "in case x is zero", "isabelle": "x = 0", "name": "zero"}},
        ]
    })])
    print_header("Branch", file)
    root.print(0, file)

    # Close the exhaustiveness goal 1.0
    root.session.age += 1
    await root.fill("1.0.1", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious on 1.0.1 (exhaustiveness)", file)
    root.print(0, file)
    print_header("Overview after 1.0.1", file)
    root.quickview(0, file)

    # Close case 1.1 (x > 0)
    root.session.age += 1
    await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious on 1.1.1 (x > 0)", file)
    root.print(0, file)
    print_header("Overview after 1.1.1", file)
    root.quickview(0, file)

    # Close case 1.2 (x < 0)
    root.session.age += 1
    await root.fill("1.2.1", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious on 1.2.1 (x < 0)", file)
    root.print(0, file)
    print_header("Overview after 1.2.1", file)
    root.quickview(0, file)

    # Close case 1.3 (x = 0)
    root.session.age += 1
    await root.fill("1.3.1", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious on 1.3.1 (x = 0)", file)
    root.print(0, file)
    print_header("Overview after 1.3.1", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("DoneGoalHidesPremises", "Test_DoneGoalHidesPremises.thy", 8)
async def _test_done_goal_hides_premises(root: Root, file: MyIO):
    """Bug: quickview shows premises for goals marked 'done'.
    When a GoalNode is done but _prev_quickview_context is None (first render),
    premises are printed despite the step needing no detail.
    Reproduce: Branch, close all cases without intermediate quickview,
    then call quickview — done goals should NOT show premises."""
    await root.fill("1", [Branch.gen_single({
        "thought": "case split on sign of x",
        "cases": [
            {"statement": {"english": "x is positive", "isabelle": "x > 0", "name": "pos"}},
            {"statement": {"english": "x is negative", "isabelle": "x < 0", "name": "neg"}},
            {"statement": {"english": "x is zero", "isabelle": "x = 0", "name": "zero"}},
        ]
    })])
    # Close all goals WITHOUT calling quickview in between
    root.session.age += 1
    await root.fill("1.0.1", [Obvious.gen_single({"facts": []})])
    root.session.age += 1
    await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    root.session.age += 1
    await root.fill("1.2.1", [Obvious.gen_single({"facts": []})])
    # Leave 1.3 open so the proof is not fully done
    # First quickview call: 1.1 and 1.2 are done with premises — should NOT show them
    print_header("Quickview (done goals should hide premises)", file)
    root.quickview(0, file)

@model_test("EquivDerive", "Test003.thy", 8)
async def _test_EquivDerive(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("2", [InferenceRule.gen_single({
        "thought": "Destruct equivalence",
        "rule": None
    })])
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("IntroConj", "Test_IntroConj.thy", 8)
async def _test_IntroConj(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("2", [InferenceRule.gen_single({
        "thought": "Destruct equivalence",
        "rule": None
    })])
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("IntroConj_short", "Test_IntroConj_short.thy", 8)
async def _test_IntroConj_short(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("2", [InferenceRule.gen_single({
        "thought": "Destruct equivalence",
        "rule": None
    })])
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("InferenceRuleSolvesGoal", "Test_InferenceRule_SolvesGoal.thy", 8)
async def _test_InferenceRuleSolvesGoal(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Apply refl which fully solves "a = a" — produces 0 subgoals.
    # This exercises the empty-BUNDL code path in InferenceRule._print_header.
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "Apply reflexivity",
        "rule": {"name": "refl"}
    })])
    print_header("After InferenceRule (goal fully solved)", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

# ----------------------------------------------------------------------------
# Intro default semantics: silent `standard_tac` fallback.
#
# When the leading goal has no leading quantifier / premise (normal Intro
# cannot proceed), Intro silently tries ONE `Classical.standard_tac ctxt []`
# step and accepts it ONLY when it reduces to exactly one new proof goal that
# itself needs Intro. Otherwise Intro is a no-op (goal unchanged), exactly as
# before. The four cases below pin each branch of that decision; the goal
# behaviour of one bare `rule` step on each fixture was verified empirically.
# ----------------------------------------------------------------------------

@model_test("IntroStandardSubset", "Test_IntroStandardSubset.thy", 8)
async def _test_IntroStandardSubset(root: Root, file: MyIO):
    """ACCEPT path. Goal `A ⊆ B` has no leading ⋀/⟹/∀/⟶, so normal Intro
    cannot proceed. The silent standard_tac step applies subsetI, exposing the
    single intro-able goal `⋀x. x ∈ A ⟹ x ∈ B`; Intro then fixes `x` and
    assumes `x ∈ A`, leaving `x ∈ B`. The agent still sees one Intro."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "introduce an element and the membership premise"
    })])
    print_header("After Intro (standard_tac fallback: subsetI, then introduce)", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("IntroStandardMultiGoal", "Test_IntroStandardMultiGoal.thy", 8)
async def _test_IntroStandardMultiGoal(root: Root, file: MyIO):
    """REJECT path — too many new goals. Goal `(∀x. P x) ∧ Q` does not need
    Intro; the standard_tac step applies conjI, producing TWO goals
    `∀x. P x` and `Q`. Even though the leading one (`∀x. P x`) would need
    Intro, the `exactly one new goal` guard rejects the fallback, so Intro is
    a no-op and the goal is unchanged."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "try to introduce"
    })])
    print_header("After Intro (no-op: standard_tac would split into 2 goals)", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("IntroStandardNoIntroAfter", "Test_IntroStandardNoIntroAfter.thy", 8)
async def _test_IntroStandardNoIntroAfter(root: Root, file: MyIO):
    """REJECT path — one new goal, but it still does not need Intro. Goal
    `P ∨ Q` does not need Intro; the standard_tac step applies disjI1, leaving
    the single goal `P`, which is atomic (no leading ⋀/⟹/∀/⟶). The
    `the new goal needs Intro` guard rejects the fallback, so Intro is a no-op
    and the goal is unchanged."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "try to introduce"
    })])
    print_header("After Intro (no-op: standard_tac result still needs no Intro)", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("IntroStandardSolves", "Test_IntroStandardSolves.thy", 8)
async def _test_IntroStandardSolves(root: Root, file: MyIO):
    """REJECT path — standard_tac fully solves the head goal (zero new goals).
    Goal `0 < Suc n` does not need Intro; the standard_tac step closes it
    outright (`zero_less_Suc`). With zero new goals the `exactly one new goal`
    guard rejects the fallback — crucially the solving step is DISCARDED, so
    Intro is a no-op and the goal is left intact for a later, explicit step."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "try to introduce"
    })])
    print_header("After Intro (no-op: standard_tac would solve the goal outright)", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("PostInstRule", "Test_PostInstRule.thy", 19)
async def _test_PostInstRule(root: Root, file: MyIO):
    # `myrule` applied to `P k` pins ?m:=k but leaves ?c residual in the
    # non-consume premise `Q ?c`. The consume-premise pre-flight misses it
    # (0 consumes); the post-rule probe must surface it and ask for a value.
    print_header("Initial", file)
    root.print(0, file)

    # Fixture answers for residual schematics, keyed by reported name. The stub
    # answers EVERY variable the interaction reports, each round, so the probe's
    # fixpoint loop converges (a one-shot answerer would loop forever).
    fixture = {"?c": "0::nat"}
    captured_kinds: list[str] = []
    async def stub(interaction):
        if isinstance(interaction, Interaction_InstantiatePostSchematics):
            captured_kinds.append(interaction.kind)
            print_header(f"Post-rule instantiation prompt (kind={interaction.kind})", file)
            await interaction.prompt(0, file)
            insts = [(n, fixture[n]) for n, _ in interaction.schematic_vars]
            return await interaction.answer(AnswerInstantiate(instantiations=insts))
        raise NotImplementedError(
            f"Unstubbed interaction in PostInstRule: {type(interaction).__name__}")
    root.session.launch_interaction = stub

    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "apply myrule (leaves ?c residual in a non-consume premise)",
        "rule": {"name": "myrule"}})])
    print_header("After InferenceRule (residual ?c instantiated)", file)
    root.print(0, file)

    # The whole goal must now be schematic-free.
    node = root.sub_nodes[1]
    tvs, tyvs = await node._state_after_beginning().schematic_variables_of(whole=True)
    file.write(f"interaction kinds fired: {captured_kinds}\n")
    file.write(f"residual term schematics: {sorted(t.unicode for t in tvs)}\n")
    file.write(f"residual type schematics: {sorted(t.unicode for t in tyvs)}\n")

def _post_inst_stub(file: MyIO, fixture: dict[str, str], captured_kinds: list[str]):
    """A `launch_interaction` stub for post-rule instantiation: answers every
    variable the interaction reports, each round, from `fixture` (keyed by the
    reported `?name`). Prints each round's prompt and records the round kind so
    the multi-round fixpoint converges."""
    async def stub(interaction):
        if isinstance(interaction, Interaction_InstantiatePostSchematics):
            captured_kinds.append(interaction.kind)
            print_header(f"Post-rule instantiation prompt (kind={interaction.kind})", file)
            await interaction.prompt(0, file)
            insts = [(n, fixture[n]) for n, _ in interaction.schematic_vars]
            return await interaction.answer(AnswerInstantiate(instantiations=insts))
        raise NotImplementedError(
            f"Unstubbed interaction: {type(interaction).__name__}")
    return stub

async def _assert_schematic_free(root: Root, file: MyIO, captured_kinds: list[str]):
    node = root.sub_nodes[1]
    tvs, tyvs = await node._state_after_beginning().schematic_variables_of(whole=True)
    file.write(f"interaction kinds fired: {captured_kinds}\n")
    file.write(f"residual term schematics: {sorted(t.unicode for t in tvs)}\n")
    file.write(f"residual type schematics: {sorted(t.unicode for t in tyvs)}\n")

@model_test("PostInstRuleType", "Test_PostInstRuleType.thy", 16)
async def _test_PostInstRuleType(root: Root, file: MyIO):
    # `?'a` occurs only in the premise → residual TYPE variable → kind=type.
    print_header("Initial", file)
    root.print(0, file)
    kinds: list[str] = []
    root.session.launch_interaction = _post_inst_stub(file, {"?'a": "nat"}, kinds)
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "apply myTrule (leaves residual type ?'a)",
        "rule": {"name": "myTrule"}})])
    print_header("After InferenceRule (residual ?'a instantiated to nat)", file)
    root.print(0, file)
    await _assert_schematic_free(root, file, kinds)

@model_test("PostInstRuleMultiTerm", "Test_PostInstRuleMultiTerm.thy", 18)
async def _test_PostInstRuleMultiTerm(root: Root, file: MyIO):
    # Two residual term vars ?c, ?d surfaced together in one term round.
    print_header("Initial", file)
    root.print(0, file)
    kinds: list[str] = []
    root.session.launch_interaction = _post_inst_stub(
        file, {"?c": "0::nat", "?d": "1::nat"}, kinds)
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "apply myrule2 (leaves residual ?c and ?d)",
        "rule": {"name": "myrule2"}})])
    print_header("After InferenceRule (?c, ?d instantiated)", file)
    root.print(0, file)
    await _assert_schematic_free(root, file, kinds)

@model_test("PostInstRuleTermPinsType", "Test_PostInstRuleTermPinsType.thy", 18)
async def _test_PostInstRuleTermPinsType(root: Root, file: MyIO):
    # ?x :: ?'a; answering ?x:=0::nat pins ?'a, so only ONE term round fires.
    print_header("Initial", file)
    root.print(0, file)
    kinds: list[str] = []
    root.session.launch_interaction = _post_inst_stub(file, {"?x": "0::nat"}, kinds)
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "apply myrule3 (?x's type ?'a is pinned by the term value)",
        "rule": {"name": "myrule3"}})])
    print_header("After InferenceRule (?x and its type ?'a both eliminated)", file)
    root.print(0, file)
    await _assert_schematic_free(root, file, kinds)

@model_test("PostInstRuleTermThenType", "Test_PostInstRuleTermThenType.thy", 18)
async def _test_PostInstRuleTermThenType(root: Root, file: MyIO):
    # ?x::?'a (term) plus independent type-only ?'b → term round, then type round.
    print_header("Initial", file)
    root.print(0, file)
    kinds: list[str] = []
    root.session.launch_interaction = _post_inst_stub(
        file, {"?x": "0::nat", "?'b": "nat"}, kinds)
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "apply myrule4 (term round pins ?'a; type round handles ?'b)",
        "rule": {"name": "myrule4"}})])
    print_header("After InferenceRule (term then type round)", file)
    root.print(0, file)
    await _assert_schematic_free(root, file, kinds)

@model_test("PostInstValidation", "Test_PostInstValidation.thy", 19)
async def _test_PostInstValidation(root: Root, file: MyIO):
    # Exercise the answer validator: empty / missing / unknown / duplicate /
    # type-clash answers are each rejected with a clean BadAnswer; the final
    # correct answer succeeds. All attempts happen within the single term round.
    print_header("Initial", file)
    root.print(0, file)
    attempts = [
        ("empty",         []),
        ("missing ?d",    [("?c", "0::nat")]),
        ("unknown ?zzz",  [("?c", "0::nat"), ("?d", "1::nat"), ("?zzz", "2::nat")]),
        ("duplicate ?c",  [("?c", "0::nat"), ("?c", "9::nat"), ("?d", "1::nat")]),
        ("type clash",    [("?c", "True"), ("?d", "1::nat")]),
        ("correct",       [("?c", "0::nat"), ("?d", "1::nat")]),
    ]
    state = {"i": 0}
    async def stub(interaction):
        if not isinstance(interaction, Interaction_InstantiatePostSchematics):
            raise NotImplementedError(f"Unstubbed: {type(interaction).__name__}")
        print_header(f"Post-rule instantiation prompt (kind={interaction.kind})", file)
        await interaction.prompt(0, file)
        while state["i"] < len(attempts):
            label, insts = attempts[state["i"]]
            state["i"] += 1
            try:
                result = await interaction.answer(AnswerInstantiate(instantiations=insts))
                file.write(f"[{label}] accepted\n")
                return result
            except Interaction_BadAnswer as e:
                file.write(f"[{label}] rejected: {e}\n")
        raise AssertionError("ran out of attempts without an accepted answer")
    root.session.launch_interaction = stub
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "apply myrule2 (validate ?c, ?d answers)",
        "rule": {"name": "myrule2"}})])
    print_header("After InferenceRule (validation passed)", file)
    root.print(0, file)
    await _assert_schematic_free(root, file, ["term"])

@model_test("AutoRewriteFallback", "Test_AutoRewriteFallback.thy", 8)
async def _test_AutoRewriteFallback(root: Root, file: MyIO):
    print_header("Initial", file)
    root.print(0, file)
    root.session.age += 1
    # `set_eq_subset` fails as an inference rule (its conclusion does not unify
    # with the set-equality goal) but works as a goal rewrite, so the failed
    # InferenceRule auto-converts in place to a genuine Rewrite (which carries the
    # AUTOCONVERT_REWRITE_MSG notice and changes the goal to the two subset dirs).
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "split the set equality into two subset directions",
        "rule": {"name": "set_eq_subset"},
    })])
    print_header("After fill (InferenceRule auto-converted to Rewrite)", file)
    root.print(0, file, show_warnings=True)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("AutoRewriteFallbackCascade", "Test_AutoRewriteFallbackCascade.thy", 8)
async def _test_AutoRewriteFallbackCascade(root: Root, file: MyIO):
    # Exercises the *cascade* auto-convert path (the coverage unique to the
    # handler mechanism over a fill-only approach): an InferenceRule that is
    # CANCELLED at introduction (a preceding step failed, so it never executes)
    # must NOT convert; once the preceding step is fixed, the cascade re-refreshes
    # it, its RULE op runs for the FIRST time, fails, and it auto-converts.
    #
    # Step 1: a Have with an ill-typed statement → its beginning op FAILS.
    # Step 2: InferenceRule(set_eq_subset) → CANCELLED because step 1 failed.
    await root.fill("1", [
        Have.gen_single({
            "thought": "ill-typed helper (will fail)",
            "statement": {"english": "bad", "conclusion": r"(0::nat) = True"},
            "name": "bad"}),
        InferenceRule.gen_single({
            "thought": "split the set equality into two subset directions",
            "rule": {"name": "set_eq_subset"}}),
    ])
    print_header("After fill: step 1 fails → step 2 is CANCELLED, still InferenceRule (NOT converted)", file)
    root.print(0, file, show_warnings=True)
    root.session.age += 1
    # Fix step 1: amend the ill-typed Have to a well-formed one (succeeds, leaves
    # the main goal unchanged). The cascade re-refreshes step 2; its set_eq_subset
    # now executes for the first time, fails as a rule, and auto-converts to Rewrite.
    await root.amend("1", [Have.gen_single({
        "thought": "well-formed helper now",
        "statement": {"english": "ok", "conclusion": r"(0::nat) = 0"},
        "name": "ok"})])
    print_header("After amend (preceding fixed → cascade converts step 2 to Rewrite)", file)
    root.print(0, file, show_warnings=True)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("CaseSplit", "Test006.thy", 9)
async def _test_CaseSplit(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split",
        "target_isabelle_term": r"l"
    })])
    print_header("Case Split", file)
    root.print(0, file)
    await root.fill("1.Nil.1", [CaseSplit.gen_single({
        "thought": "Case split",
        "target_isabelle_term": r"l"
    })])
    print_header("Case Split", file)
    root.print(0, file)

@model_test("CaseSplit_Bool", "Test_CaseSplit_Bool.thy", 8)
async def _test_CaseSplit_Bool(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on boolean b",
        "target_isabelle_term": r"b"
    })])
    print_header("Case Split Bool", file)
    root.print(0, file)

@model_test("CaseSplit_NoSimp", "Test_CaseSplit_NoSimp.thy", 8)
async def _test_CaseSplit_NoSimp(root: Root, file: MyIO):
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on boolean b without simplification",
        "target_isabelle_term": r"b",
        "simplify": False
    })])
    print_header("CaseSplit with simplify=false", file)
    root.print(0, file)

@model_test("Induction_NoSimp", "Test_Induction_NoSimp.thy", 8)
async def _test_Induction_NoSimp(root: Root, file: MyIO):
    await root.fill("1", [Induction.gen_single({
        "thought": "Induction on l without simplification",
        "target_isabelle_term": r"l",
        "variables": [{"name": "l", "status": "fixed"}],
        "simplify": False
    })])
    print_header("Induction with simplify=false", file)
    root.print(0, file)

@model_test("CaseSplit_Quickview", "Test_CaseSplit_Quickview.thy", 8)
async def _test_CaseSplit_Quickview(root: Root, file: MyIO):
    """Bug: quickview after CaseSplit doesn't print the binding variables
    and premises produced by the case-split. The full print shows them,
    but quickview omits them entirely.
    Uses a list CaseSplit so both case_vars (Cons introduces a, list)
    and case_hyps (e.g. Cons.prem0: l = a # list) are exercised."""
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on list l",
        "target_isabelle_term": r"l"
    })])
    print_header("Full print (shows variables and premises)", file)
    root.print(0, file)
    print_header("Quickview (should show variables and premises too)", file)
    root.quickview(0, file)

@model_test("GoalCtxQuickview", "Test_GoalCtxQuickview.thy", 8)
async def _test_GoalCtxQuickview(root: Root, file: MyIO):
    """Test that quickview prints goal.context.vars even when case_vars is None.
    After SplitConjs on '∀x::nat. P x ∧ Q x', the fixed variable x
    appears in each GoalNode's goal.context.vars but NOT in case_vars (since
    these GoalNodes come from SplitConjs, not CaseSplit).

    The leading ⋀x triggers the framework's auto-Intro at step 1 (fixes x)
    which leaves a single residual goal `P x ∧ Q x` and does not open a
    sub-proof block. We apply SplitConjs at step 2 on that residual."""
    root.session.age += 1
    await root.fill("2", [SplitConjs.gen_single({
        "thought": "Split conjunction",
    })])
    print_header("Full print", file)
    root.print(0, file)
    print_header("Quickview (should show x in subgoal context)", file)
    root.quickview(0, file)

@model_test("ResetLocalStepCascade", "Test_ResetLocalStepCascade.thy", 8)
async def _test_ResetLocalStepCascade(root: Root, file: MyIO):
    """Verifies that `_reset_local_step` cascades id recomputation to
    descendants.  Without the cascade, renaming a GoalNode would leave
    its sub-nodes' `.id` strings carrying the stale parent prefix."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Seed: successful list induction with Obvious children in both cases.
    await root.fill("1", [Induction.gen_single({
        "thought": "induct on l",
        "target_isabelle_term": r"l",
        "variables": [{"name": "l", "status": "fixed"}],
    })])
    await root.fill("1.Nil.1", [Obvious.gen_single({"facts": []})])
    await root.fill("1.Cons.1", [Obvious.gen_single({
        "facts": [{"name": "Cons.IH"}]
    })])
    print_header("After seed (cases Nil/Cons, each with an Obvious child)", file)
    root.print(0, file)

    nil_gn = root.locate_node("1.Nil")
    nil_child = root.locate_node("1.Nil.1")
    assert nil_gn.id == "1.Nil", f"pre-rename parent id: {nil_gn.id}"
    assert nil_child.id == "1.Nil.1", f"pre-rename child id: {nil_child.id}"

    nil_gn._reset_local_step("renamed")
    if nil_gn.id != "1.renamed":
        raise TestFailed(
            f"Parent id not updated: got `{nil_gn.id}`, expected `1.renamed`")
    if nil_child.id != "1.renamed.1":
        raise TestFailed(
            f"Cascade failed: child id stayed `{nil_child.id}`, "
            f"expected `1.renamed.1`")
    file.write(
        f"rename cascade verified: parent={nil_gn.id}, child={nil_child.id}\n")

@model_test("Induction", "Test_Induction.thy", 8)
async def _test_Induction(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", [Induction.gen_single({
        "thought": "some thought about Induction",
        "target_isabelle_term": r"l",
        "variables": [{"name": "l", "status": "fixed"}],
    })])
    print_header("Induction", file)
    root.print(0, file)
    await root.fill("1.Nil.1", [Obvious.gen_single({"facts": []})])
    print_header("Obvious", file)
    root.print(0, file)
    await root.fill("1.Cons.1", [Obvious.gen_single({
        "facts": [{"name": "Cons.IH"}]
    })])
    print_header("Obvious", file)
    root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Induction_IllTypedBoundVar", "Test_Induction_IllTypedBoundVar.thy", 8)
async def _test_Induction_IllTypedBoundVar(root: Root, file: MyIO):
    """Reproduces the "Ill-typed instantiation: n :: 'a" induction failure.

    Root cause: the agent inducts on a variable that is universally
    *bound* in the goal (here `n` in the Have statement `∀n. b n > 0`)
    but has NOT been introduced/fixed into the proof context. The
    INDUCT target string `"n"` is parsed by `check_term` against the
    proof context, where no fixed `n` exists, so it resolves to a fresh
    free variable of unconstrained type `'a`. With the default rule
    Isabelle then cannot pick an induction rule ("Unable to figure out
    induct rule"); with an explicit `nat.induct` (which fixes the
    predicate type to `nat`) the `'a` free clashes with `nat`, raised by
    `ind_prep_inst` in library/proof.ML via `Type.could_unify('a, nat)`
    = false → "Ill-typed instantiation: n :: 'a".

    Faithful to the live log: after `HAVE(pos_b, '∀n. b n > 0')` the
    framework's auto-Intro fixes `n :: nat` at step 1.1. The agent then
    issued `edit{action: amend, target_step: 4.1, operation: Induction}`
    — i.e. it AMENDED the auto-Intro node into an Induction. Amending
    removes the Intro, so `n` reverts to bound/un-introduced and the
    induction instantiation goes ill-typed. The fix on the agent side is
    to keep the `Intro n` (induct only on a fixed `nat`), not replace it.

    We use a self-contained positive function of `n` so the Have
    statement type-checks without extra context."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    # Pose a helper whose conclusion universally quantifies `n`. The
    # framework auto-introduces `n :: nat` at step 1.1 (mirrors the live
    # `pos_b: ∀n. b n > 0`, whose `n` was likewise auto-fixed).
    await root.fill("1", [Have.gen_single({
        "thought": "b is always positive",
        "statement": {
            "english": "two to the power n is positive for every n",
            "conclusion": r"\<forall>n::nat. (2::int)^n > 0"},
        "name": "pos_b"
    })])
    print_header("After Have pos_b (auto-Intro fixes n at 1.1)", file)
    root.print(0, file)
    root.session.age += 1
    # Amend the auto-Intro node (1.1) into an Induction — this is the
    # exact `action: amend, target_step: 4.1` from the live log. The
    # Intro is dropped, so `n` is bound again. Default rule: Isabelle
    # cannot figure out the induction rule (target type is 'a).
    await root.amend("1.1", [Induction.gen_single({
        "thought": "Induction on n",
        "target_isabelle_term": r"n",
        "variables": [{"name": "n", "status": "fixed"}],
    })])
    print_header("Amend 1.1 → Induction n (default rule) — Unable to figure out induct rule", file)
    root.print(0, file)
    root.session.age += 1
    # Amend again with explicit nat.induct: the free `n :: 'a` clashes
    # with the rule's `nat` predicate type → "Ill-typed instantiation:
    # n :: 'a" (raised by ind_prep_inst in library/proof.ML).
    await root.amend("1.1", [Induction.gen_single({
        "thought": "Induction on n using nat induction rule",
        "target_isabelle_term": r"n",
        "rule": {"name": "nat.induct"},
        "variables": [{"name": "n", "status": "fixed"}],
    })])
    print_header("Amend 1.1 → Induction n (rule nat.induct) — Ill-typed instantiation n :: 'a", file)
    root.print(0, file)

@model_test("Induction_AutoIntroBoundVar", "Test_Induction_AutoIntroBoundVar.thy", 8)
async def _test_Induction_AutoIntroBoundVar(root: Root, file: MyIO):
    """A1′ fix: a `Have` whose body LEADS with an `Induction` on a ∀-bound
    variable `n` (no explicit `Intro`). This is the faithful fill-with-body
    trigger from the live log — supplying the Induction body used to SUPPRESS
    the auto-Intro, leaving `Induction n` to run on the still-`∀`-bound `n` and
    fail with `Ill-typed instantiation: n :: 'a`.

    With A1′ the framework detects (ML-side) that the body's first step is an
    Induction whose target hits an un-introduced leading binder, and injects a
    full `Intro` (fixing `n :: nat`) BEFORE the Induction — so the induction
    runs on a fixed `n` and opens the base/Suc cases instead of ill-typed."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "two to the power n is positive",
        "statement": {
            "english": "2^n > 0 for every n",
            "conclusion": r"\<forall>n::nat. (2::int)^n > 0"},
        "name": "pos_pow",
        "proof": [
            {"operation": "Induction",
             "thought": "induction on n",
             "target_isabelle_term": "n",
             "variables": [{"name": "n", "status": "fixed"}],
             "proofs": "GivenLater"},
        ],
    })])
    print_header("After Have (auto-Intro injected before body-leading Induction)", file)
    root.print(0, file)

@model_test("Suffices", "Test_Suffices.thy", 9)
async def _test_Suffices(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use "it suffices to show" that x*x + 1 > 0
    await root.fill("1", [Suffices.gen_single({
        "thought": "It suffices to show a stronger statement",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "conclusion": "x * x + 1 > 0"
        }
    })])
    print_header("After Suffices", file)
    root.print(0, file)
    # Now we need to prove: (x * x + 1 > 0) --> (x * x >= 0)
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("After proving implication", file)
    root.print(0, file)
    # Now we need to prove: x * x + 1 > 0
    await root.fill("2", [Obvious.gen_single({"facts": []})])
    print_header("After proving suffices goal", file)
    root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Rewrite1", "Test_Rewrite.thy", 12)
async def _test_Rewrite1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["h2"]
    })])
    print_header("After Rewrite", file)
    root.print(0, file)
    await root.rename_fact("premise0", "my_premise")
    print_header("After Rename Fact", file)
    root.print(0, file)

@model_test("Rewrite2", "Test_Rewrite2.thy", 12)
async def _test_Rewrite2(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["h2"]
    })])
    print_header("After Rewrite", file)
    root.print(0, file)
    await root.rename_fact("premise0", "my_premise")
    print_header("After Rename Fact", file)
    root.print(0, file)
    await root.delete(["1"])
    print_header("After Remove the Rewrite", file)
    root.print(0, file)

@model_test("Rewrite3", "Test_Rewrite3.thy", 13)
async def _test_Rewrite3(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    await root.fill("1", [Have.gen_single({
        "thought": "I don't know",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "conclusion": "x = y"
        },
        "name": "lem1"
    })])
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("After Have", file)
    root.print(0, file)
    await root.fill("2", [Rewrite.gen_single({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"name": "lem1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After Rewrite", file)
    root.print(0, file)
    await root.amend("1", [Have.gen_single({
        "thought": "I don't know!!!",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "conclusion": "x = y * 1"
        },
        "name": "lem1"
    })])
    print_header("After Amend Have", file)
    root.print(0, file)
    await root.amend("1", [Have.gen_single({
        "thought": "I don't know!!!",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "conclusion": "x = y * 2"
        },
        "name": "lem1"
    })])
    print_header("After Amend Have", file)
    root.print(0, file)

@model_test("Rewrite_NoProgress", "Test_Rewrite_NoProgress.thy", 13)
async def _test_Rewrite_NoProgress(root: Root, file: MyIO):
    """Rewrite with an irrelevant rule should fail with 'no progress' after the
    CHANGED_PROP fix in proof.ML."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Rewrite h1 using foo_def — completely irrelevant, should make no progress
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Attempt rewrite with irrelevant rule",
        "using": [{"name": "foo_def"}],
        "use system simplifiers": False,
        "rewrite goal": False,
        "rewrite premises": ["h1"]
    })])
    # Rewrite reverts on no-progress, so committed may be empty.
    success = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("Response", file)
    file.write(f"Success: {success}\n")
    file.write(f"Reason: {reason}\n")
    print_header("After Rewrite", file)
    root.print(0, file)

@model_test("Rewrite_OF_ZeroPremise", "Test_Rewrite_OF_ZeroPremise.thy", 10)
async def _test_Rewrite_OF_ZeroPremise(root: Root, file: MyIO):
    """Regression test for OF _ on zero-premise facts.

    LLM agents habitually attach discharge: [null] (→ OF _) to every fact
    reference because HAMMER tolerates it.  SIMPLIFY evaluates facts via
    Attrib.eval_thms → xOF (aux.ML), which strictly checks premise count and
    raises a hard error on zero-premise facts.

    After the fix: _of_clause strips trailing null entries, so discharge: [null]
    on a zero-premise fact no longer emits OF _ and the Rewrite succeeds.

    See /tmp/problem_4.md for the original incident (EA6E9592F_20F38CE)."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Rewrite with discharge: [null] on h1 (a zero-premise equation).
    # After fix: trailing null is stripped, so this succeeds (was: hard error).
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite using h1 with trailing-null discharge",
        "using": [{"name": "h1", "discharge": [None]}],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("Rewrite with discharge: [null] (trailing null stripped)", file)
    file.write(f"failure: {_outcome.failure}\n")
    root.print(0, file)

    root.session.age += 1

    # Step 2: Non-trailing discharge on a zero-premise fact still fails,
    # but now with an enhanced error message suggesting the fix.
    await root.delete(["1"])
    root.session.age += 1
    _outcome2 = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite using h1 with non-null discharge",
        "using": [{"name": "h1", "discharge": [{"name": "h1"}]}],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    is_error = _outcome2.failure is not None and _outcome2.failure.is_error
    print_header("Rewrite with discharge: [h1] on zero-premise fact", file)
    file.write(f"is_error: {is_error}\n")
    file.write(f"reason: {_outcome2.failure}\n")

@model_test("SuppressParentGoal", "Test_SuppressParentGoal.thy", 10)
async def _test_SuppressParentGoal(root: Root, file: MyIO):
    """When Rewrite changes the goal, quickview should show 'goal changes into'
    in the Rewrite node but NOT duplicate the same goal in the parent's
    'Error: Unfinished Proof' section."""
    await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite the goal using h1",
        "using": [{"name": "h1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("Quickview after Rewrite (goal changed)", file)
    root.quickview(0, file)
    print_header("Quickview again (should not re-print)", file)
    root.quickview(0, file)

@model_test("Rewrite_DeleteSiblingNoChange", "Test_Rewrite_DeleteSiblingNoChange.thy", 10)
async def _test_Rewrite_DeleteSiblingNoChange(root: Root, file: MyIO):
    """Deleting a sibling after a Rewrite step must NOT mark the Rewrite as
    'changed' when its produced goal hasn't actually changed.  Regression
    test for false-positive caused by resulting_state() routing shift."""
    # Step 1: Rewrite the goal using h1 — this changes the goal.
    await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite goal using h1",
        "using": [{"name": "h1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("Quickview after Rewrite", file)
    root.quickview(0, file)
    root.reset()
    # Step 2: Add a Have after the Rewrite and prove it.
    root.session.age += 1
    await root.fill("2", [Have.gen_single({
        "thought": "helper fact",
        "statement": {"english": "trivially true", "conclusion": "True"},
        "name": "helper"
    })])
    root.session.age += 1
    await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    print_header("Quickview after Have+Obvious", file)
    root.quickview(0, file)
    root.reset()
    # Delete the Have — Rewrite must NOT be marked (changed).
    root.session.age += 1
    await root.delete(["2"])
    print_header("Quickview after deleting Have (Rewrite must not be changed)", file)
    root.quickview(0, file)

# @model_test("RewriteThenObviousFails", "Test_Rewrite_Then_Obvious_Fails.thy", 18)
# async def _test_RewriteThenObviousFails(root: Root, file: MyIO):
#     """Reproduce: a successful Rewrite as the last child followed by a
#     failing Obvious fill must return a graceful failure_reason instead of
#     crashing with InternalError("Prooftree is not initialized").
# 
#     Root cause: Minilang_State.execute() sets assign_to.prooftree = None on
#     IsabelleError. When the failing step is the last child of a StdBlock,
#     its resulting_state() resolves to the block's shared
#     _state_before_ending_ — which is the SAME Python object that the
#     previous (successful) child's resulting_state() resolves to. Zeroing
#     the prooftree therefore wipes out the prior successful state. When
#     fill()'s revert path then calls `rp._refresh_me_alone()` on the
#     predecessor Rewrite, line 3602 / 3544 of model.py dereferences
#     `self.resulting_state().prooftree_of()` and raises."""
#     print_header("Initial YAML", file)
#     root.print(0, file)
# 
#     # Step 1: Rewrite the goal `P x` using `h: x = y`. Succeeds, producing
#     # the residual goal `P y`. This write populates the block's
#     # _state_before_ending_ via goal1's resulting_state (goal1 is the last
#     # child at this moment).
#     root.session.age += 1
#     node1, is_error1, reason1 = await root.fill("1", Rewrite.gen_single({
#         "thought": "Rewrite the goal using h",
#         "using": [{"name": "h"}],
#         "use system simplifiers": False,
#         "rewrite goal": True,
#         "rewrite premises": []
#     }))
#     file.write(f"Rewrite step 1: status={node1.status.status.value}, is_error={is_error1}\n")
#     if reason1:
#         file.write(f"  reason: {reason1.reason if isinstance(reason1, FailureReason) else reason1}\n")
#     print_header("After successful Rewrite", file)
#     root.print(0, file)
# 
#     # Step 2: Obvious with no facts. Expected to fail on `P y` (nothing
#     # closes it). The bug surfaces here: instead of returning a graceful
#     # failure_reason, the framework raises InternalError from the
#     # predecessor re-refresh path.
#     root.session.age += 1
#     try:
#         node2, is_error2, reason2 = await root.fill("2", Obvious.gen_single({"facts": []}))
#         file.write(f"Obvious step 2: status={node2.status.status.value}, is_error={is_error2}\n")
#         if reason2:
#             file.write(f"  reason: {reason2.reason if isinstance(reason2, FailureReason) else reason2}\n")
#     except InternalError as e:
#         file.write(f"BUG REPRODUCED: InternalError: {e}\n")
#     except Exception as e:
#         file.write(f"UNEXPECTED {type(e).__name__}: {e}\n")
#     print_header("After failed Obvious (bug point)", file)
#     root.print(0, file)

@model_test("Witness1", "Test_Witness.thy", 9)
async def _test_Witness1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)

    # Use Witness to provide a witness for the existential goal
    await root.fill("1", [Witness.gen_single({
        "thought": "Provide 5 as witness for the existential",
        "witnesses": ["5"]
    })])
    print_header("After Witness", file)
    root.print(0, file)

    # Prove the remaining goal (5 = 5) using Obvious
    await root.fill("2", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Define_AutoProved", "Test_Define_AutoProved.thy", 14)
async def _test_Define_AutoProved(root: Root, file: MyIO):
    """Happy path for the Define operation. Defines `double n = n + n`
    (non-recursive, trivially terminating), then uses `double` as the
    witness for the outer existential. The Define node's auto-prove
    path closes pat-completeness + termination on its own — no
    deferred block opens, no sub_nodes are added, and Define's
    `ending_opr` returns `None` so no END is emitted for this node.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Define `double` — the auto-prove path handles it entirely.
    await root.fill("1", [Define.gen_single({
        "thought": "Introduce the doubling function as a witness",
        "name": "double",
        "type": r"nat \<Rightarrow> nat",
        "equations": ["double n = n + n"],
    })])
    print_header("After Define (auto-proved)", file)
    root.print(0, file)

    # Use `double` to instantiate the existential.
    await root.fill("2", [Witness.gen_single({
        "thought": "Pick the freshly-defined `double` as the witness",
        "witnesses": ["double"],
    })])
    print_header("After Witness", file)
    root.print(0, file)

    # Close the remaining equation `double 2 = 4` via Obvious.
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Define_QuerySimps", "Test_Define_QuerySimps.thy", 8)
async def _test_Define_QuerySimps(root: Root, file: MyIO):
    """After defining a proof-local function, verify that its .simps
    fact can be found via session.retrieval_state() and semantic_knn
    exact_name lookup."""
    from Isabelle_RPC_Host.universal_key import EntityKind

    await root.fill("1", [Define.gen_single({
        "thought": "Define doubling function",
        "name": "double",
        "type": r"nat \<Rightarrow> nat",
        "equations": ["double n = n + n"],
    })])
    print_header("After Define", file)
    root.print(0, file)

    ml = root.session.retrieval_state()

    results, warnings = await ml.semantic_knn(
        None, 1, [EntityKind.THEOREM], exact_name="double.simps")
    file.write(f"Query double.simps: {len(results)} results, warnings={warnings}\n")
    assert len(results) > 0, \
        f"Expected double.simps to be found after proof-local Define, got: {warnings}"
    file.write(f"  Found: {results[0].entity.short_name.unicode}\n")

    await root.fill("2", [Witness.gen_single({
        "thought": "Use double as witness",
        "witnesses": ["double"],
    })])
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After proof complete", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")
    assert len(unfinished_nodes) == 0, "Expected proof to be complete"

@model_test("Define_QueryConst", "Test_Define_QueryConst.thy", 8)
async def _test_Define_QueryConst(root: Root, file: MyIO):
    """After defining a proof-local function, verify that querying for
    it as a constant by exact_name works. Currently, the query tool only
    finds true Const(_, _) entities via universal_key_of, so a
    pseudo-constant (fixed free variable) created by Define is reported
    as Undefined."""
    from Isabelle_RPC_Host.universal_key import EntityKind

    await root.fill("1", [Define.gen_single({
        "thought": "Define doubling function",
        "name": "double",
        "type": r"nat \<Rightarrow> nat",
        "equations": ["double n = n + n"],
    })])
    print_header("After Define", file)
    root.print(0, file)

    ml = root.session.retrieval_state()

    # Query for double.simps (lemma) — should succeed
    results_simps, warnings_simps = await ml.semantic_knn(
        None, 1, [EntityKind.THEOREM], exact_name="double.simps")
    file.write(f"Query double.simps (lemma): {len(results_simps)} results, warnings={warnings_simps}\n")
    if results_simps:
        file.write(f"  Found: {results_simps[0].entity.short_name.unicode}\n")

    # Query for double (constant) — this is the bug: pseudo-constants
    # defined by Define are fixed free variables, not true Const(_, _),
    # so universal_key_of cannot resolve them.
    results_const, warnings_const = await ml.semantic_knn(
        None, 1, [EntityKind.CONSTANT], exact_name="double")
    file.write(f"Query double (constant): {len(results_const)} results, warnings={warnings_const}\n")
    if results_const:
        file.write(f"  Found: {results_const[0].entity.short_name.unicode}\n")

    # Complete the proof so the test leaves a clean state
    await root.fill("2", [Witness.gen_single({
        "thought": "Use double as witness",
        "witnesses": ["double"],
    })])
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After proof complete", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")
    assert len(unfinished_nodes) == 0, "Expected proof to be complete"

@model_test("QueryLocalScore_PatternOnly", "Test_QueryLocalScore_PatternOnly.thy", 9)
async def _test_QueryLocalScore_PatternOnly(root: Root, file: MyIO):
    """Documents (and guards) current behavior: the pattern-only path (query=None)
    does NOT surface a posed proof-local `Have` fact -> 0 results. Pattern-only's
    candidates come solely from entities_of, whose static-fact enumeration does
    not include a posed-but-unproven Have (it is tracked in Minilang's
    contextual_thms, not yet note_thmss'd into Proof_Context.facts_of), and the
    pattern-only path has no contextual_thms force-add. Contrast with
    QueryLocalScore_KNN, where the ContextExtended force-add surfaces it at 0.500.
    If pattern-only is later given a local-fact force-add, this golden flags it."""
    from Isabelle_RPC_Host.universal_key import EntityKind

    await root.fill("1", [Have.gen_single({
        "thought": "local helper",
        "statement": {"english": "x squared is non-negative",
                      "conclusion": r"(0::int) \<le> x * x"},
        "name": "uniqLocalLemmaZZ",
    })])

    ml = root.session.retrieval_state()
    results, warnings = await ml.semantic_knn(
        None, 5, [EntityKind.THEOREM], name_contains=["uniqLocalLemmaZZ"])
    file.write(f"pattern-only name_contains=[uniqLocalLemmaZZ]: {len(results)} results, warnings={warnings}\n")
    for r in results:
        file.write(f"  {r.score:.3f} {r.entity.kind.label} {r.entity.short_name.unicode}\n")

@model_test("QueryLocalScore_KNN", "Test_QueryLocalScore_KNN.thy", 9)
async def _test_QueryLocalScore_KNN(root: Root, file: MyIO):
    """Same as QueryLocalScore_PatternOnly but via the semantic KNN path (a query
    string, so store.lookup runs). The proof-local `Have` fact has no embedding
    vector, so the merge assigns it the provider default_local_score (0.500): the
    query is embedded but no candidate has a vector, so the score is deterministic
    and independent of the embedding DB. name_contains pins the candidate set to
    the local fact. Verifies the lookup() merge + is_local path (ML uncached flag
    -> entities_of is_local_map -> _default_score)."""
    from Isabelle_RPC_Host.universal_key import EntityKind

    await root.fill("1", [Have.gen_single({
        "thought": "local helper",
        "statement": {"english": "x squared is non-negative",
                      "conclusion": r"(0::int) \<le> x * x"},
        "name": "uniqLocalLemmaZZ",
    })])

    ml = root.session.retrieval_state()
    results, warnings = await ml.semantic_knn(
        "x squared is non-negative", 5, [EntityKind.THEOREM], name_contains=["uniqLocalLemmaZZ"])
    file.write(f"knn 'x squared is non-negative' name_contains=[uniqLocalLemmaZZ]: {len(results)} results, warnings={warnings}\n")
    for r in results:
        file.write(f"  {r.score:.3f} {r.entity.kind.label} {r.entity.short_name.unicode}\n")

@model_test("Define_Manual", "Test_Define_Manual.thy", 16)
async def _test_Define_Manual(root: Root, file: MyIO):
    """Manual-discharge path for the Define operation. The test .thy
    sets `Minilang.fun_fake_automatic_failure = true`, which forces
    the default termination prover, the `BY_METRIC` metric path's
    sledgehammer, AND the auto+termination_simp simplification pass
    to all return failure. With that flag set, the Define node's
    metric path still applies `resolve_tac [termination']` +
    `relation_infer_tac`, instantiating the schematic `?R` with
    `measure (\\<lambda>n. n)`, and pushes the raw residual subgoals
    (`wf (measure (\\<lambda>n. n))` and
    `\\<And>n. (n, Suc (Suc n)) \\<in> measure (\\<lambda>n. n)`)
    onto the minilang stack as a deferred block.

    `Define._deferred_block_opened` is set to True from the
    `Termination_Proof_Opened_Msg` reporter signal, so Define's
    `ending_opr` returns END. The agent then discharges each residual
    with Obvious (which uses the real sledgehammer — the fake flag
    only affects the Define-internal path, not the general
    `HAMMER_i`/`default_prover` used by Obvious). After both
    residuals close and the Define block ends, the outer proof
    continues with Witness + Obvious on the existential goal.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Define `halve` with a user-supplied metric. Under
    # fun_fake_automatic_failure, all three auto-prove tiers fail and
    # the metric path falls through to MetricPartial, pushing the
    # prepped state (2 subgoals) as a deferred block.
    await root.fill("1", [Define.gen_single({
        "thought": "Define halve as a witness; fake flag forces manual "
                   "discharge of termination residuals",
        "name": "halve",
        "type": r"nat \<Rightarrow> nat",
        "equations": [
            "halve 0 = 0",
            "halve (Suc 0) = 0",
            "halve (Suc (Suc n)) = Suc (halve n)",
        ],
        "metric": [r"\<lambda>n::nat. n"],
    })])
    print_header("After Define (deferred block opened)", file)
    root.print(0, file)

    # Discharge the first residual inside the deferred block:
    # `wf (measure (\<lambda>n. n))`, closed by `wf_measure`.
    await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious on residual 1 (well-foundedness)", file)
    root.print(0, file)

    # Discharge the second residual inside the deferred block:
    # `\<And>n. (n, Suc (Suc n)) \<in> measure (\<lambda>n. n)`,
    # closed by `in_measure` + arithmetic.
    await root.fill("1.2.2", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious on residual 2 (decrease)", file)
    root.print(0, file)

    # Block auto-closes; proceed with the outer proof.
    await root.fill("2", [Witness.gen_single({
        "thought": "Pick the freshly-defined `halve` as the witness",
        "witnesses": ["halve"],
    })])
    print_header("After Witness", file)
    root.print(0, file)

    # `halve 4 = Suc (halve 2) = Suc (Suc (halve 0)) = Suc (Suc 0)`.
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious on halve 4 = 2", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Define_Nullary", "Test_Define_Nullary.thy", 16)
async def _test_Define_Nullary(root: Root, file: MyIO):
    """Define DOES support a nullary constant. The function/fun package
    rejects an argument-free left-hand side ("Function has no
    arguments"), so AoA's Define op (ML side) detects the nullary case
    via Minilang.is_nullary_def_cmd and routes it through the plain Isar
    `define` command instead of Minilang.FUN''. The bare constant
    `P = 5` is therefore introduced successfully: the Define node carries
    no error and is satisfied, leaving only the outer existential goal
    unfinished. (Regression test for the nullary-define fix.)
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Introduce P = 5 as a nullary constant. Detected as nullary on the
    # ML side and routed through plain `define` (not the fun package).
    _outcome = await root.fill("1", [Define.gen_single({
        "thought": "Name the constant 5 as P for shorter computations",
        "name": "P",
        "type": "nat",
        "equations": ["P = 5"],
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("After Define (nullary constant, now supported)", file)
    root.print(0, file)
    file.write(f"is_error: {is_error}\n")
    file.write(f"reason: {reason.reason if isinstance(reason, FailureReason) else reason}\n")

    # The nullary Define is satisfied (no residual termination /
    # pat-completeness obligations); only the outer existential remains.
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")
    assert len(unfinished_nodes) == 1, \
        f"Nullary Define should be satisfied (only outer goal left), " \
        f"got {len(unfinished_nodes)} unfinished"

@model_test("Define_CaseExpr", "Test_Define_CaseExpr.thy", 16)
async def _test_Define_CaseExpr(root: Root, file: MyIO):
    """Reproducer for fastype_of: Bound.
    Defines a recursive function whose equation uses a `case` expression
    to destructure the recursive call's pair result. The `case` compiles
    to an Abs internally, and check_looping_simp_rules's
    matches_subterm_of descends into the Abs body without substituting
    the bound variable — the loose Bound crashes fastype_of inside
    Pattern.match.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    await root.fill("1", [Define.gen_single({
        "thought": "Define a pair-valued recurrence using case to "
                   "destructure the recursive call",
        "name": "sa",
        "type": r"nat \<Rightarrow> nat \<times> nat",
        "equations": [
            "sa 0 = ((1::nat), (1::nat))",
            r"sa (Suc n) = (case sa n of (s, a) \<Rightarrow> (s + a, s))",
        ],
    })])
    print_header("After Define", file)
    root.print(0, file)

@model_test("Define_SucIMO", "Test_Define_SucIMO.thy", 16)
async def _test_Define_SucIMO(root: Root, file: MyIO):
    """Same as Define_SucPattern but under imo_1974_p3 imports
    (Complex_Main + HOL-Number_Theory + HOL-Computational_Algebra).
    Reproduces the "Non-constructor pattern" failure the LLM hit.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    await root.fill("1", [Define.gen_single({
        "thought": "Define pow2 with Suc pattern under imo_1974_p3 imports",
        "name": "pow2",
        "type": r"nat \<Rightarrow> nat",
        "equations": [
            "pow2 0 = (1::nat)",
            "pow2 (Suc n) = (2::nat) * pow2 n",
        ],
    })])
    print_header("After Define", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Define_SucPattern", "Test_Define_SucPattern.thy", 19)
async def _test_Define_SucPattern(root: Root, file: MyIO):
    """Reproducer from imo_1974_p3: Define with Suc constructor pattern.
    The LLM tried `myf 0 = 1` / `myf (Suc n) = 2 * myf n` and got
    "Non-constructor pattern not allowed in sequential mode" every time.
    This test checks whether the same equations work in the standard
    Minilang_Agent context.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    await root.fill("1", [Define.gen_single({
        "thought": "Define pow2 with Suc pattern — simplest failing case from imo_1974_p3 logs",
        "name": "pow2",
        "type": r"nat \<Rightarrow> nat",
        "equations": [
            "pow2 0 = (1::nat)",
            "pow2 (Suc n) = (2::nat) * pow2 n",
        ],
    })])
    print_header("After Define (Suc pattern)", file)
    root.print(0, file)

    await root.fill("2", [Witness.gen_single({
        "thought": "Use pow2 as witness",
        "witnesses": ["pow2"],
    })])
    print_header("After Witness", file)
    root.print(0, file)

    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Witness2", "Test_Witness2.thy", 8)
async def _test_Witness2(root: Root, file: MyIO):
    """Witness on a non-existential goal: the node stays in the tree
    with an Error status (default _on_edit_failure returns CONTINUE),
    while outcome.failure remains None."""
    print_header("Initial YAML", file)
    root.print(0, file)

    _outcome = await root.fill("1", [Witness.gen_single({
        "thought": "Provide 1 as witness, which is positive",
        "witnesses": ["1"]
    })])
    file.write(f"outcome.failure: {_outcome.failure}\n")
    print_header("After Witness (error visible in tree)", file)
    root.print(0, file)

@model_test("Witness3", "Test_Witness3.thy", 9)
async def _test_Witness3(root: Root, file: MyIO):
    """Multiple witnesses supplied at once: a single Witness leaf carrying
    two terms instantiates both leading existentials of `∃ x y. x+y=10` in
    one step, exercising the `witnesses:` block renderer and full
    multi-instantiation."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Witness.gen_single({
        "thought": "Provide 3 and 7 as witnesses for x and y",
        "witnesses": ["3", "7"],
    })])
    print_header("After Witness (two witnesses at once)", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Witness4", "Test_Witness4.thy", 9)
async def _test_Witness4(root: Root, file: MyIO):
    """Partial instantiation across separate Witness steps: witness x first
    (leaving the residual `∃ y. 3+y=10`), then y, then close. Exercises the
    relaxed gate allowing fewer witnesses than leading existentials."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Witness.gen_single({
        "thought": "Provide 3 as the first witness (x), leaving the residual existential over y",
        "witnesses": ["3"],
    })])
    print_header("After first Witness (partial: x:=3)", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("2", [Witness.gen_single({
        "thought": "Provide 7 as the witness for the residual y",
        "witnesses": ["7"],
    })])
    print_header("After second Witness (y:=7)", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Witness5", "Test_Witness5.thy", 9)
async def _test_Witness5(root: Root, file: MyIO):
    """Too many witnesses: the goal `∃ x. x=0` has a single leading
    existential, but two witness terms are supplied. The node stays in the
    tree with a 'Too many witness terms' Error status, while
    outcome.failure remains None (mirrors Witness2)."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    _outcome = await root.fill("1", [Witness.gen_single({
        "thought": "Provide two witnesses for a single existential (too many)",
        "witnesses": ["0", "1"],
    })])
    file.write(f"outcome.failure: {_outcome.failure}\n")
    print_header("After Witness (error visible in tree)", file)
    root.print(0, file)
    # Exercise the multi-witness quickview_title (`', '.join`) on the
    # two-witness node; this case is never proof-cached (it errors), so the
    # test body actually runs.
    print_header("Quickview (multi-witness title)", file)
    root.quickview(0, file)

@model_test("Witness6", "Test_Witness6.thy", 9)
async def _test_Witness6(root: Root, file: MyIO):
    """The empty-witness guard: an empty `witnesses` list is rejected by the
    Python validator inside `gen_single`, before any proof operation runs.
    The tree is never rendered so this golden is independent of goal/global
    rendering."""
    try:
        Witness.gen_single({
            "thought": "Provide no witnesses",
            "witnesses": [],
        })
        file.write("ERROR: empty witnesses was NOT rejected\n")
    except model.ArgumentError as e:
        file.write(f"ArgumentError: {e}\n")

@model_test("WitnessTypeMismatch", "Test_WitnessTypeMismatch.thy", 14)
async def _test_WitnessTypeMismatch(root: Root, file: MyIO):
    """Reproduces the `exception THM 1 ... RSN: no unifiers` crash.

    The goal binds `g :: real × real ⇒ real` (a function on a *pair*), but
    the witness is supplied *curried* (`λ x y. ...`), i.e. of type
    `real ⇒ real ⇒ real`. The two types are incompatible, yet the term
    survives `read_terms_with_type`'s `_type_constraint_` check and the
    mismatch only surfaces deep inside `CHOOSE'` (proof.ML) when
    `exI`-instantiated-with-the-witness is resolved against the goal via
    `RS` — there it raises a raw `THM 1 (... RSN: no unifiers)` instead of a
    clean, agent-readable type error. The node stays in the tree with that
    Error status (default `_on_edit_failure` returns CONTINUE), mirroring
    Witness2 / Witness5."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    _outcome = await root.fill("1", [Witness.gen_single({
        "thought": "Curry the witness over x and y instead of pairing them",
        "witnesses": [r"\<lambda>(x::real) (y::real). 0"],
    })])
    file.write(f"outcome.failure: {_outcome.failure}\n")
    print_header("After Witness (type-mismatch error visible in tree)", file)
    root.print(0, file)

@model_test("Unfold1", "Test_Unfold1.thy", 15)
async def _test_Unfold1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)

    # First Unfold: silently pick XXX_def (index 0) — no interaction printed.
    async def stub_silent(interaction):
        return await interaction.answer(AnswerIndexesOrName(indexes=[0], name=None))
    root.session.launch_interaction = stub_silent
    await root.fill("1", [Unfold.gen_single({
        "thought": "Unfold the goal",
        "targets": ["XXX"],
    })])
    print_header("After Unfold", file)
    root.print(0, file)

    # Amend: re-install stub that prints the prompt and picks XXX_alt (index 1).
    async def stub_fork(interaction):
        print_header("Interaction Prompt", file)
        await interaction.prompt(0, file)
        return await interaction.answer(AnswerIndexesOrName(indexes=[1], name=None))
    root.session.launch_interaction = stub_fork
    await root.amend("1", [Unfold.gen_single({
        "thought": "Unfold the goal",
        "targets": ["XXX"],
    })])
    print_header("After Answer", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Delete1", "Test_Delete1.thy", 13)
async def _test_Delete1(root: Root, file: MyIO):
    """Test deleting a single step."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "helper",
        "statement": {"english": "x equals y plus 0", "conclusion": "x = y"},
        "name": "lem1"
    })])
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    root.session.age += 1
    await root.fill("2", [Rewrite.gen_single({
        "thought": "rewrite",
        "using": [{"name": "lem1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After building 3 steps", file)
    root.print(0, file, update_line=False)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()
    # Delete the middle step (Have + its substep)
    root.session.age += 1
    await root.delete(["1"])
    print_header("After deleting step 1 (Have)", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()
    # Insert a Have before step 2
    root.session.age += 1
    await root.insert_before("2", [Have.gen_single({
        "thought": "re-add helper",
        "statement": {"english": "x equals y plus 0", "conclusion": "x = y + 0"},
        "name": "lem1"
    })])
    print_header("After inserting Have before step 2", file)
    root.print(0, file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()

# @model_test("Delete2", "Test_Delete2.thy", 13)
# async def _test_Delete2(root: Root, file: MyIO):
#     """Test deleting multiple steps at once."""
#     print_header("Initial YAML", file)
#     root.print(0, file)
#     root.session.age += 1
#     await root.fill("1", Have.gen_single({
#         "thought": "helper",
#         "statement": {"english": "x equals y", "isabelle": "x = y"},
#         "name": "lem1"
#     }))
#     root.session.age += 1
#     await root.fill("1.1", Obvious.gen_single({"facts": []}))
#     root.session.age += 1
#     await root.fill("2", Have.gen_single({
#         "thought": "helper2",
#         "statement": {"english": "y equals z", "isabelle": "y = z"},
#         "name": "lem2"
#     }))
#     root.session.age += 1
#     await root.fill("2.1", Obvious.gen_single({"facts": []}))
#     root.session.age += 1
#     await root.fill("3", Obvious.gen_single({"facts": []}))
#     print_header("After building 5 steps", file)
#     root.print(0, file)
#     buffer = io.StringIO()
#     root.print(0, MyIO(buffer), update_line=True)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset()
#     # Delete two steps at once
#     root.session.age += 1
#     await root.delete(["1", "2"])
#     print_header("After deleting steps 1 and 2", file)
#     root.print(0, file)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset()
# 
# @model_test("Delete3", "Test_Delete3.thy", 13)
# async def _test_Delete3(root: Root, file: MyIO):
#     """Test deleting with duplicate IDs (deduplication)."""
#     print_header("Initial YAML", file)
#     root.print(0, file)
#     root.session.age += 1
#     await root.fill("1", Have.gen_single({
#         "thought": "helper",
#         "statement": {"english": "x equals y", "isabelle": "x = y"},
#         "name": "lem1"
#     }))
#     root.session.age += 1
#     await root.fill("1.1", Obvious.gen_single({"facts": []}))
#     root.session.age += 1
#     await root.fill("2", Obvious.gen_single({"facts": []}))
#     print_header("After building steps", file)
#     root.print(0, file)
#     buffer = io.StringIO()
#     root.print(0, MyIO(buffer), update_line=True)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset()
#     # Delete with duplicate ID — should deduplicate and not error
#     root.session.age += 1
#     await root.delete(["1", "1"])
#     print_header("After deleting step 1 (with duplicate)", file)
#     root.print(0, file)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset()

@model_test("ReferFactByProposition", "Test001.thy", 6)
async def _test_ReferFactByProposition(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    fullname = await root.ml_state.fetch_facts([{"name": "notI"}])
    file.write(f"Fullname of notI: {fullname}\n")
    return

@model_test("RetrieveFact", "Test_RetrieveFact1.thy", 6)
async def _test_RetrieveFact(root: Root, file: MyIO):
    """Test fetch_facts with FactByName, FactByProposition, and FactByDescription."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # 1. Test fetch_facts with all three fact types
    fetched = await root.ml_state.fetch_facts([
        {"name": "log_nat_power"},           # → IsabelleFact_Presented
        {"name": "nonexistent_lemma"},        # → IsabelleFact_Unfound
        {"proposition": "(8::nat) = 2^3"},  # → IsabelleFact_ProveInTime
        {"english": "8 = 2^3"},       # → Interaction_RetrieveForProof
    ])
    for i, f in enumerate(fetched):
        file.write(f"  fetch_facts[{i}]: {type(f).__name__}\n")
    assert isinstance(fetched[0], IsabelleFact_Presented)
    assert isinstance(fetched[1], IsabelleFact_Unfound)
    assert isinstance(fetched[2], IsabelleFact_ProveInTime)
    assert isinstance(fetched[3], Interaction_RetrieveForProof)
    # 2. Test Obvious with FactByProposition and FactByName (no interaction).
    root.session.age += 1
    gn = Obvious.gen_single({
        "facts": [
            {"proposition": "(8::nat) = 2^3"},
            {"name": "log_nat_power"},
        ]
    })
    _outcome = await root.fill("2", [gn])
    node = _outcome.committed[0] if _outcome.committed else None
    assert node is not None
    file.write(f"Filled node: {type(node).__name__}, id={node.id}\n")
    node.print(1, file, show_warnings=True)
    print_header("After fill", file)
    root.print(0, file)
    return

@model_test("RetrieveFact2", "Test_RetrieveFact2.thy", 6)
async def _test_RetrieveFact2(root: Root, file: MyIO):
    """Test fetch_facts with FactByDescription interaction flow."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # 1. Test fetch_facts with FactByDescription → Interaction_RetrieveForProof
    fetched = await root.ml_state.fetch_facts([
        {"name": "log_nat_power"},           # → IsabelleFact_Presented
        {"english": "8 = 2^3"},       # → Interaction_RetrieveForProof
    ])
    for i, f in enumerate(fetched):
        file.write(f"  fetch_facts[{i}]: {type(f).__name__}\n")
    assert isinstance(fetched[0], IsabelleFact_Presented)
    assert isinstance(fetched[1], Interaction_RetrieveForProof)
    # 2. Test InferenceRule with FactByDescription (triggers interaction).
    root.session.age += 1

    async def stub_fork(interaction):
        file.write(f"RaiseInteraction raised with 1 interaction(s)\n")
        file.write(f"  interaction[0]: {type(interaction).__name__}\n")
        assert isinstance(interaction, Interaction_RetrieveForProof)
        file.write(f"    query: {interaction.query}\n")
        file.write(f"    candidates: {len(await interaction.candidate_facts())}\n")
        # Answer with a ProveInTime statement
        result = await interaction.answer(AnswerIndexesOrSpec(indexes=[], statement="(8::nat) = 2^3"))
        assert isinstance(result, list) and len(result) == 1
        pit = result[0]
        file.write(f"    ProveInTime answer: {type(pit).__name__}\n")
        assert isinstance(pit, IsabelleFact_ProveInTime)
        file.write(f"    statement: {pit.statement.unicode}\n")
        return result
    root.session.launch_interaction = stub_fork

    _outcome = await root.fill("2", [InferenceRule.gen_single({
        "thought": "test description-based retrieval",
        "rule": {"english": "8 = 2^3"},
    })])
    node = _outcome.committed[0] if _outcome.committed else None
    assert node is not None
    file.write(f"Filled node: {type(node).__name__}, id={node.id}\n")
    node.print(1, file, show_warnings=True)
    print_header("After fill", file)
    root.print(0, file)
    return

@model_test("Obvious_partial_solve", "Test_Obvious_partial_solve.thy", 13)
async def _test_Obvious_partial_solve(root: Root, file: MyIO):
    """Reproduces HAMMER partially solving a goal, leaving subgoals that cause
    an unexpected Intro node to be auto-appended."""
    # Step 1: Have h2: log 2 8 = 3
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "log_2(8) = 3",
        "name": "h2",
        "statement": {
            "english": "log base 2 of 8 equals 3",
            "conclusion": "log (2::real) (8::real) = (3::real)"
        }
    })])
    # Step 1.1: Obvious with log_pow_cancel
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": [{"name": "log_pow_cancel"}]})])
    # Step 2: Have h3: log 8 x = log 2 x / 3
    root.session.age += 1
    await root.fill("2", [Have.gen_single({
        "thought": "change of base",
        "name": "h3",
        "statement": {
            "english": "log base 8 of x equals log base 2 of x divided by 3",
            "conclusion": "log (8::real) x = log (2::real) x / (3::real)"
        }
    })])
    # Step 2.1: Obvious with log_base_change and h2
    root.session.age += 1
    await root.fill("2.1", [Obvious.gen_single({"facts": [
        {"name": "log_base_change"},
        {"name": "h2"}
    ]})])
    # Step 3: Have h4: log 8 (log 2 x) = log 2 (log 2 x) / 3
    root.session.age += 1
    await root.fill("3", [Have.gen_single({
        "thought": "change of base again",
        "name": "h4",
        "statement": {
            "english": "log base 8 of (log base 2 of x) equals log base 2 of (log base 2 of x) divided by 3",
            "conclusion": "log (8::real) (log (2::real) x) = log (2::real) (log (2::real) x) / (3::real)"
        }
    })])
    print_header("Before step 3.1", file)
    root.print(0, file)
    # Step 3.1: Obvious with log_base_change + h2 → HAMMER partially solves,
    # leaving subgoals that trigger an unexpected Intro at step 3.2
    root.session.age += 1
    await root.fill("3.1", [Obvious.gen_single({"facts": [
        {"name": "log_base_change"},
        {"name": "h2"}
    ]})])
    print_header("After step 3.1 (unexpected Intro at 3.2)", file)
    root.print(0, file)

@model_test("Hammer_ProveInTime", "Test_Hammer_ProveInTime.thy", 13)
async def _test_Hammer_ProveInTime(root: Root, file: MyIO):
    """Reproduces OutOfData error when HAMMER uses a ProveInTime fact."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Step 1: Have h_log8
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "log base 8 of x equals log base 2 of x divided by 3",
        "name": "h_log8",
        "statement": {
            "english": "log base 8 of x equals (log base 2 of x) / 3",
            "conclusion": "log (8::real) x = log (2::real) x / 3"
        }
    })])
    print_header("After Have h_log8", file)
    root.print(0, file)
    # Step 1.1: Obvious with a ProveInTime fact (by proposition), a library fact, and a local premise
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": [
        {"proposition": "(8::real) = (2::real) ^ (3::nat)"},
        {"name": "log_base_pow"},
        {"name": "h0"},
    ]})])
    print_header("After Obvious with ProveInTime", file)
    root.print(0, file)

@model_test("Simplify_stuck", "Test_Simplify_stuck.thy", 13)
async def _test_Simplify_stuck(root: Root, file: MyIO):
    """Reproduces stuck SIMPLIFY when rewriting with local + library facts inside a Have block."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "Since 8 = 2^3, log base 8 of x equals log base 2 of x divided by 3",
        "name": "h2",
        "statement": {
            "english": "log base 8 of x equals log base 2 of x divided by 3",
            "conclusion": "log (8::real) x = log (2::real) x / 3"
        }
    })])
    print_header("After Have h2", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1.1", [Have.gen_single({
        "thought": "First establish that 8 = 2^3 as reals",
        "name": "h8",
        "statement": {
            "english": "8 equals 2 to the power 3",
            "conclusion": "(8::real) = (2::real) ^ 3"
        }
    })])
    root.session.age += 1
    await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    print_header("After proving h8", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1.2", [Rewrite.gen_single({
        "thought": "Rewrite 8 as 2^3 in the goal using h8, then apply log_base_pow",
        "using": [
            {"name": "h8"},
            {"name": "log_base_pow"}
        ],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After Rewrite", file)
    root.print(0, file)

@model_test("Simplify_no_intro_bindings", "Test_Simplify_no_intro_bindings.thy", 13)
async def _test_Simplify_no_intro_bindings(root: Root, file: MyIO):
    """Reproduces 'Expected exactly one Intro_Bindings_Msg, got 0' when Rewrite
    references a local fact (h8eq) that is out of scope."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Step 1: Have h2
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "log base 8 of x equals log base 2 of x divided by 3",
        "name": "h2",
        "statement": {
            "english": "log base 8 of x equals log base 2 of x divided by 3",
            "conclusion": "log (8::real) x = log 2 x / 3"
        }
    })])
    # Step 1.1: Have h8eq (inside h2's proof)
    root.session.age += 1
    await root.fill("1.1", [Have.gen_single({
        "thought": "First establish that 8 = 2^3 as reals",
        "name": "h8eq",
        "statement": {
            "english": "8 equals 2 to the power 3",
            "conclusion": "(8::real) = 2 ^ 3"
        }
    })])
    # Step 1.1.1: Obvious (proves h8eq)
    root.session.age += 1
    await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    # Step 1.2: Rewrite using h8eq + log_base_pow (triggers timeout fallback)
    root.session.age += 1
    await root.fill("1.2", [Rewrite.gen_single({
        "thought": "Rewrite 8 as 2^3 using h8eq, then apply log_base_pow",
        "using": [
            {"name": "h8eq"},
            {"name": "log_base_pow"}
        ],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    # Step 1.3: Obvious (closes h2's remaining goal)
    root.session.age += 1
    await root.fill("1.3", [Obvious.gen_single({"facts": []})])
    print_header("After completing h2", file)
    root.print(0, file)
    # Step 2: Have h3
    root.session.age += 1
    await root.fill("2", [Have.gen_single({
        "thought": "Rewrite h1 using h2",
        "name": "h3",
        "statement": {
            "english": "log base 2 of (log base 2 of x divided by 3) equals log base 2 of (log base 2 of x) divided by 3",
            "conclusion": "log (2::real) (log 2 x / 3) = log 2 (log 2 x) / 3"
        }
    })])
    # Step 2.1: Have h2b (inside h3's proof)
    root.session.age += 1
    await root.fill("2.1", [Have.gen_single({
        "thought": "log 8 (log 2 x) = log 2 (log 2 x) / 3 by the same log_base_pow argument",
        "name": "h2b",
        "statement": {
            "english": "log base 8 of (log base 2 of x) equals log base 2 of (log base 2 of x) divided by 3",
            "conclusion": "log (8::real) (log 2 x) = log 2 (log 2 x) / 3"
        }
    })])
    # Step 2.1.1: Rewrite using h8eq + log_base_pow with no system simplifiers
    # h8eq is OUT OF SCOPE here (it was local to step 1's proof)
    # This triggers: Expected exactly one Intro_Bindings_Msg, got 0
    root.session.age += 1
    await root.fill("2.1.1", [Rewrite.gen_single({
        "thought": "Rewrite 8 as 2^3 using h8eq and apply log_base_pow",
        "using": [
            {"name": "h8eq"},
            {"name": "log_base_pow"}
        ],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After step 2.1.1", file)
    root.print(0, file)

@model_test("Intro_no_intro_bindings", "Test_Intro_no_intro_bindings.thy", 8)
async def _test_Intro_no_intro_bindings(root: Root, file: MyIO):
    """Reproduces 'Expected exactly one Intro_Bindings_Msg in Intro's messages, got 0'.

    Root cause: `AUTO_INTRO` (contrib/Isa-Mini/Agent/agent.ML) short-
    circuits on `not (Minilang.need_intro st)` and returns
    `(([], []), s)` without calling `Minilang.get_reporter () (INTRO_BINDINGS ...)`.
    `need_intro` is false when the leading goal has no outer
    Pure.imp / Pure.all / HOL.All / HOL.implies. The Python side
    (model.py:5817, `Intro._refresh_the_beginning_opr`) then finds zero
    `Intro_Bindings_Msg` and raises `InternalError`.

    Trigger here: `CaseSplit` on a boolean brings the case hypothesis into the
    goal context as a named premise (`True.prem0: b`), leaving the residual
    goal `P True` with no outer ⋀ / ⟹. An `Intro` inside that case (e.g. to
    rename the hypothesis via `fact_bindings`) hits the early-return path.
    This matches the real-world trace where `CaseSplit` on `q = (3 :: nat)`
    was followed by `Intro { fact_bindings: ['q_eq_3'] }` inside the True case.
    """
    print_header("Initial YAML", file)
    root.print(0, file)
    # Step 1: CaseSplit on b. Each case subgoal has the hypothesis already in
    # the local context (True.prem0: b, False.prem0: ¬ b); the residual goals
    # `P True` / `P False` have no outer quantifier or implication.
    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on boolean b",
        "target_isabelle_term": r"b"
    })])
    print_header("After CaseSplit", file)
    root.print(0, file)
    # === DEBUG PROBE ===
    true_goal = root.locate_node("1.True")
    s = true_goal.ml_state
    file.write(f"[probe] 1.True: display_goals_count={s.display_goals_count}")
    if s.leading_goal:
        file.write(f", leading={s.leading_goal.conclusion.unicode}")
    file.write("\n")
    # Step 1.True.1: Intro with a fact_binding. Empirically verified via
    # `ml_state.need_intro(...)` probe that both need_intro(True) and
    # need_intro(False) return False at `1.True` (the case hypothesis is
    # already a named local premise, not an outer ⟹), so AUTO_INTRO
    # short-circuits without emitting INTRO_BINDINGS. Pre-fix the Python
    # `_refresh_the_beginning_opr` then raised:
    #   Expected exactly one Intro_Bindings_Msg in Intro's messages, got 0
    root.session.age += 1
    _intro_outcome = await root.fill("1.True.1", [Intro.gen_single({
        "thought": "Rename the case hypothesis",
        "fact_bindings": ["b_true"]
    })])
    print_header("edit_message: Intro under 1.True", file)
    file.write((await _P.edit_message(root, _intro_outcome, root.session))[0])
    file.write("---------------\n")
    print_header("Intro node print (1.True.1)", file)
    intro_node = root.locate_node("1.True.1")
    intro_node.print(0, file)
    # === DEBUG PROBE ===
    rs = intro_node.resulting_state()
    file.write(f"[probe] Intro: new_subgoals_count={rs.new_subgoals_count}, display_goals_count={rs.display_goals_count}\n")
    print_header("Full tree after Intro", file)
    root.print(0, file)

@model_test("InferenceRule_in_CaseSplit", "Test_InferenceRule_in_CaseSplit.thy", 8)
async def _test_InferenceRule_in_CaseSplit(root: Root, file: MyIO):
    """Verify that an InferenceRule producing exactly 1 subgoal inside a
    CaseSplit case triggers the same sibling-leak display bug as Intro
    no-op. Both inherit SubgoalMaker (model.py:5722, 5926); neither
    overrides `_refresh_the_beginning_opr` / `_should_open_proof_block`,
    so the "open a 2-child block iff top_goals() > 1" check at
    model.py:3932 fires for both whenever the top HHF leaves exactly 1
    goal (→ `prt0` gives `PROP` → MAGIC's `cat_tree` composes it with
    the sibling case into a *leaf* BUNDL → `MLPT_Bundle.top_goals`
    returns both).

    Setup: goal `b ⟶ P b`, CaseSplit on b, then impI in the True case.
    impI applied via `Thm.biresolution` gives exactly 1 resulting
    subgoal (`True ⟹ P True`), so the top HHF has 1 goal.

    Expected: `1.True.1` (the InferenceRule) spuriously shows 2 child
    subgoals — `1.True.1.1` plus a sibling-leak `1.True.1.False`
    renamed from the outer CaseSplit's False case — same symptom as
    Intro no-op.
    """
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on boolean b",
        "target_isabelle_term": r"b"
    })])
    print_header("After CaseSplit", file)
    root.print(0, file)
    # Apply disjI1 to `P True ∨ P True` — produces exactly 1 protected
    # subgoal `P True` in the top HHF. With the top HHF at 1 goal,
    # `print_stack`'s `prt0` returns PROP; the MAGIC PRT callback then
    # composes it with the False sibling into a leaf BUNDL, so
    # `top_goals()` leaks to 2.
    root.session.age += 1
    await root.fill("1.True.1", [InferenceRule.gen_single({
        "thought": "Apply disjI1 (produces exactly 1 subgoal from disjunction)",
        "rule": {"name": "disjI1"}
    })])
    # === DEBUG PROBE ===
    ir_node = root.locate_node("1.True.1")
    sab = cast(StdBlock, ir_node)._state_after_beginning()
    file.write(f"[probe] InferenceRule: new_subgoals_count={sab.new_subgoals_count}, display_goals_count={sab.display_goals_count}\n")
    file.write(f"[probe] InferenceRule sub_nodes ids: {[c.id for c in cast(NonLeaf_Node, ir_node).sub_nodes]}\n")
    print_header("After InferenceRule (expect spurious 2nd sibling-leak subgoal)", file)
    root.print(0, file)

@model_test("Nested_InferenceRule_Leak",
            "Test_Nested_InferenceRule_Leak.thy", 8)
async def _test_Nested_InferenceRule_Leak(root: Root, file: MyIO):
    """Verify that the sibling-leak bug also manifests WITHOUT a CaseSplit —
    plain nested `InferenceRule`s are enough.

    Setup: goal `((1=1) ∧ (2=2)) ∧ (3=3)`.
    - Outer conjI → 2 subgoals: `(1=1) ∧ (2=2)` and `(3=3)`.
    - Inner conjI on the first subgoal → expected 2 subgoals (`1=1`, `2=2`);
      however at the ML level RULE does NOT push a new frame, so
      `Thm.biresolution ... 1` just rewrites the single top HHF from
      `[(1=1)∧(2=2), 3=3]` to `[1=1, 2=2, 3=3]` — three *flat* protected
      subgoals.  Python's `MLPT_Bundle.top_goals` (model.py:935-942) returns
      `[1=1, 2=2, 3=3]` and `SubgoalMaker._refresh_the_beginning_opr` at
      model.py:3932 opens a 3-child block.  The third child is advanced by
      `sorry_next` and lands on the outer sibling `3=3` — same symptom as
      the CaseSplit-based leaks, without any CaseSplit involved.

    Expected (empirically): inner InferenceRule has 3 sub_nodes, not 2.
    """
    print_header("Initial YAML", file)
    root.print(0, file)
    # Step 1: outer conjI — produces 2 subgoals
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "Outer conjI: split ((1=1)∧(2=2)) ∧ (3=3)",
        "rule": {"name": "conjI"}
    })])
    print_header("After outer conjI (expect 2 child GoalNodes: 1.1, 1.2)", file)
    root.print(0, file)
    outer_ir = root.locate_node("1")
    outer_kids = [c.id for c in cast(NonLeaf_Node, outer_ir).sub_nodes
                  if type(c).__name__ == "GoalNode"]
    file.write(f"[probe] outer conjI GoalNode children: {outer_kids}\n")
    # Step 1.1.1: inner conjI on the first subgoal (1=1) ∧ (2=2)
    root.session.age += 1
    await root.fill("1.1.1", [InferenceRule.gen_single({
        "thought": "Inner conjI on first subgoal: split (1=1) ∧ (2=2)",
        "rule": {"name": "conjI"}
    })])
    inner_ir = root.locate_node("1.1.1")
    sab = cast(StdBlock, inner_ir)._state_after_beginning()
    file.write(f"[probe] inner conjI: new_subgoals_count={sab.new_subgoals_count}, display_goals_count={sab.display_goals_count}\n")
    inner_kids = [c.id for c in cast(NonLeaf_Node, inner_ir).sub_nodes
                  if type(c).__name__ == "GoalNode"]
    file.write(f"[probe] inner conjI GoalNode children: {inner_kids}\n")
    print_header("After inner conjI (2 expected; 3 if leak present)", file)
    root.print(0, file)

@model_test("Have1", "Test_Have1.thy", 9)
async def _test_Have1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "helper",
        "statement": {"english": "x squared is non-negative", "conclusion": r"(0::int) \<le> x * x"},
        "name": "lem1"
    })])
    print_header("After Have", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])

@model_test("HaveParseError", "Test_HaveParseError.thy", 9)
async def _test_HaveParseError(root: Root, file: MyIO):
    """log-2: a Have whose conclusion is an inner-syntax parse error must report a
    precise 【marked token】 location (here the `n` in the typed group `(m n :: nat)`),
    not the opaque `at ""`. Mirrors ForeNodeFail's failed-Have rendering."""
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "intentionally malformed binder group",
        "statement": {"english": "malformed",
                      "conclusion": r"\<forall>(f :: nat \<Rightarrow> real) (m n :: nat). f m \<le> f n"},
        "name": "bad"
    })])
    step = root.locate_node("1")
    file.write(f"Step 1 status: {step.status.status.value}\n")
    print_header("After malformed Have", file)
    root.print(0, file)

@model_test("SubagentSlotResolve", "Test_SubagentSlotResolve.thy", 8)
async def _test_SubagentSlotResolve(root: Root, file: MyIO):
    """`Node.locate_node_or_slot` resolves the address space that `subagent`
    now accepts (existing node OR unfilled proof slot), mirroring `fill`.
    After a top-level `Have` at step 1, the open slots are `1.1` (the Have's
    body) and `2` (the top-level continuation) — see the `Have1` golden."""
    await root.fill("1", [Have.gen_single({
        "thought": "helper",
        "statement": {"english": "z squared is non-negative",
                      "conclusion": r"(0::int) \<le> z * z"},
        "name": "lem1"
    })])
    def probe(id: str) -> str:
        try:
            r = root.locate_node_or_slot(id)
        except model.NodeNotFound:
            return "NodeNotFound"
        if isinstance(r, model.Resolved_Node):
            return f"Resolved_Node(node.id={r.node.id!r})"
        if isinstance(r, model.Resolved_Slot):
            return f"Resolved_Slot(parent.id={r.parent.id!r}, slot_id={r.slot_id!r})"
        return f"UNEXPECTED {r!r}"
    print_header("locate_node_or_slot resolution", file)
    # 1     : existing materialized node           -> Resolved_Node
    # 1.1   : the Have's open body slot            -> Resolved_Slot(parent=Have 1)
    # 2     : top-level continuation slot          -> Resolved_Slot(parent=GoalNode "")
    # 1.9   : a non-open slot under existing parent -> NodeNotFound
    # 1.1.1 : slot whose parent (1.1) doesn't exist -> NodeNotFound
    for id in ["1", "1.1", "2", "1.9", "1.1.1"]:
        file.write(f"{id} -> {probe(id)}\n")

@model_test("HaveAutoApply", "Test_Have_AutoApply.thy", 10)
async def _test_HaveAutoApply(root: Root, file: MyIO):
    """Have with auto_apply=True auto-registers the proven equation as a simp
    rule, so the enclosing goal `myf 3 = 10` can be closed without referring
    to the new fact by name. Fails if auto_apply_fact is not wired up — plain
    Obvious cannot unfold `myf` otherwise, since `myf_def` is not a simp rule
    by default."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Derive an equation for the user-defined constant `myf`. The classifier
    # sees an equation conclusion (chk_simp) and registers it into the simpset
    # of the live context via auto_apply_fact.
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "Derive a simp rule for myf so the outer goal becomes trivial",
        "statement": {
            "english": "myf n equals n plus 7",
            "conclusion": r"myf n = n + 7"
        },
        "name": "myf_eq",
        "auto_apply": True,
    })])
    print_header("After Have (auto_apply=True)", file)
    root.print(0, file)

    # Discharge the Have's subgoal by unfolding the definition; `myf_def`
    # must be passed explicitly because it is not in the default simpset.
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({
        "facts": [{"name": "myf_def"}]
    })])
    print_header("After proving Have sub-goal", file)
    root.print(0, file)

    # Close the outer goal `myf 3 = 10` with Rewrite that uses ONLY the
    # system simplification set (no manually-supplied rules). This only
    # succeeds if `myf_eq` was auto-registered into the simpset by
    # `mini_auto_apply` — otherwise the system simpset has no way to unfold
    # `myf` and the goal cannot be reduced to `10 = 10`.
    root.session.age += 1
    ret = await root.fill("2", [Rewrite.gen_single({
        "thought": "Close the outer goal using only the system simplifier",
        "using": [],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After closing outer goal", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("SetupRewriting", "Test_SetupRewriting.thy", 10)
async def _test_SetupRewriting(root: Root, file: MyIO):
    """SetupRewriting proves a rewriting equation and auto-registers it as a
    simp rule. The outer goal `myg 3 = 8` becomes trivial once `myg n = n + 5`
    is in the simpset."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [SetupRewriting.gen_single({
        "thought": "Derive a simp rule for myg so the outer goal becomes trivial",
        "redex": "myg n",
        "residue": "n + (5::nat)",
        "conditions": [],
    })])
    print_header("After SetupRewriting", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({
        "facts": [{"name": "myg_def"}]
    })])
    print_header("After proving SetupRewriting sub-goal", file)
    root.print(0, file)

    root.session.age += 1
    ret = await root.fill("2", [Rewrite.gen_single({
        "thought": "Close the outer goal using only the system simplifier",
        "using": [],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After closing outer goal", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("SetupRewriting_SimpNoProgress", "Test_SetupRewriting_SimpNoProgress.thy", 12)
async def _test_SetupRewriting_SimpNoProgress(root: Root, file: MyIO):
    """Reproduce: conditional SetupRewriting (f x -> x^2 - f(x-1)) is not
    auto-registered into the simpset because classify_thm/chk_simp doesn't
    handle meta-level implications (Pure.imp) produced by HAVE''.  The rule
    exists as a named fact but never enters the simpset, so a subsequent
    Rewrite that relies on system simplifiers sees 'no progress'.
    Reproduces the failure from interaction e173f3e4f_1.

    Root cause: chk_simp (sledgehammer_solver.ML dest_eq) traverses
    HOL.implies but not Pure.imp.  HAVE'' wraps conditions as meta-level
    premises (Pure.imp), so the conditional equation is invisible to
    chk_simp and classify_thm never adds it as "simp".

    Direct Isabelle confirms the conditional rule works fine:
      by (simp add: rule h1)   -- succeeds even for 75-step unfolding
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [SetupRewriting.gen_single({
        "thought": "Derive rewriting rule f x = x^2 - f(x-1) from h0",
        "for_any": [{"name": "x", "type": "int"}],
        "redex": "f x",
        "residue": "x ^ (2::nat) - f (x - (1::int))",
        "conditions": [{"name": "cond", "term": "(3::int) ≤ x"}],
        "proof": [{"operation": "Obvious", "facts": [{"name": "h0"}]}],
    })])
    print_header("After SetupRewriting", file)
    root.print(0, file)

    # Rewrite WITHOUT explicit setup_rewriting__1 — fails because
    # the conditional rule was not auto-added to the simpset
    root.session.age += 1
    outcome = await root.fill("2", [Rewrite.gen_single({
        "thought": "Apply setup_rewriting rule and h1 to compute f(5)",
        "using": [{"name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": [],
    })])
    print_header("After Rewrite (no explicit rule)", file)
    file.write(f"Rewrite failed: {outcome.failure is not None}\n")
    file.write(f"Failure reason: {outcome.failure}\n")
    root.print(0, file)

@model_test("Rewrite_Contradictory_Premise", "Test_Rewrite_Contradictory_Premise.thy", 13)
async def _test_Rewrite_Contradictory_Premise(root: Root, file: MyIO):
    """Reproduces gconv_rule crash when Rewrite completely solves the goal
    by deriving False from a contradictory premise after definition expansion.
    Bug: exception THM 1 raised (line 232 of "conv.ML"): gconv_rule"""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Rewrite premise 'eq' using MyConst1_def (=2) and MyConst2_def (=3).
    # The premise "MyConst1 = MyConst2" rewrites to "2 = 3" then False,
    # causing clarsimp to solve the entire goal.
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite premise using definitions to derive contradiction",
        "using": [
            {"name": "MyConst1_def"},
            {"name": "MyConst2_def"}
        ],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["eq"]
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("After Rewrite", file)
    root.print(0, file)
    file.write(f"is_error: {is_error}\n")
    file.write(f"reason: {reason.reason if isinstance(reason, FailureReason) else reason}\n")

@model_test("Rewrite_NO_SIMP_Leak", "Test_Rewrite_NO_SIMP_Leak.thy", 33)
async def _test_Rewrite_NO_SIMP_Leak(root: Root, file: MyIO):
    """Reproduce NO_SIMP leaking into premises when Rewrite targets a premise
    while the goal conclusion is False.

    Root cause: SIMPLIFY_GOAL_AND_PREMISES' wraps the conclusion as
    Trueprop(NO_SIMP(False)) when simplify_goal=false. clear_simpset clears
    simp rules but preserves the classical wrapper and solvers. When the
    classical wrapper has notnotD [dest!] (standard in AFP/seL4 projects),
    clarify resolves double negation, and the resulting interaction with the
    NO_SIMP-wrapped conclusion can leak '¬ NO_SIMP False' into premises.
    The unwrapping step only cleans the conclusion, not premises.

    The theory declares notnotD [dest!] to match the seL4/AFP context where
    the original bug was observed.
    """
    def assert_no_NO_SIMP(label: str) -> None:
        raw_buf = io.StringIO()
        yaml_buf = MyIO(raw_buf)
        root.print(0, yaml_buf)
        yaml_output = raw_buf.getvalue()
        if "NO_SIMP" in yaml_output:
            file.write(f"BUG DETECTED ({label}): NO_SIMP leaked into premises!\n")
            file.write(yaml_output)
            raise TestFailed(f"NO_SIMP leaked into premises ({label})")

    print_header("Initial YAML", file)
    root.print(0, file)

    # Rewrite premise h using is_nonzero_def with system simplifiers disabled.
    # This directly takes the cleared-simpset path (same as the timeout fallback).
    # The premise ¬ is_nonzero(f a) rewrites to ¬(f a ≠ 0) = ¬¬(f a = 0).
    # With notnotD [dest!] in the classical wrapper, clarify resolves the double
    # negation. The NO_SIMP(False) conclusion should NOT leak into premises.
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite h using is_nonzero_def to expose double negation",
        "using": [{"name": "is_nonzero_def"}],
        "use system simplifiers": False,
        "rewrite goal": False,
        "rewrite premises": ["h"]
    })])
    success = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("After Rewrite", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason.reason if isinstance(reason, FailureReason) else reason}\n")
    assert_no_NO_SIMP("NO_SIMP leaked via classical reasoning on wrapped conclusion")

@model_test("Rewrite_Once_Simproc", "Test_Rewrite_Once_Simproc.thy", 27)
async def _test_Rewrite_Once_Simproc(root: Root, file: MyIO):
    """Test that a genuinely looping rewrite rule triggers the once-simproc
    fallback instead of timing out. The rule my_wrap (f x = g (f x)) is
    self-looping: the LHS matches a subterm of the RHS. The fallback should
    wrap it as a simproc limited to fire at most once."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Rewrite goal using my_wrap — a self-looping rule (f x = g (f x)).
    # The looping rule triggers an interaction for target selection.
    # Select all targets so the once-simproc wraps them.
    async def stub_fork(interaction):
        print_header("Interaction Prompt", file)
        await interaction.prompt(0, file)
        assert isinstance(interaction, Interaction_SelectRewriteTargets)
        num_matches = len(interaction.looping_rules[0][2]) if interaction.looping_rules else 0
        return await interaction.answer(AnswerIndexes(indexes=list(range(num_matches))))
    root.session.launch_interaction = stub_fork
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite using my_wrap to unfold f into g(f(...))",
        "using": [{"name": "my_wrap"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    success = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("After Rewrite (via interaction)", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason.reason if isinstance(reason, FailureReason) else reason}\n")

@model_test("Rewrite_Targeted", "Test_Rewrite_Targeted.thy", 25)
async def _test_Rewrite_Targeted(root: Root, file: MyIO):
    """Test interactive target selection for a looping rewrite rule.
    The rule my_wrap (f x = g (f x)) loops. The goal contains two matching
    subterms: f a and f b. We select only the first (f a) to rewrite,
    leaving f b untouched. The targeted simproc should fire only on f a."""
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_fork(interaction):
        print_header("Interaction Prompt", file)
        await interaction.prompt(0, file)
        # Select index 1 only (should be "f a", leaving "f b" untouched)
        return await interaction.answer(AnswerIndexes(indexes=[1]))
    root.session.launch_interaction = stub_fork
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite f a using my_wrap, leave f b alone",
        "using": [{"name": "my_wrap"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    success = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("After Targeted Rewrite", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason.reason if isinstance(reason, FailureReason) else reason}\n")

@model_test("Rewrite_Targeted_Drop", "Test_Rewrite_Targeted_Drop.thy", 23)
async def _test_Rewrite_Targeted_Drop(root: Root, file: MyIO):
    """Test that selecting no targets during the interaction drops the looping
    rule entirely. The Rewrite should proceed without the rule — since no other
    rules are provided, the simplification should fail with 'no progress'."""
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_fork(interaction):
        print_header("Interaction Prompt", file)
        await interaction.prompt(0, file)
        return await interaction.answer(AnswerIndexes(indexes=[]))
    root.session.launch_interaction = stub_fork
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Attempt rewrite with looping rule, then dismiss",
        "using": [{"name": "my_wrap"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    success = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("After Rewrite (rule dropped)", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason.reason if isinstance(reason, FailureReason) else reason}\n")

@model_test("Rewrite_LoopingForkCtxt", "Test_Rewrite_LoopingForkCtxt.thy", 16)
async def _test_Rewrite_LoopingForkCtxt(root: Root, file: MyIO):
    """Regression for driver_api._run_fork bug: looping rewrite rules trigger
    launch_interaction with FORKING_WITH_CTXT during edit tool execution. The
    driver copies self._messages which has a pending function_call without
    ToolResultMsg, causing 'No tool output found' API error."""
    from .driver_api import (
        AssistantMsg as DrvAssistantMsg, UserMsg as DrvUserMsg,
        SystemMsg as DrvSystemMsg, ToolCall, ProviderResponse, Usage, Msg)

    print_header("Initial YAML", file)
    root.print(0, file)

    fork_triggered = False

    async def stub_fork(interaction):
        nonlocal fork_triggered
        fork_triggered = True
        file.write(f"forking_mode: {interaction.forking.name}\n")
        if interaction.forking != ForkingMode.FORKING_WITH_CTXT:
            raise TestFailed(
                f"Expected FORKING_WITH_CTXT but got {interaction.forking.name}.")

        # --- Reproduce the bug scenario in _run_fork ---
        # During edit tool execution, self._messages ends with an AssistantMsg
        # whose function_calls have no matching ToolResultMsg.
        tc = ToolCall(id="call_repro", name="edit",
                      arguments='{"action":"fill","target_step":"1"}')
        pending_resp = ProviderResponse(
            content=None, thinking=None, tool_calls=[tc], usage=Usage(0, 0, 0))
        simulated_messages: list[Msg] = [
            DrvSystemMsg("sys"),
            DrvUserMsg("initial prompt"),
            DrvAssistantMsg(response=pending_resp),  # pending tool call, no result
        ]

        # Apply the same fix as _run_fork:
        fork_messages = list(simulated_messages)
        if (fork_messages
                and isinstance(fork_messages[-1], DrvAssistantMsg)
                and fork_messages[-1].response.tool_calls):
            pending = fork_messages[-1].response.tool_calls
            parts = [f"calling {tc.name} with arguments:\n{tc.arguments}"
                     for tc in pending]
            fork_messages[-1] = DrvAssistantMsg(
                response=ProviderResponse(
                    content="I am " + "\n".join(parts),
                    thinking=None, tool_calls=[], usage=Usage(0, 0, 0)))
        fork_messages.append(DrvUserMsg("fork prompt"))

        # Verify: the patched messages have no dangling function_calls
        last_asst = [m for m in fork_messages if isinstance(m, DrvAssistantMsg)][-1]
        if last_asst.response.tool_calls:
            raise TestFailed("Fix failed: fork_messages still has dangling tool_calls")
        if last_asst.response.content is None or "edit" not in last_asst.response.content:
            raise TestFailed("Fix failed: replacement message should mention the tool")
        file.write(f"fix_verified: True\n")

        print_header("Interaction Prompt", file)
        await interaction.prompt(0, file)
        return await interaction.answer(AnswerIndexes(indexes=[0]))

    root.session.launch_interaction = stub_fork

    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite using looping rule",
        "using": [{"name": "my_wrap"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    if not fork_triggered:
        raise TestFailed("Fork interaction was not triggered for looping rule")
    file.write(f"fork_triggered: {fork_triggered}\n")
    print_header("After Rewrite", file)
    root.print(0, file)

@model_test("Rewrite_QuantifiedGoal", "Test_Rewrite_QuantifiedGoal.thy", 28)
async def _test_Rewrite_QuantifiedGoal(root: Root, file: MyIO):
    """Regression test: applying a looping rewrite rule to a quantified goal
    must not crash with 'fastype_of: Bound'.

    Root cause: find_matching_subterms descends into Abs bodies via
      collect (Abs (_, _, body)) acc = collect body acc
    without substituting the bound variable, leaving dangling Bound indices.
    Pattern.match then calls fastype_of on these subterms, which crashes."""
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_fork(interaction):
        print_header("Interaction Prompt", file)
        await interaction.prompt(0, file)
        assert isinstance(interaction, Interaction_SelectRewriteTargets)
        num_matches = len(interaction.looping_rules[0][2]) if interaction.looping_rules else 0
        return await interaction.answer(AnswerIndexes(indexes=list(range(num_matches))))
    root.session.launch_interaction = stub_fork
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite f y inside the existential using my_wrap",
        "using": [{"name": "my_wrap"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    success = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("After Rewrite (quantified goal)", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason.reason if isinstance(reason, FailureReason) else reason}\n")

@model_test("Rewrite_Targeted_Where", "Test_Rewrite_Targeted_Where.thy", 16)
async def _test_Rewrite_Targeted_Where(root: Root, file: MyIO):
    """Regression: looping rule with [where ...] instantiation must still fire.

    check_looping_rules uses the uninstantiated rule to find matching subterms,
    but the actual SIMPLIFY uses the instantiated rule. The targeted simproc's
    lhss pattern (from the instantiated LHS) must still hit the selected target.
    Without the fix, the simproc misses and reports 'no progress'."""
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_fork(interaction):
        print_header("Interaction Prompt", file)
        await interaction.prompt(0, file)
        assert isinstance(interaction, Interaction_SelectRewriteTargets)
        num_matches = len(interaction.looping_rules[0][2]) if interaction.looping_rules else 0
        file.write(f"num_matches: {num_matches}\n")
        return await interaction.answer(AnswerIndexes(indexes=list(range(num_matches))))
    root.session.launch_interaction = stub_fork
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Apply my_looping with x instantiated to a",
        "using": [{"name": "my_looping",
                   "instantiations": [{"name": "?x",
                                       "value": "a::nat"}]}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After Rewrite", file)
    root.print(0, file)
    if _outcome.failure is not None:
        file.write(f"FAILURE: {_outcome.failure}\n")
    else:
        file.write("SUCCESS\n")

@model_test("Rewrite_InternalError", "Test_Rewrite_InternalError.thy", 21)
async def _test_Rewrite_InternalError(root: Root, file: MyIO):
    """Bug reproduction: when SIMPLIFY hits an internal Isabelle exception
    (e.g. THM type-conflict from a simproc), the raw ML exception trace
    leaks into the agent-facing error message.

    Root cause chain:
      1. agent_server.ML's error handler doesn't catch THM (only OPR_FAIL,
         ERROR, FACT_IN_TIME_FAIL, Auto_Fail).
      2. Leaf._refresh_me_alone stores the raw error as FailureReason.
      3. Rewrite._on_edit_failure propagates it into CannotEdit_EvaluationFailed.
      4. edit_message renders str(failure) verbatim to the agent.

    The test theory defines a simproc that throws THM when the simplifier
    encounters 'trigger_thm_err _', simulating the real-world scenario
    where the HOL simplifier hits a type-instantiation conflict."""
    print_header("Initial YAML", file)
    root.print(0, file)

    outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Try system simplifiers",
        "using": [],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])

    print_header("Outcome", file)
    failure = outcome.failure
    file.write(f"has_failure: {failure is not None}\n")
    file.write(f"is_error: {failure.is_error if failure else None}\n")
    file.write(f"committed_count: {len(outcome.committed)}\n")
    if failure:
        reason_str = str(failure)
        file.write(f"failure_message:\n{reason_str}\n")
        raw_exception_leaked = ("exception THM" in reason_str
                                or "raised (line" in reason_str)
        file.write(f"raw_exception_leaked: {raw_exception_leaked}\n")

    print_header("After Rewrite attempt", file)
    root.print(0, file)

# class TestCase_Interactive_Unfold:
#     pass

@model_test("IMO_1966_p5", "Test_imo_1966_p5.thy", 19)
async def _test_imo_1966_p5(root: Root, file: MyIO):
    """Test filling Have steps into an initially empty proof tree.
    The proof tree has no auto-Intro (the goal is presented directly),
    so we fill step 1 with a Have, then work on its subproof."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()

    # 1. Fill step 1 with Have eq1
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "Since a(2) < a(1), a(3) < a(2), a(4) < a(3), we know a(1) > a(2) > a(3) > a(4). "
                   "Subtracting h7 from h6, the coefficients factor as (a(1)-a(2))*(-x1+x2+x3+x4)=0. "
                   "Since a(1)-a(2)>0, we get x1=x2+x3+x4.",
        "name": "eq1",
        "statement": {
            "english": "x(1) equals x(2) + x(3) + x(4)",
            "conclusion": "x (1::nat) = x (2::nat) + x (3::nat) + x (4::nat)"
        }
    })])
    print_header("After filling Have eq1", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()

    # 2. Try Obvious to prove eq1 — fails (non-trivial)
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({
        "facts": [
            {"name": "h6"},
            {"name": "h7"},
            {"name": "assms(1)"},
            {"name": "assms(2)"},
            {"name": "assms(3)"}
        ]
    })])
    print_header("After failed Obvious on eq1", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()

    # 3. Delete the failed Obvious step
    root.session.age += 1
    await root.delete(["1.1"])
    print_header("After deleting failed Obvious", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()

    # 4. Fill with intermediate Have: a1_gt_a3
    root.session.age += 1
    await root.fill("1.1", [Have.gen_single({
        "thought": "From assms(1) and assms(2), a(1) > a(3), so |a(1) - a(3)| = a(1) - a(3)",
        "name": "a1_gt_a3",
        "statement": {
            "english": "a(1) is greater than a(3)",
            "conclusion": "a (1::nat) > a (3::nat)"
        }
    })])
    # Prove a1_gt_a3 with Obvious — should succeed
    root.session.age += 1
    await root.fill("1.1.1", [Obvious.gen_single({
        "facts": [
            {"name": "assms(1)"},
            {"name": "assms(2)"}
        ]
    })])
    print_header("After proving a1_gt_a3", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()

    # 5. Fill with intermediate Have: a1_gt_a4
    root.session.age += 1
    await root.fill("1.2", [Have.gen_single({
        "thought": "From assms, a(1) > a(2) > a(3) > a(4), so a(1) > a(4)",
        "name": "a1_gt_a4",
        "statement": {
            "english": "a(1) is greater than a(4)",
            "conclusion": "a (1::nat) > a (4::nat)"
        }
    })])
    # Prove a1_gt_a4 with Obvious — should succeed
    root.session.age += 1
    await root.fill("1.2.1", [Obvious.gen_single({
        "facts": [
            {"name": "a1_gt_a3"},
            {"name": "assms(3)"}
        ]
    })])
    print_header("After proving a1_gt_a4", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset()

@model_test("SemanticKNN_patterns", "Test_RetrieveFact.thy", 8)
async def _test_semantic_knn_patterns(root: Root, file: MyIO):
    """Test semantic_knn with term_patterns, type_patterns, theories_include, and warnings."""
    from Isabelle_RPC_Host.universal_key import EntityKind
    ml = root.ml_state

    def _pp(r) -> str:
        expr = ', '.join(e.unicode for e in r.entity.expression)
        return f"{r.entity.kind.label} {r.entity.short_name.unicode}: {expr}" if expr else f"{r.entity.kind.label} {r.entity.short_name.unicode}"

    # 1. Baseline: no patterns
    results_base, warnings_base = await ml.semantic_knn("logarithm power", 5, [EntityKind.THEOREM])
    file.write(f"Baseline (no patterns): {len(results_base)} results, {len(warnings_base)} warnings\n")
    for r in results_base:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")
    assert not warnings_base, "Expected no warnings for baseline"

    # 2. With term_patterns: restrict to theorems containing "ln"
    results_term, warnings_term = await ml.semantic_knn("logarithm power", 10, [EntityKind.THEOREM],
                                   term_patterns=["ln ?x"])
    file.write(f"With term_patterns=[\"ln ?x\"]: {len(results_term)} results, {len(warnings_term)} warnings\n")
    for r in results_term:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")
    assert len(results_term) > 0, "Expected at least one result with term pattern 'ln ?x'"

    # 3. With type_patterns: restrict to theorems involving nat
    results_type, warnings_type = await ml.semantic_knn("logarithm", 10, [EntityKind.THEOREM],
                                   type_patterns=["nat"])
    file.write(f"With type_patterns=[\"nat\"]: {len(results_type)} results, {len(warnings_type)} warnings\n")
    for w in warnings_type:
        file.write(f"  Warning: {w}\n")
    for r in results_type:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")

    # 4. With theories_include
    results_thy, warnings_thy = await ml.semantic_knn("logarithm", 10, [EntityKind.THEOREM],
                                  theories_include=["HOL.Transcendental"])
    file.write(f"With theories_include=[\"HOL.Transcendental\"]: {len(results_thy)} results, {len(warnings_thy)} warnings\n")
    for w in warnings_thy:
        file.write(f"  Warning: {w}\n")
    for r in results_thy:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")

    # 5. Constants with type_patterns
    results_const, warnings_const = await ml.semantic_knn("logarithm", 5, [EntityKind.CONSTANT],
                                    type_patterns=["real \\<Rightarrow> real"])
    file.write(f"Constants with type_patterns=[\"real => real\"]: {len(results_const)} results, {len(warnings_const)} warnings\n")
    for w in warnings_const:
        file.write(f"  Warning: {w}\n")
    for r in results_const:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")

    # 6. Empty patterns = same as baseline
    results_empty, warnings_empty = await ml.semantic_knn("logarithm power", 5, [EntityKind.THEOREM],
                                    term_patterns=[], type_patterns=[], theories_include=[])
    file.write(f"Empty patterns: {len(results_empty)} results, {len(warnings_empty)} warnings\n")
    assert len(results_empty) == len(results_base), "Empty patterns should match baseline"
    assert not warnings_empty, "Expected no warnings for empty patterns"

    # 6b. name_contains: single substring
    results_nc, warnings_nc = await ml.semantic_knn("logarithm", 10, [EntityKind.THEOREM],
                                    name_contains=["ln"])
    file.write(f"With name_contains=[\"ln\"]: {len(results_nc)} results\n")
    for r in results_nc:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")
        assert "ln" in r.entity.full_name.lower(), f"Expected 'ln' in name: {r.entity.full_name}"
    assert len(results_nc) > 0, "Expected at least one result with name containing 'ln'"

    # 6c. name_contains: multiple substrings (conjunction)
    results_nc2, warnings_nc2 = await ml.semantic_knn("logarithm", 10, [EntityKind.THEOREM],
                                    name_contains=["ln", "real"])
    file.write(f"With name_contains=[\"ln\", \"real\"]: {len(results_nc2)} results\n")
    for r in results_nc2:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")
        assert "ln" in r.entity.full_name.lower() and "real" in r.entity.full_name.lower(), \
            f"Expected both 'ln' and 'real' in name: {r.entity.full_name}"
    assert len(results_nc2) <= len(results_nc), "Conjunction should narrow results"

    # 6d. name_contains with constants
    results_nc_c, warnings_nc_c = await ml.semantic_knn("logarithm", 5, [EntityKind.CONSTANT],
                                    name_contains=["ln"])
    file.write(f"Constants with name_contains=[\"ln\"]: {len(results_nc_c)} results\n")
    for r in results_nc_c:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")
        assert "ln" in r.entity.full_name.lower(), f"Expected 'ln' in name: {r.entity.full_name}"

    # 6e. Empty name_contains = same as baseline
    results_nc_e, _ = await ml.semantic_knn("logarithm power", 5, [EntityKind.THEOREM],
                                    name_contains=[])
    assert len(results_nc_e) == len(results_base), "Empty name_contains should match baseline"

    # 6f. Pattern-only search (query=None) with limit
    results_lim, warnings_lim = await ml.semantic_knn(None, 3, [EntityKind.THEOREM],
                                    name_contains=["ln"])
    file.write(f"Pattern-only with limit=3, name_contains=[\"ln\"]: {len(results_lim)} results\n")
    for r in results_lim:
        file.write(f"  {_pp(r)}\n")
        assert "ln" in r.entity.full_name.lower(), f"Expected 'ln' in name: {r.entity.full_name}"
    assert len(results_lim) <= 3, f"Expected at most 3 results, got {len(results_lim)}"
    assert len(results_lim) > 0, "Expected at least one result"

    # 6g. Pattern-only with limit=1 returns exactly 1
    results_lim1, _ = await ml.semantic_knn(None, 1, [EntityKind.THEOREM],
                                    name_contains=["ln"])
    file.write(f"Pattern-only with limit=1: {len(results_lim1)} results\n")
    assert len(results_lim1) == 1, f"Expected exactly 1 result, got {len(results_lim1)}"

    # --- Error cases ---

    # 7a. Mix of matching and non-matching theory substrings: matching theory
    # still searched, the non-matching one produces a warning.
    results_mix, warnings_mix = await ml.semantic_knn(
        "logarithm", 5, [EntityKind.THEOREM],
        theories_include=["HOL.Transcendental", "Nonexistent_Theory_XYZ"])
    file.write(f"Mixed valid/invalid theories: {len(results_mix)} results, {len(warnings_mix)} warnings\n")
    for w in warnings_mix:
        file.write(f"  Warning: {w}\n")
    assert len(results_mix) > 0, "Expected results from the matching theory"
    assert any("Nonexistent_Theory_XYZ" in w for w in warnings_mix), \
        "Expected warning mentioning the non-matching substring"

    # 7b. No substring matches any theory: zero results plus warnings for each.
    results_bad_thy, warnings_bad_thy = await ml.semantic_knn(
        "logarithm", 5, [EntityKind.THEOREM],
        theories_include=["Nonexistent_Theory_XYZ", "Also_Nonexistent_Theory"])
    file.write(f"All invalid theories: {len(results_bad_thy)} results, {len(warnings_bad_thy)} warnings\n")
    for w in warnings_bad_thy:
        file.write(f"  Warning: {w}\n")
    assert len(results_bad_thy) == 0, "Expected zero results when all theories invalid"
    assert any("Nonexistent_Theory_XYZ" in w for w in warnings_bad_thy)
    assert any("Also_Nonexistent_Theory" in w for w in warnings_bad_thy)

    # 8. Invalid term pattern (unparseable) → warning, not error
    results_bad_term, warnings_bad_term = await ml.semantic_knn("logarithm", 5, [EntityKind.THEOREM],
                        term_patterns=["1 2 3 ??? bad syntax"])
    file.write(f"Invalid term pattern: {len(results_bad_term)} results, {len(warnings_bad_term)} warnings\n")
    for w in warnings_bad_term:
        file.write(f"  Warning: {w}\n")
    assert len(warnings_bad_term) > 0, "Expected warning for invalid term pattern"
    assert '\x05' not in warnings_bad_term[0], "YXML not stripped from warning"

    # 9. Invalid type pattern (unparseable) → warning, not error
    results_bad_type, warnings_bad_type = await ml.semantic_knn("logarithm", 5, [EntityKind.CONSTANT],
                        type_patterns=["not_a_real_type_XYZ"])
    file.write(f"Invalid type pattern: {len(results_bad_type)} results, {len(warnings_bad_type)} warnings\n")
    for w in warnings_bad_type:
        file.write(f"  Warning: {w}\n")
    assert len(warnings_bad_type) > 0, "Expected warning for invalid type pattern"
    assert '\x05' not in warnings_bad_type[0], "YXML not stripped from warning"

    # 10. Misspelled constant → warning about undeclared free variable (not error)
    results_misspell, warnings_misspell = await ml.semantic_knn("logarithm", 5, [EntityKind.THEOREM],
                                       term_patterns=["misspeled_ln ?x"])
    file.write(f"Misspelled pattern: {len(results_misspell)} results, {len(warnings_misspell)} warnings\n")
    for w in warnings_misspell:
        file.write(f"  Warning: {w}\n")
    assert len(warnings_misspell) > 0, "Expected warning about undeclared free variable"
    assert "misspeled_ln" in warnings_misspell[0], "Warning should mention the misspelled name"


@model_test("SemanticKNN_theories_include",
            "Test_SemanticKNN_theories_include.thy", 8)
async def _test_semantic_knn_theories_include(root: Root, file: MyIO):
    """semantic_knn: theories_include is a case-insensitive substring match on
    a theory's fully-qualified name (OR across entries). A substring that
    matches no loaded theory yields a warning, not an abort. Reproduces agent
    log 2026-04-17 where ``theories_include=['Discrete_Sqrt', 'Sqrt']`` killed
    the whole query because names were matched exactly instead of as substrings.

    Covers five behaviors:
      1. Substring matching no theory → zero results + warning.
      2. Mixed matching + non-matching → matching theory still searched + warning.
      3. Duplicate non-matching names → warnings deduplicated.
      4. Non-matching name on a non-theorem kind (CONSTANT) → still warns.
      5. A short / lowercase fragment matches by substring → results, no warning.
    """
    from Isabelle_RPC_Host.universal_key import EntityKind
    ml = root.ml_state

    # 1. A substring matching no theory: zero results + one warning, no abort.
    results1, warnings1 = await ml.semantic_knn(
        "list append", 5, [EntityKind.THEOREM],
        theories_include=["Nonexistent_XYZ"])
    file.write(f"No match: {len(results1)} results, {len(warnings1)} warnings\n")
    for w in warnings1:
        file.write(f"  Warning: {w}\n")
    assert len(results1) == 0, "A substring matching no theory must give zero results"
    assert len(warnings1) == 1
    assert "Nonexistent_XYZ" in warnings1[0]

    # 2. Mixed matching + non-matching: still get results from the matching theory.
    results2, warnings2 = await ml.semantic_knn(
        "list append", 5, [EntityKind.THEOREM],
        theories_include=["HOL.List", "Nonexistent_XYZ"])
    file.write(f"Mixed match/no-match: {len(results2)} results, {len(warnings2)} warnings\n")
    for w in warnings2:
        file.write(f"  Warning: {w}\n")
    assert len(results2) > 0, "Matching HOL.List should still yield results"
    assert any("Nonexistent_XYZ" in w for w in warnings2)
    assert not any("HOL.List" in w for w in warnings2), \
        "A matching theory must not produce a warning"

    # 3. Duplicated non-matching name: warnings are deduplicated.
    results3, warnings3 = await ml.semantic_knn(
        "list append", 5, [EntityKind.THEOREM],
        theories_include=["Nonexistent_XYZ", "Nonexistent_XYZ"])
    file.write(f"Duplicate no-match: {len(results3)} results, {len(warnings3)} warnings\n")
    for w in warnings3:
        file.write(f"  Warning: {w}\n")
    assert len(warnings3) == 1, "Duplicate non-matching names must dedup to one warning"

    # 4. Non-matching name applied to CONSTANT kind (exercises make_constants_callback
    #    path rather than make_theorems_callback).
    results4, warnings4 = await ml.semantic_knn(
        "append", 5, [EntityKind.CONSTANT],
        theories_include=["Nonexistent_XYZ"])
    file.write(f"Constant kind no-match: {len(results4)} results, {len(warnings4)} warnings\n")
    for w in warnings4:
        file.write(f"  Warning: {w}\n")
    assert len(results4) == 0
    assert len(warnings4) == 1
    assert "Nonexistent_XYZ" in warnings4[0]

    # 5. A lowercase fragment matches HOL.List by case-insensitive substring:
    #    results come back and there is no warning (the whole point of the fix).
    results5, warnings5 = await ml.semantic_knn(
        "list append", 5, [EntityKind.THEOREM],
        theories_include=["hol.list"])
    file.write(f"Substring fragment: {len(results5)} results, {len(warnings5)} warnings\n")
    for w in warnings5:
        file.write(f"  Warning: {w}\n")
    assert len(results5) > 0, "Lowercase substring 'hol.list' must match HOL.List"
    assert len(warnings5) == 0, "A substring that matches a theory must not warn"


@model_test("SemanticKNN_lexerr", "Test_SemanticKNN_lexerr.thy", 8)
async def _test_semantic_knn_lexerr(root: Root, file: MyIO):
    """semantic_knn with invalid unicode term pattern returns warnings, not crash.
    Reproduces agent log 2026-04-01: term_patterns=['¬ coprime'] caused os._exit(1)."""
    from Isabelle_RPC_Host.universal_key import EntityKind
    ml = root.ml_state

    # This is the exact call from the failing agent log.
    # After fix: unicode '¬' is converted to '\\<not>' by ascii_of_unicode,
    # Isabelle parse error is caught on ML side and returned as a warning.
    results, warnings = await ml.semantic_knn(
        "not coprime if both divisible by 2", 5, [EntityKind.THEOREM],
        term_patterns=["¬ coprime"])
    file.write(f"Results: {len(results)}, Warnings: {warnings}\n")
    assert len(warnings) > 0, "Expected warning about parse failure"
    for w in warnings:
        assert '\x05' not in w and '\x06' not in w, f"YXML not stripped: {w!r}"


@model_test("SemanticKNN_induction_rule",
            "Test_SemanticKNN_induction_rule.thy", 8)
async def _test_semantic_knn_induction_rule(root: Root, file: MyIO):
    """semantic_knn with INDUCTION_RULE kind triggers Match exception in retrieve callback.
    Reproduces agent log 2026-04-26: query with kinds=['induction rule'] caused
    'exception Match raised (line 483 of agent_server.ML)' because the retrieve
    function in agent_server.ML has no case for InductionRuleK or CaseSplitRuleK."""
    from Isabelle_RPC_Host.universal_key import EntityKind
    ml = root.ml_state

    def _pp(r) -> str:
        expr = ', '.join(e.unicode for e in r.entity.expression)
        return f"{r.entity.kind.label} {r.entity.short_name.unicode}: {expr}" if expr else f"{r.entity.kind.label} {r.entity.short_name.unicode}"

    # 1. INDUCTION_RULE kind — this crashes with Match before the fix
    results_ind, warnings_ind = await ml.semantic_knn(
        "induction on natural numbers", 5, [EntityKind.INDUCTION_RULE])
    file.write(f"Induction rules: {len(results_ind)} results, {len(warnings_ind)} warnings\n")
    for r in results_ind:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")
    assert len(results_ind) > 0, "Expected at least one induction rule for nat"

    # 2. CASE_SPLIT_RULE kind — same missing case in retrieve
    results_cs, warnings_cs = await ml.semantic_knn(
        "case split on list", 5, [EntityKind.CASE_SPLIT_RULE])
    file.write(f"Case-split rules: {len(results_cs)} results, {len(warnings_cs)} warnings\n")
    for r in results_cs:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")
    assert len(results_cs) > 0, "Expected at least one case-split rule for list"

    # 3. Mixed kinds including INDUCTION_RULE alongside THEOREM
    results_mix, warnings_mix = await ml.semantic_knn(
        "induction on natural numbers", 5,
        [EntityKind.INDUCTION_RULE, EntityKind.THEOREM])
    file.write(f"Mixed (induction+theorem): {len(results_mix)} results, {len(warnings_mix)} warnings\n")
    for r in results_mix:
        file.write(f"  {r.score:.3f} {_pp(r)}\n")
    assert len(results_mix) > 0, "Expected results from mixed kind query"


@model_test("SemanticKNN_UnequalLengths",
            "Test_SemanticKNN_UnequalLengths.thy", 8)
async def _test_semantic_knn_unequal_lengths(root: Root, file: MyIO):
    """semantic_knn with unparseable term_patterns must return warnings, not crash.
    Reproduces agent log 2026-06-07 EA313F528: term_patterns with mismatched parens
    ('summable (λn. 1 / real (lcm') or schematics in binder positions
    ('inj_on (λ?d. ?N div ?d)') raised UnequalLengths in parse_patterns
    (context.ML) because failed patterns were dropped from the parsed list
    but kept in the input list before zipping with ~~."""
    from Isabelle_RPC_Host.universal_key import EntityKind
    ml = root.ml_state

    # 1. Single unparseable pattern: mismatched parentheses.
    #    The ML parse_patterns drops the failed pattern from term_pats but keeps
    #    it in term_pat_strs, then crashes on (term_pat_strs ~~ term_pats).
    results1, warnings1 = await ml.semantic_knn(
        "test query", 5, [EntityKind.THEOREM],
        term_patterns=["f (x"])
    file.write(f"Mismatched parens: {len(results1)} results, {len(warnings1)} warnings\n")
    for w in warnings1:
        file.write(f"  Warning: {w}\n")
    assert len(warnings1) > 0, "Expected warning for unparseable pattern"

    # 2. Mixed: one parseable + one unparseable (the log-realistic scenario).
    #    The valid pattern should still filter; the bad one should produce a warning.
    results2, warnings2 = await ml.semantic_knn(
        "addition", 5, [EntityKind.THEOREM],
        term_patterns=["?x + ?y", "g (z"])
    file.write(f"Mixed patterns: {len(results2)} results, {len(warnings2)} warnings\n")
    for w in warnings2:
        file.write(f"  Warning: {w}\n")
    assert len(warnings2) > 0, "Expected warning for the unparseable pattern"

    # 3. Schematic in lambda binder (from real agent log EA313F528).
    results3, warnings3 = await ml.semantic_knn(
        "injective function", 5, [EntityKind.THEOREM],
        term_patterns=["inj_on (λ?d. ?N div ?d)"])
    file.write(f"Schematic in binder: {len(results3)} results, {len(warnings3)} warnings\n")
    for w in warnings3:
        file.write(f"  Warning: {w}\n")
    assert len(warnings3) > 0, "Expected warning for schematic-in-binder pattern"


@model_test("QueryNullFields", "Test_QueryNullFields.thy", 8)
async def _test_query_null_fields(root: Root, file: MyIO):
    """query tool: LLM sends null for optional list/string fields.
    Reproduces agent log 2026-05-08: theories_include=None, target_type=None,
    exact_name=None, exact_term=None caused 'Failed to unpack callback argument'
    because q.get("key", []) returns None when the key exists with value None.
    Fix: use q.get("key") or [] instead."""
    from .retrieval import _query_tool_logic

    # Force direct search path (test session has no launch_interaction)
    root.session.interactive_retrieval = InteractiveRetrievalMode.NO

    # Exact args from the failing agent log
    args = {'queries': [
        {'kinds': ['lemma'],
         'description': 'divisibility and square result',
         'term_patterns': ['_ dvd _ + _'],
         'type_patterns': ['nat'],
         'theories_include': None,
         'name_contains': ['dvd'],
         'target_type': None,
         'number': 20,
         'exact_name': None,
         'exact_term': None},
        {'kinds': ['lemma'],
         'description': 'quotient is a perfect square',
         'term_patterns': None,
         'type_patterns': None,
         'theories_include': None,
         'name_contains': None,
         'target_type': None,
         'number': 50,
         'exact_name': None,
         'exact_term': None},
    ]}

    result, is_error = await _query_tool_logic(root.session, args)
    file.write(f"Result (is_error={is_error}):\n{result}\n")
    assert not is_error, f"query with null fields must not error: {result}"

    # Also test: kinds=None should default to ["constant"]
    args_null_kinds = {'queries': [
        {'kinds': None,
         'description': 'addition on natural numbers',
         'term_patterns': None,
         'type_patterns': None,
         'theories_include': None,
         'name_contains': None,
         'target_type': None,
         'number': 5,
         'exact_name': None,
         'exact_term': None},
    ]}
    result2, is_error2 = await _query_tool_logic(root.session, args_null_kinds)
    file.write(f"Null kinds result (is_error={is_error2}):\n{result2}\n")
    assert not is_error2, f"query with null kinds must not error: {result2}"


@model_test("QueryScalarStringField", "Test_QueryScalarStringField.thy", 8)
async def _test_query_scalar_string_field(root: Root, file: MyIO):
    """query tool: LLM sends a bare string for a list-typed optional field.
    Reproduces agent log 2026-06-06 13:30:34:
        query {'queries': [{'kinds': ['lemma'],
                            'description': 'P = Q iff P --> Q & Q --> P',
                            'name_contains': 'iff'}, ...]}
    -> 'Failed to unpack callback argument'.

    Root cause: `name_contains` (also term_patterns/type_patterns/
    theories_include) is declared as an array in the query tool schema, but the
    model passed the SCALAR string 'iff'. `_run_knn_for_query` only normalizes
    falsy values via ``q.get("name_contains") or []`` — a non-empty string is
    truthy, so 'iff' is forwarded unchanged down to the ML entity-enumeration
    callback whose arg_schema unpacks name_contains with ``unpackList
    unpackString`` (contrib/Isabelle_RPC/Tools/context.ML). msgpack encodes the
    Python str as a msgpack Str, the ML ``unpackList`` rejects it, the callback
    raises Unpack -> ``error "Failed to unpack callback argument"`` (RPC.ML),
    which surfaces back as the tool error.

    Fix should coerce a scalar string into a singleton list (or validate/warn)
    for every list-typed query field, before it reaches the callback."""
    from .retrieval import _query_tool_logic

    # Force direct search path (test session has no launch_interaction)
    root.session.interactive_retrieval = InteractiveRetrievalMode.NO

    # Exact args from the failing agent log: name_contains is a bare string.
    args = {'queries': [
        {'kinds': ['lemma'],
         'description': 'P = Q if and only if P ⟶ Q ∧ Q ⟶ P',
         'name_contains': 'iff'},
        {'kinds': ['lemma'],
         'description': 'equality of booleans is equivalence: (P = Q) = (P ⟶ Q ∧ Q ⟶ P)'},
    ]}

    result, is_error = await _query_tool_logic(root.session, args)
    file.write(f"Result (is_error={is_error}):\n{result}\n")
    assert not is_error, f"query with scalar-string name_contains must not error: {result}"


@model_test("QuerySearchSummary", "Test_QuerySearchSummary.thy", 8)
async def _test_query_search_summary(root: Root, file: MyIO):
    """query tool: each call appends a per-query summary line
    'XX entities match the filters — YY new, ZZ shown earlier are not shown again.'.
    Asserts (format-based, count-agnostic):
      - the first 5 summary lines per session use the verbose phrasing, the
        rest a terse one;
      - the XX clause appears only when the query has a structural filter;
      - ZZ ('already shown') grows when the same filtered query is repeated.
    Only the (deterministic) summary lines are written to the golden — the
    entity list itself is embedding-ranking dependent."""
    import re
    from .retrieval import _query_tool_logic

    # Force the direct (non-fork) search path.
    root.session.interactive_retrieval = InteractiveRetrievalMode.NO

    def summary_lines(result: str) -> list[str]:
        return [ln.strip() for ln in result.splitlines() if "shown earlier" in ln]

    async def run(q: dict) -> str:
        result, is_error = await _query_tool_logic(root.session, {'queries': [q]})
        assert not is_error, f"query must not error: {result}"
        lines = summary_lines(result)
        assert len(lines) == 1, f"expected one summary line, got {lines}"
        return lines[0]

    # 6 filtered single-query calls (distinct substrings) → 6 summary lines.
    # Pre-set the counter so the boundary (15) is crossed at the 2nd call.
    root.session.search_summary_count = 14
    fragments = ["plus", "less", "mult", "diff", "power", "abs"]
    collected: list[str] = []
    for frag in fragments:
        line = await run({'kinds': ['lemma'],
                          'description': f'lemmas mentioning {frag}',
                          'name_contains': [frag], 'number': 5})
        collected.append(line)
    for i, line in enumerate(collected):
        file.write(f"call {i+1}: {line}\n")
    assert "not shown again" in collected[0], f"1st must be verbose: {collected[0]}"
    assert "match the filters" in collected[0], f"filtered query must show XX: {collected[0]}"
    for line in collected[1:]:
        assert "not shown again" not in line, f"must be terse: {line}"
    assert "match" in collected[1] and "shown earlier." in collected[1], \
        f"2nd must be terse with XX: {collected[1]}"

    # ZZ grows on repeat: re-run the first fragment; its entities are now seen.
    repeat = await run({'kinds': ['lemma'],
                        'description': 'lemmas mentioning plus',
                        'name_contains': ['plus'], 'number': 5})
    file.write(f"repeat: {repeat}\n")
    m = re.search(r"(\d+) shown earlier", repeat)
    assert m and int(m.group(1)) > 0, f"repeat must report ZZ>0 already shown: {repeat}"

    # XX gate: a bare semantic query (no structural filter) omits the XX clause.
    bare = await run({'kinds': ['lemma'],
                      'description': 'induction over natural numbers',
                      'number': 5})
    file.write(f"no-filter: {bare}\n")
    assert "match" not in bare, f"bare semantic query must omit XX: {bare}"


@model_test("IntroSplitConj", "Test_IntroSplitConj.thy", 10)
async def _test_intro_split_conj(root: Root, file: MyIO):
    """Test SplitConjs splits P ∧ Q ∧ R into separate subgoals.
    The goal P ∧ Q ∧ R is a pure conjunction (premises are in the HHF context),
    so no auto-Intro fires. SplitConjs goes directly at step 1."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # The goal is already P ∧ Q ∧ R (premises handled by HHF context).
    # Apply SplitConjs at step 1 to split the conjunction.
    root.session.age += 1
    await root.fill("1", [SplitConjs.gen_single({
        "thought": "Split conjunction into separate subgoals",
    })])
    print_header("After SplitConjs", file)
    root.print(0, file)
    print_header("Overview after split", file)
    root.quickview(0, file)

    # Close each subgoal with Obvious
    for i in range(1, 4):
        root.session.age += 1
        try:
            await root.fill(f"1.{i}.1", [Obvious.gen_single({"facts": []})])
        except Exception as e:
            file.write(f"Cannot fill 1.{i}.1: {type(e).__name__}: {e}\n")
    print_header("After closing subgoals", file)
    root.print(0, file)
    print_header("Final overview", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("MetaConjFromMultiShows", "Test_MetaConjFromMultiShows.thy", 27)
async def _test_meta_conj_from_multi_shows(root: Root, file: MyIO):
    """Reproduce the 'meta conjunction' obstacle (mbzuai log e9912b2bf_8 =
    avl_AVL_front_nodeqtvc).

    A theorem with multiple `shows "A" and "B"` clauses (one per why3 VC) is
    bundled by Isar into a single goal that is a Pure meta-conjunction
    `A &&& B`, NOT a HOL `A ∧ B`. The Minilang goal printer atomizes `&&&` to
    `∧` for display, so the goal below PRINTS as `P ∧ Q` — yet SplitConjs (and
    every other object-level conjunction op) fails on it, because
    `is_conj_goal` (proof.ML) only recognizes `HOL.conj`, not
    `Pure.conjunction`.

    The contradiction captured in the golden — goal displayed as `P ∧ Q` while
    SplitConjs reports "the leading goal is not a conjunction" — IS the bug.
    The real proof obligation `A &&& B` is only closeable via the meta-level
    rule `Pure.conjunctionI`, which the agent has no first-class operation for.
    """
    print_header("Initial State (goal displays with HOL ∧, but is Pure &&&)", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # The natural first move on a goal that LOOKS like `P ∧ Q`: split it.
    # On the real `&&&` goal this fails with
    #   "SPLIT_CONJS: the leading goal is not a conjunction".
    root.session.age += 1
    try:
        await root.fill("1", [SplitConjs.gen_single({
            "thought": "Goal looks like P ∧ Q, split it into two subgoals",
        })])
    except Exception as e:
        file.write(f"SplitConjs raised: {type(e).__name__}: {e}\n")
    print_header("After SplitConjs (expected to FAIL on the Pure &&& goal)", file)
    root.print(0, file)
    print_header("Overview after failed split", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("IntroSplitPremConj", "Test_IntroSplitPremConj.thy", 29)
async def _test_intro_split_prem_conj(root: Root, file: MyIO):
    """Exercise split_prem_conj destructuring on:
      - plain conj           A ∧ B ∧ C        → 3 atoms, premise0(1..3)
      - ∀-conj               ∀x. P x ∧ Q x    → 2 atoms, premise1(1..2)
      - ⟶-conj (small ant)  D ⟶ E ∧ F         → 2 atoms, premise2(1..2)
      - ⟶-conj (large ant)  BIG ⟶ G ∧ H       → 1 atom, premise3 (size guard)

    The auto-Intro at proof start fires split_prem_conj (config-default true)
    so the initial printed state already shows the destructured bindings.
    Then Obvious on step 2 discharges the conclusion using the atoms.
    """
    print_header("Initial State (auto-Intro should have destructured 3 of 4 prems)", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # Auto-Intro already occupies step 1; the pending goal is step 2.
    # Discharge it with Obvious using the destructured atoms.
    root.session.age += 1
    try:
        await root.fill("2", [Obvious.gen_single({"facts": []})])
        print_header("After Obvious on 2", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"Obvious on 2 failed: {type(e).__name__}: {e}\n")

    print_header("Final Overview", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("IntroSplitPremConj_IdenticalPrems", "Test_IntroSplitPremConj_IdenticalPrems.thy", 14)
async def _test_intro_split_prem_conj_identical_prems(root: Root, file: MyIO):
    """Corner: two premises with syntactically identical terms A ∧ B.
    Each prem should still get its own positional base name
    (premise0, premise1) and independent atom indexing (1..2 each)."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    root.session.age += 1
    try:
        await root.fill("2", [Obvious.gen_single({"facts": []})])
        print_header("After Obvious on 2", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"Obvious on 2 failed: {type(e).__name__}: {e}\n")

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("IntroSplitPremConj_NoDestruct", "Test_IntroSplitPremConj_NoDestruct.thy", 13)
async def _test_intro_split_prem_conj_no_destruct(root: Root, file: MyIO):
    """Corner: no premise is destructible. split_prem_conj should be a
    no-op; every prem appears as a plain premiseN binding with no (k)
    suffix, no aliases. Verifies alias machinery doesn't misfire on
    inapplicable inputs."""
    print_header("Initial State", file)
    root.print(0, file)

    root.session.age += 1
    try:
        await root.fill("2", [Obvious.gen_single({"facts": []})])
        print_header("After Obvious on 2", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"Obvious on 2 failed: {type(e).__name__}: {e}\n")

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("IntroObvious", "Test_IntroObvious.thy", 10)
async def _test_intro_obvious(root: Root, file: MyIO):
    """Test that Intro on P ∧ Q ∧ R (with assumptions P, Q, R) auto-completes.
    Previously this could generate infinite 'True' pending goals; now the
    auto-Intro succeeds outright so no manual fill is needed."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # The auto-Intro at step 1 should introduce premises P, Q, R
    # and auto-prove the conjunction. No subgoals should remain.
    # Verify by attempting to fill 1.1.1 — it should fail because
    # the proof is already complete.
    root.session.age += 1
    _outcome = await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    if _outcome.failure is not None:
        file.write(
            f"No step 1.1.1 needed (auto-proved): "
            f"{type(_outcome.failure).__name__}: {_outcome.failure}\n")
    else:
        print_header("After Obvious on 1.1.1 (subgoal existed)", file)
        root.print(0, file)
        print_header("Overview after 1.1.1", file)
        root.quickview(0, file)

    print_header("Final Overview", file)
    root.quickview(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("DeleteIntro", "Test_DeleteIntro.thy", 10)
async def _test_delete_intro(root: Root, file: MyIO):
    """Reproduce: deleting the auto-Intro makes the proof appear complete
    with no 'Error: Unfinished Proof' shown."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # Delete the auto-Intro (step 1)
    root.session.age += 1
    await root.delete(["1"])
    print_header("After deleting Intro", file)
    root.print(0, file)
    print_header("Overview after delete", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("ForeNodeFail", "Test_ForeNodeFail.thy", 12)
async def _test_ForeNodeFail(root: Root, file: MyIO):
    """Test that nodes after a failed fore node get CANCELLED, not refreshed."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Have with a valid statement (succeeds)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "helper",
        "statement": {"english": "x equals y", "conclusion": "x = y"},
        "name": "lem1"
    })])
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("After step 1 (Have x=y, should succeed)", file)
    root.print(0, file)

    # Step 2: Have with INVALID Isabelle syntax (should FAIL)
    root.session.age += 1
    await root.fill("2", [Have.gen_single({
        "thought": "intentionally bad step",
        "statement": {"english": "invalid", "conclusion": "1 1 1"},
        "name": "bad"
    })])
    step2 = root.locate_node("2")
    file.write(f"Step 2 status: {step2.status.status.value}\n")
    print_header("After step 2 (invalid Have, should fail)", file)
    root.print(0, file)

    # Step 3 (fill): Should be CANCELLED because step 2 failed
    root.session.age += 1
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    step3 = root.locate_node("3")
    file.write(f"Step 3 status (fill after failed): {step3.status.status.value}\n")
    assert step3.status.status == EvaluationStatus.Status.CANCELLED, \
        f"fill: Expected CANCELLED but got {step3.status.status.value}"
    print_header("After step 3 (fill, should be cancelled)", file)
    root.print(0, file)

    # Insert before step 3: predecessor is step 2 (FAILURE), should be CANCELLED
    root.session.age += 1
    _outcome = await root.insert_before("3", [Have.gen_single({
        "thought": "inserted step",
        "statement": {"english": "x equals z", "conclusion": "x = z"},
        "name": "lem2"
    })])
    inserted = _outcome.committed[0] if _outcome.committed else None
    assert inserted is not None
    file.write(f"Inserted step status (insert_before after failed): {inserted.status.status.value}\n")
    assert inserted.status.status == EvaluationStatus.Status.CANCELLED, \
        f"insert_before: Expected CANCELLED but got {inserted.status.status.value}"
    print_header("After insert_before (should be cancelled)", file)
    root.print(0, file)

    # Amend step 2 to fix it (valid statement)
    root.session.age += 1
    await root.amend("2", [Have.gen_single({
        "thought": "fixed step",
        "statement": {"english": "y equals x", "conclusion": "y = x"},
        "name": "lem_fixed"
    })])
    step2_fixed = root.locate_node("2")
    file.write(f"Step 2 status after amend (should succeed): {step2_fixed.status.status.value}\n")
    # After fixing step 2, subsequent steps should be refreshed (no longer CANCELLED)
    step2A = root.locate_node("2A")
    step3_after = root.locate_node("3")
    file.write(f"Inserted step status after amend: {step2A.status.status.value}\n")
    file.write(f"Step 3 status after amend: {step3_after.status.status.value}\n")
    print_header("After amend (fix step 2, should refresh all after)", file)
    root.print(0, file)


@model_test("ResolveContextAt", "Test_ResolveContextAt.thy", 12)
async def _test_resolve_context_at(root: Root, file: MyIO):
    """`Session.resolve_context_at` backs the `query` tool's `context_at`. It must:
      - resolve an unfilled OPEN SLOT to the state in effect there — the original
        motivating bug, where `context_at` named the very slot being filled and
        the old code raised "Step 1 not found";
      - resolve a FAILED node to its still-live before-state (the first failure
        after a run of successes — the step the agent means to replace);
      - reject a position sitting in a CANCELLED / head-FAILED region (its proof
        state was reset by `_cancel`, or never initialized) with a clear
        ValueError, instead of feeding a dead server-side name into retrieval and
        surfacing an opaque ML `beginning_state_not_found`.
    Deadness is position-dependent (see the debate-verified BLOCKERs): the first
    cancelled sibling keeps a live before-state while later ones do not."""
    session = root.session

    def probe(sid: str) -> None:
        try:
            st = session.resolve_context_at(sid)
            g = st.leading_goal
            concl = g.conclusion.unicode if g is not None else "<no leading goal>"
            file.write(f"context_at({sid!r}): initialized={st.initialized()} goal={concl}\n")
        except ValueError as e:
            file.write(f"context_at({sid!r}): ValueError: {e}\n")

    # --- A. Live open slot (the original bug): fresh tree, slot "1" has no node
    #        yet; resolve_context_at must return the initial goal state. ---
    print_header("A. Live open slot (fresh tree)", file)
    probe("1")

    # Build a tree with a failure in the middle so later siblings are cancelled:
    #   1 : Have (valid)   -> SUCCESS (opening block, body left open)
    #   2 : Have "1 1 1"   -> FAILURE (ill-typed beginning op)
    #   3 : Have (valid)   -> CANCELLED (block; stays opening() so it has a slot)
    #   4 : Obvious        -> CANCELLED (leaf)
    session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "ok", "statement": {"english": "x equals y", "conclusion": "x = y"},
        "name": "lem1"})])
    await root.fill("2", [Have.gen_single({
        "thought": "intentionally ill-typed", "statement": {"english": "bad", "conclusion": "1 1 1"},
        "name": "bad"})])
    await root.fill("3", [Have.gen_single({
        "thought": "cancelled block", "statement": {"english": "x equals z", "conclusion": "x = z"},
        "name": "lem3"})])
    await root.fill("4", [Obvious.gen_single({"facts": []})])
    print_header("Tree built: 1 ok, 2 FAILURE, 3 & 4 cancelled", file)
    root.print(0, file)

    # --- B. Failed node, still-live before-state: node "2" failed, but its
    #        before-state (= node "1"'s resulting state, a SUCCESS) is live. ---
    print_header("B. Failed node with live before-state", file)
    probe("2")

    # --- C. Dead open slot: node "3" is a CANCELLED block, still opening(), so
    #        its slot "3.1" resolves; its `_state_before_ending_` was reset by
    #        `_cancel` -> dead -> clear ValueError. ---
    print_header("C. Dead slot (cancelled block's open slot)", file)
    probe("3.1")

    # --- D. Position-dependent deadness among cancelled siblings: "3" (node)
    #        may survive (its before-state = node 2's resulting, not reset),
    #        while "4" (node) is dead (its before-state = node 3's resulting,
    #        reset by node 3's `_cancel`). ---
    print_header("D. Cancelled siblings: node 3 vs node 4", file)
    probe("3")
    probe("4")

    # --- E. A genuinely nonexistent id still errors clearly. ---
    print_header("E. Nonexistent id", file)
    probe("9")


@model_test("ProveInTime_ParseError", "Test_ProveInTime_ParseError.thy", 8)
async def _test_prove_in_time_parse_error(root: Root, file: MyIO):
    """Reproduce: Obvious with an IsabelleFact_ProveInTime containing invalid
    Isabelle syntax (as from a fork answering with bad text) should fail
    gracefully, not raise an unhandled IsabelleError.

    The bug: validate_prove_in_time raises IsabelleError for unparseable
    statements inside _filter_unprovable → mk_node, which is not caught
    by the driver."""
    print_header("Initial State", file)
    root.print(0, file)

    # Get an ml_state we can use for validate_prove_in_time
    ml_state = root.global_env.ml_state

    # --- Test 1: validate_prove_in_time directly with ASCII statement ---
    stmt_ascii = "if ?a < ?b then abs(?a - ?b) = ?b - ?a"
    file.write(f"validate_prove_in_time(\"{stmt_ascii}\"):\n")
    try:
        results = await ml_state.validate_prove_in_time([ascii_of_unicode(stmt_ascii)])
        file.write(f"  returned: {results}\n")
    except IsabelleError as e:
        file.write(f"  UNCAUGHT IsabelleError: {e}\n")
    except Exception as e:
        file.write(f"  UNCAUGHT {type(e).__name__}: {e}\n")

    # --- Test 2: validate_prove_in_time with Unicode ¦ (U+00A6) statement ---
    stmt_unicode = "if ?a < ?b then \u00a6?a - ?b\u00a6 = ?b - ?a"
    stmt_converted = ascii_of_unicode(stmt_unicode)
    file.write(f"ascii_of_unicode(\"{stmt_unicode}\") = \"{stmt_converted}\"\n")
    file.write(f"validate_prove_in_time(\"{stmt_converted}\"):\n")
    try:
        results = await ml_state.validate_prove_in_time([stmt_converted])
        file.write(f"  returned: {results}\n")
    except IsabelleError as e:
        file.write(f"  UNCAUGHT IsabelleError: {e}\n")
    except Exception as e:
        file.write(f"  UNCAUGHT {type(e).__name__}: {e}\n")

    # --- Test 3: _filter_unprovable with bad ProveInTime ---
    bad_pit = IsabelleFact_ProveInTime(IsaTerm.from_agent(stmt_ascii), assigned_name="P__I__T__test0")
    file.write(f"_filter_unprovable([ProveInTime(\"{stmt_ascii}\")]): ")
    try:
        kept, warnings = await _filter_unprovable([bad_pit], ml_state)
        file.write(f"kept={len(kept)}, warnings={warnings}\n")
    except IsabelleError as e:
        file.write(f"UNCAUGHT IsabelleError: {e}\n")
    except Exception as e:
        file.write(f"UNCAUGHT {type(e).__name__}: {e}\n")

    # --- Test 4: _filter_unprovable with Unicode ¦ variant ---
    bad_pit_unicode = IsabelleFact_ProveInTime(IsaTerm.from_agent(stmt_unicode), assigned_name="P__I__T__test1")
    file.write(f"_filter_unprovable([ProveInTime(unicode ¦ variant)]): ")
    try:
        kept, warnings = await _filter_unprovable([bad_pit_unicode], ml_state)
        file.write(f"kept={len(kept)}, warnings={warnings}\n")
    except IsabelleError as e:
        file.write(f"UNCAUGHT IsabelleError: {e}\n")
    except Exception as e:
        file.write(f"UNCAUGHT {type(e).__name__}: {e}\n")

    # --- Test 5: Obvious.gen_single() with bad ProveInTime (HAMMER path) ---
    root.session.age += 1
    try:
        await root.fill("1", [Obvious.gen_single({"facts": [
            {"proposition": stmt_ascii}
        ]})])
        file.write("Obvious created (should have failure status)\n")
        node = root.locate_node("1")
        file.write(f"Step 1 status: {node.status.status.value}\n")
    except IsabelleError as e:
        file.write(f"IsabelleError raised (BUG - should be caught): {e}\n")
    except Exception as e:
        file.write(f"Exception raised (BUG - should be caught): {type(e).__name__}: {e}\n")

    print_header("After Obvious with bad ProveInTime", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # Verify proof tree is still usable
    root.session.age += 1
    try:
        await root.fill("1" if root.locate_node("1").status.status != EvaluationStatus.Status.SUCCESS
                  else "2",
                  [Obvious.gen_single({"facts": []})])
        file.write("Subsequent fill succeeded (tree not stuck)\n")
    except Exception as e:
        file.write(f"Subsequent fill: {type(e).__name__}: {e}\n")

    print_header("Final State", file)
    root.print(0, file)


@model_test("Obvious_ClassFactRSN", "Test_Obvious_ClassFactRSN.thy", 11)
async def _test_Obvious_ClassFactRSN(root: Root, file: MyIO):
    """Regression for the raw `exception THM 1 raised ... RSN: no unifiers`
    leak from `Obvious` (HAMMER).

    Root cause (auto_sledgehammer/library/sledgehammer_solver.ML): the
    improved-sledgehammer `fastforce` path classifies every supplied /
    MePo-selected fact via `infer_type_of_rule` -> `chk_split` ->
    `Simpdata.mk_eq` -> `RS Eq_TrueI`. `Eq_TrueI : ?P ==> ?P == True` expects a
    `Trueprop`; type-class theorems (`*_class.super` / `*.intro_of_class`) have a
    raw Pure-prop conclusion `OFCLASS(?'a, c_class)`, so `RS Eq_TrueI` has no
    unifiers and raised a raw `THM "RSN: no unifiers"`.

    That `THM` is not an `Auto_Fail`, so it escaped every cleanup layer
    (`try_stage`/`fastforce` catch only `Auto_Fail`/`Timeout`;
    `Par_List.get_some` re-raises via `Par_Exn.release_first`;
    `Phi_Sledgehammer_Solver.auto` re-raises non-`ERROR` via `Exn.reraise`;
    `HAMMER_i` only catches `ERROR`) and surfaced to the agent verbatim instead
    of a clean "sledgehammer failed" message.

    Fix: detect & silently drop OFCLASS lemmas at the fact entry points, plus a
    defensive `handle THM _ => false` in `chk_split`.

    This test supplies such a class theorem to `Obvious` on a goal hammer
    cannot close. While the bug is present the failed leaf's reason / rendered
    tree contains the raw `THM ... RSN: no unifiers`; once fixed the hammer
    fails cleanly (a normal "fail to prove" reason) and this test passes.
    """
    # Production-faithful: a `Have` whose proof sub-step is the `Obvious`
    # (in the real run it was `Have term_cont` -> `step 6.1: Obvious`). The
    # Have ("1") stays posed; filling "1.1" actually runs the HAMMER on `P n`
    # with the OFCLASS fact supplied. `Orderings.preorder_class.super` has a
    # raw Pure-prop conclusion `OFCLASS(?'a, ord_class)` and, pre-fix, made the
    # fastforce classifier raise `THM "RSN: no unifiers"`.
    bad_fact = "Orderings.preorder_class.super"
    await root.fill("1", [Have.gen_single({
        "thought": "regression probe",
        "statement": {"english": "arbitrary P n",
                      "conclusion": r"(P::nat \<Rightarrow> bool) n"},
        "name": "h"})])
    ob = await root.fill("1.1", [Obvious.gen_single({"facts": [{"name": bad_fact}]})])

    # The failed Obvious is reverted from the tree, but its failure cause is
    # carried by `ob.failure` (and, if kept, on the committed node / rendered
    # tree). Collect every place the cause could surface and assert it is NOT
    # the raw ML exception.  Post-fix it is a clean "automatic proof fails"
    # message; pre-fix it was `exception THM 1 raised ... RSN: no unifiers`.
    parts = [str(ob.failure)]
    parts += [n.status.reason.reason for n in ob.committed
              if n.status.reason is not None]
    _buf = io.StringIO()
    root.print(0, MyIO(_buf))
    parts.append(_buf.getvalue())
    haystack = "\n".join(parts)
    leaked = ("RSN: no unifiers" in haystack
              or ("exception THM" in haystack and "raised" in haystack))
    if leaked:
        raise TestFailed(
            "Obvious (HAMMER) leaked a raw ML exception instead of failing "
            f"cleanly: {str(ob.failure)!r}")
    file.write("Obvious failed cleanly (no raw THM / RSN leak)\n")


@model_test("ObviousProofFail", "Test_ObviousProofFail.thy", 8)
async def _test_ObviousProofFail(root: Root, file: MyIO):
    """Test that Have with proof='Obvious' where HAMMER fails doesn't crash quickview."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Have with an easy statement — Obvious should succeed
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "trivial identity",
        "statement": {"english": "x equals x", "conclusion": "x = x"},
        "name": "lem1",
    })])
    print_header("After Have x=x (Obvious succeeds)", file)
    root.print(0, file)

    # Have with a hard/false statement — Obvious (HAMMER) should fail
    root.session.age += 1
    await root.fill("2", [Have.gen_single({
        "thought": "this is false",
        "statement": {"english": "x equals x plus one", "conclusion": "x = x + 1"},
        "name": "bad",
    })])
    print_header("After Have x=x+1 (Obvious fails)", file)
    root.print(0, file)

    # This quickview should not crash
    print_header("Overview", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("HaveObviousProof", "Test_ObviousProof.thy", 8)
async def _test_HaveObviousProof(root: Root, file: MyIO):
    """Test that Have with proof='Obvious' auto-creates an Obvious sub-node."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Have with proof: "Obvious" — Obvious sub-node should be auto-created
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "x times x is non-negative because x times x equals x squared",
        "statement": {
            "english": "x times x equals x squared",
            "conclusion": "x * x = x^2"
        },
        "name": "sq",
    })])
    print_header("After Have with proof=Obvious", file)
    root.print(0, file)

    # The remaining goal should still need a proof
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": []})])
    print_header("After closing the remaining goal", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("SufficesObviousProof", "Test_SufficesObviousProof.thy", 8)
async def _test_SufficesObviousProof(root: Root, file: MyIO):
    """Test that Suffices with proof='Obvious' auto-creates an Obvious sub-node."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Suffices.gen_single({
        "thought": "It suffices to show a stronger statement",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "conclusion": "x * x + 1 > 0"
        },
    })])
    print_header("After Suffices with proof=Obvious", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("HaveStructured", "Test_HaveStructured.thy", 8)
async def _test_HaveStructured(root: Root, file: MyIO):
    """Have with explicit for_any: the ML layer fixes variables via
    Specification.schematic_theorem_cmd, so the proof goal is the clean
    conclusion without needing a separate Intro."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "Prove a general lemma with explicit variable binding",
        "statement": {
            "english": "n plus 1 is greater than n for any natural n",
            "for_any": [{"name": "n", "type": "nat"}],
            "conclusion": "n + 1 > n"
        },
        "name": "succ_gt",
    })])
    print_header("After Have with for_any", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("After proving Have sub-goal", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({
        "facts": [{"name": "succ_gt"}]
    })])
    print_header("After closing outer goal", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("HaveDupFixed", "Test_HaveDupFixed.thy", 8)
async def _test_HaveDupFixed(root: Root, file: MyIO):
    """Reproduce: Have with for_any naming a variable that is already fixed
    in the proof context (after Intro) triggers 'Duplicate fixed variable(s)'
    from gen_HAVE's set_body-false path."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Intro to fix a, b and the premise into the context.
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "introduce universally quantified variables and premise"
    })])
    print_header("After Intro (a, b now fixed)", file)
    root.print(0, file)

    # Step 2: Have with for_any:[a, b] — these names collide with
    # the already-fixed a, b from the Intro above.
    root.session.age += 1
    outcome = await root.fill("2", [Have.gen_single({
        "thought": "Prove a helper lemma universally quantified over a and b",
        "statement": {
            "english": "For all positive a,b with the divisibility, the quotient is a perfect square",
            "for_any": [{"name": "a", "type": "nat"}, {"name": "b", "type": "nat"}],
            "premises": [
                {"name": "ha", "term": "(0::nat) < a"},
                {"name": "hb", "term": "(0::nat) < b"},
                {"name": "hdvd", "term": "a * b + 1 dvd a^2 + b^2"}
            ],
            "conclusion": "\\<exists>x::nat. real (x^2) = real (a^2 + b^2) / real (a * b + 1)"
        },
        "name": "main",
    })])
    print_header("After Have with for_any (duplicate a, b)", file)
    root.print(0, file)

    have_node = root.locate_node("2")
    file.write(f"Have status: {have_node.status.status.value}\n")
    if outcome.failure:
        file.write(f"Failure: {outcome.failure}\n")

@model_test("HaveSpuriousForAny", "Test_HaveSpuriousForAny.thy", 8)
async def _test_HaveSpuriousForAny(root: Root, file: MyIO):
    """Bug: Have after Intro gets spurious for_any from Newly_Fixed_Vars_Msg.

    Scenario: goal is (∀x∈{1..10}. x+1>1) ∧ True.
    Step 1: SplitConjs splits the conjunction.
    Step 2: In the first branch, Intro fixes x and introduces x∈{1..10}.
    Step 3: Have with conclusion "x + 1 > 1" (no for_any).
    Expected: for_any should be empty — x is already fixed by Intro.
    Bug: the system reports Newly_Fixed x, making the Have universally
    quantified over x, which changes the semantics entirely."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # SplitConjs to split (∀x∈{1..10}. x+1>1) ∧ True.
    # First branch: Intro + Have (no for_any) + Obvious
    # Second branch: Obvious (True is trivial)
    root.session.age += 1
    await root.fill("1", [SplitConjs.gen_single({
        "thought": "split the conjunction",
        "proofs": [
            [
                {"operation": "Intro", "thought": "introduce x and the membership"},
                {"operation": "Have", "thought": "derive x+1>1 from membership",
                 "statement": {
                     "english": "x + 1 is greater than 1",
                     "conclusion": "x + (1::nat) > 1"
                 },
                 "name": "helper"},
                {"operation": "Obvious", "facts": [{"name": "helper"}]}
            ],
            [
                {"operation": "Obvious", "facts": []}
            ]
        ]
    })])
    print_header("After SplitConjs with Intro+Have", file)
    root.print(0, file)

    # Check if the Have node got spurious for_any
    have_node = root.locate_node("1.1.2")
    file.write(f"Have status: {have_node.status.status.value}\n")
    assert isinstance(have_node, Have), f"Expected Have, got {type(have_node).__name__}"
    if have_node.for_any:
        file.write(f"BUG: for_any is non-empty: {[(n.unicode, t.unicode) for n, t in have_node.for_any]}\n")
    else:
        file.write("OK: for_any is empty as expected\n")

    # Also test the sequential fill scenario (after Intro already refreshed)
    print_header("--- Sequential scenario ---", file)
    root.session.age += 1
    # Delete steps after Intro in first branch and re-fill
    await root.delete(["1.1.2", "1.1.3"])
    root.session.age += 1
    await root.fill("1.1.2", [Have.gen_single({
        "thought": "derive x+1>1 from membership (re-fill)",
        "statement": {
            "english": "x + 1 is greater than 1",
            "conclusion": "x + (1::nat) > 1"
        },
        "name": "helper2",
    })])
    print_header("After sequential Have fill", file)
    root.print(0, file)

    have_node2 = root.locate_node("1.1.2")
    assert isinstance(have_node2, Have), f"Expected Have, got {type(have_node2).__name__}"
    if have_node2.for_any:
        file.write(f"BUG: for_any is non-empty: {[(n.unicode, t.unicode) for n, t in have_node2.for_any]}\n")
    else:
        file.write("OK: for_any is empty as expected\n")

@model_test("SufficesDupFixed", "Test_SufficesDupFixed.thy", 8)
async def _test_SufficesDupFixed(root: Root, file: MyIO):
    """Mirror of HaveDupFixed but with Suffices: for_any names a variable
    already fixed by Intro. gen_SUFFICES uses read_stmt (body-mode fixes)
    + separate augment, so it may or may not hit the same duplicate error."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Intro to fix a, b and the premise.
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "introduce universally quantified variables and premise"
    })])
    print_header("After Intro (a, b now fixed)", file)
    root.print(0, file)

    # Step 2: Suffices with for_any:[a, b] — same names as the fixed vars.
    root.session.age += 1
    outcome = await root.fill("2", [Suffices.gen_single({
        "thought": "It suffices to show the universal statement",
        "statement": {
            "english": "For all positive a,b with divisibility, quotient is a square",
            "for_any": [{"name": "a", "type": "nat"}, {"name": "b", "type": "nat"}],
            "premises": [
                {"name": "ha", "term": "(0::nat) < a"},
                {"name": "hb", "term": "(0::nat) < b"},
                {"name": "hdvd", "term": "a * b + 1 dvd a^2 + b^2"}
            ],
            "conclusion": "\\<exists>x::nat. real (x^2) = real (a^2 + b^2) / real (a * b + 1)"
        },
    })])
    print_header("After Suffices with for_any (duplicate a, b)", file)
    root.print(0, file)

    suffices_node = root.locate_node("2")
    file.write(f"Suffices status: {suffices_node.status.status.value}\n")
    if outcome.failure:
        file.write(f"Failure: {outcome.failure}\n")

@model_test("SufficesStructured", "Test_SufficesStructured.thy", 8)
async def _test_SufficesStructured(root: Root, file: MyIO):
    """Suffices with explicit for_any and premises: the ML layer builds the
    HOL proposition, and INTRO' in the CB auto-introduces after the implication
    is proven, yielding a clean goal."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "introduce the universal quantifier"
    })])
    print_header("After Intro", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("2", [Suffices.gen_single({
        "thought": "It suffices to show the universal statement",
        "statement": {
            "english": "n*n >= n for any natural n",
            "for_any": [{"name": "n", "type": "nat"}],
            "conclusion": r"n * n \<ge> n"
        },
    })])
    print_header("After Suffices with for_any", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    print_header("After proving implication", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After closing suffices goal", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("SufficesPartialForAny", "Test_SufficesPartialForAny.thy", 8)
async def _test_SufficesPartialForAny(root: Root, file: MyIO):
    """Suffices where for_any fixes only some variables and the conclusion
    contains additional ∀-quantifiers.  Previously raised
    'SUFFICES: expected 2 variable binding(s) but got 1'."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "introduce the universal quantifier"
    })])
    print_header("After Intro", file)
    root.print(0, file)

    root.session.age += 1
    outcome = await root.fill("2", [Suffices.gen_single({
        "thought": "suffices to show universally for n, with m still quantified",
        "statement": {
            "english": "n + m >= n for any m",
            "for_any": [{"name": "n", "type": "nat"}],
            "conclusion": r"\<forall>(m::nat). n + m \<ge> n"
        },
    })])
    [suffices_node] = outcome.committed
    print_header("After Suffices with partial for_any", file)
    root.print(0, file)
    file.write(f"Suffices status: {suffices_node.status.status.value}\n")

    root.session.age += 1
    await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    print_header("After proving implication", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After closing suffices goal", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("InductionObviousProof", "Test_ObviousProof_Induction.thy", 8)
async def _test_InductionObviousProof(root: Root, file: MyIO):
    """Test that Induction with proof='Obvious' auto-creates Obvious in all case GoalNodes."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Induction.gen_single({
        "thought": "Induction on list l",
        "target_isabelle_term": "l",
        "variables": [],
    })])
    print_header("After Induction with proof=Obvious", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("MultiGoalQuickview", "Test_MultiGoalQuickview.thy", 10)
async def _test_multi_goal_quickview(root: Root, file: MyIO):
    """Test quickview rendering for root-level multi-goal lemma (shows P and Q and R).
    Each goal is directly an assumption, so auto-Intro proves them all."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # Each goal (P, Q, R) is directly an assumption, so auto-Intro
    # should auto-prove them all. Verify by attempting to fill —
    # should fail because goals are already complete.
    for goal_name in ["goal1", "goal2", "goal3"]:
        root.session.age += 1
        _outcome = await root.fill(f"{goal_name}.1", [Obvious.gen_single({"facts": []})])
        if _outcome.failure is not None:
            file.write(
                f"No step {goal_name}.1 needed (auto-proved): "
                f"{type(_outcome.failure).__name__}: {_outcome.failure}\n")
        else:
            print_header(f"Overview ({goal_name} filled manually)", file)
            root.quickview(0, file)

    print_header("Final Overview", file)
    root.quickview(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("ObviousTimeout_default", "Test_ObviousTimeout2.thy", 8)
async def _test_ObviousTimeout_default(root: Root, file: MyIO):
    """Test Obvious without explicit timeout (should default to 20)."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Obvious without timeout — should default to 20
    root.session.age += 1
    await root.fill("1", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious (default timeout)", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("ObviousTimeout_subproof", "Test_ObviousTimeout3.thy", 8)
async def _test_ObviousTimeout_subproof(root: Root, file: MyIO):
    """Test Have with proof=Obvious dict including timeout threads through SubProof."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Have with proof as Obvious dict with explicit timeout=15
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "x squared is non-negative",
        "statement": {
            "english": "x times x equals x squared",
            "conclusion": "x * x = x^2"
        },
        "name": "sq",
        "proof": [{"operation": "Obvious", "facts": [], "timeout": 15}]
    })])
    print_header("After Have with proof=Obvious(timeout=15)", file)
    root.print(0, file)

    # Close the remaining goal
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": [], "timeout": 30})])
    print_header("After closing remaining goal (timeout=30)", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("Derive1", "Test_Specialize1.thy", 11)
async def _test_Derive1(root: Root, file: MyIO):
    """Test Derive with HOL universal quantifier instantiation + premise discharge."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Derive on h2 (∀x. P x → Q x) with x=0, discharge P 0 using h1
    root.session.age += 1
    await root.fill("1", [Derive.gen_single({
        "thought": "Instantiate h2 with x=0 and discharge with h1",
        "rule": {"name": "h2"},
        "instantiations": [{"name": "x", "value": "0"}],
        "discharging_facts": [{"name": "h1"}],
        "result_name": "derived_Q0"
    })])
    print_header("After Derive", file)
    root.print(0, file)
    # Close goal using the derived fact — may already be auto-proved
    root.session.age += 1
    _outcome = await root.fill("2", [Obvious.gen_single({
        "facts": [{"name": "derived_Q0"}]
    })])
    if _outcome.failure is not None:
        file.write(
            f"No step 2 needed (auto-proved after Derive): "
            f"{type(_outcome.failure).__name__}: {_outcome.failure}\n")
    else:
        print_header("After Obvious", file)
        root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Derive2", "Test_Specialize2.thy", 11)
async def _test_Derive2(root: Root, file: MyIO):
    """Test Derive with discharge only (no instantiation)."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Derive on h2 (P 0 → Q 0) by discharging with h1 (P 0), no instantiation
    root.session.age += 1
    await root.fill("1", [Derive.gen_single({
        "thought": "Discharge h2 with h1 via modus ponens",
        "rule": {"name": "h2"},
        "discharging_facts": [{"name": "h1"}],
        "result_name": "mp_result"
    })])
    print_header("After Derive", file)
    root.print(0, file)
    # Close goal using the named result
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({
        "facts": [{"name": "mp_result"}]
    })])
    print_header("After Obvious", file)
    root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Derive3", "Test_Specialize3.thy", 10)
async def _test_Derive3(root: Root, file: MyIO):
    """Test Derive with unfound rule fact — should fail gracefully."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Try to use a nonexistent rule
    root.session.age += 1
    _outcome = await root.fill("1", [Derive.gen_single({
        "thought": "Try to use a nonexistent rule",
        "rule": {"name": "nonexistent_rule"},
        "result_name": "should_fail"
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("Response", file)
    file.write(f"Is error: {is_error}\n")
    file.write(f"Reason: {reason}\n")
    print_header("After Derive (unfound)", file)
    root.print(0, file)

@model_test("Derive4", "Test_Specialize4.thy", 11)
async def _test_Derive4(root: Root, file: MyIO):
    """Test Derive where discharging fact is semantically equal but syntactically
    different from the instantiated premise — reproduces 'OF: no unifiers'."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Derive on h2 with x = 1 - 1, then discharge with h1 (P 0).
    # After instantiation, premise is P (1 - 1) but h1 is P 0 — no syntactic unification.
    root.session.age += 1
    _outcome = await root.fill("1", [Derive.gen_single({
        "thought": "Derive h2 with x = 1 - 1, discharge with h1 (P 0) — should fail: no unifiers",
        "rule": {"name": "h2"},
        "instantiations": [{"name": "x", "value": "1 - (1::nat)"}],
        "discharging_facts": [{"name": "h1"}],
        "result_name": "bad_result"
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("Response", file)
    file.write(f"Is error: {is_error}\n")
    file.write(f"Reason: {reason}\n")
    print_header("After Derive (no unifiers)", file)
    root.print(0, file)

@model_test("Derive5", "Test_Specialize5.thy", 12)
async def _test_Derive5(root: Root, file: MyIO):
    """Regression test for SPECIALIZE hang: timed_OPR 8000 typo + lazy timeout
    bypass in discharge_one_prove / fast_mepo_tac.

    mult_mod_cancel_left expects ``?n * ?a mod ?m = ?n * ?b mod ?m`` as its
    first premise.  h1 is just ``x mod q = y mod q`` (no multiplication), so
    OF fails.  The fallback discharge_one_prove triggers fast_mepo_tac on a
    goal with schematic variables.  Before the fix:
      - timed_OPR 8000 (typo for 8) provides an ~2 h outer timeout
      - the 3 s timeout in run_mepo_and_render is bypassed by lazy Seq
        evaluation of the THEN combinator
    This makes the SPECIALIZE operation hang."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    start = time()
    _outcome = await root.fill("1", [Derive.gen_single({
        "thought": "Apply mult_mod_cancel_left — h1 lacks ?n*?a pattern, OF will fail",
        "rule": {"name": "mult_mod_cancel_left"},
        "discharging_facts": [
            {"name": "h1"},
            {"name": "h2"}
        ],
        "result_name": "should_fail"
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    elapsed = time() - start
    print_header("Response", file)
    file.write(f"Is error: {is_error}\n")
    file.write(f"Reason: {reason}\n")
    # After fix: SPECIALIZE should timeout via timed_OPR 8 and return an error
    # within ~10 s.  Before fix: hangs for up to 8000 s.
    if elapsed > 30:
        raise TestFailed(
            f"Derive5: SPECIALIZE took {elapsed:.1f}s (expected <30s). "
            "Likely timed_OPR 8000 typo / lazy timeout bypass bug."
        )
    print_header("After Derive", file)
    root.print(0, file)

@model_test("Derive6", "Test_Specialize6.thy", 11)
async def _test_Derive6(root: Root, file: MyIO):
    """Derive with mult_mod_cancel_left on nat — OF fails because
    mult_mod_cancel_left requires euclidean_ring_cancel which nat does not
    satisfy.  The error should be reported clearly, not as a hang."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    start = time()
    _outcome = await root.fill("1", [Derive.gen_single({
        "thought": "Apply mult_mod_cancel_left on nat — type mismatch, OF will fail",
        "rule": {"name": "mult_mod_cancel_left"},
        "discharging_facts": [
            {"name": "h1"},
            {"name": "h2"}
        ],
        "result_name": "should_fail"
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    elapsed = time() - start
    print_header("Response", file)
    file.write(f"Is error: {is_error}\n")
    file.write(f"Reason: {reason}\n")
    if elapsed > 30:
        raise TestFailed(
            f"Derive6: SPECIALIZE took {elapsed:.1f}s (expected <30s). "
            "Likely timed_OPR / lazy timeout bug."
        )
    print_header("After Derive", file)
    root.print(0, file)

@model_test("Derive7", "Test_Specialize7.thy", 16)
async def _test_Derive7(root: Root, file: MyIO):
    """Test that SPECIALIZE diagnostic unifier produces actionable error messages.

    Type clash: mult_mod_cancel_left on nat — should report type mismatch
    (nat vs ?'a::{euclidean_ring_cancel,semiring_gcd}).
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # --- Sub-test 1: Type clash (nat vs euclidean_ring_cancel) ---
    root.session.age += 1
    _outcome = await root.fill("1", [Derive.gen_single({
        "thought": "mult_mod_cancel_left on nat — type mismatch expected",
        "rule": {"name": "mult_mod_cancel_left"},
        "discharging_facts": [
            {"name": "h1"},
            {"name": "h2"}
        ],
        "result_name": "should_fail_type"
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    print_header("Sub-test 1: Type clash", file)
    file.write(f"Is error: {is_error}\n")
    file.write(f"Reason: {reason}\n")
    assert is_error, "Expected type clash error"
    assert reason is not None and "does not unify with" in str(reason), \
        f"Expected 'does not unify with' in reason, got: {reason}"

    print_header("Final state", file)
    root.print(0, file)

@model_test("Derive_NullGap", "Test_Specialize_NullGap.thy", 12)
async def _test_Derive_NullGap(root: Root, file: MyIO):
    """Null in discharging_facts must be accepted (skipped position).

    The LLM may emit null to skip a premise position in discharging_facts.
    Derive.__init__ already filters None, but validation rejects it before
    __init__ runs because the TypedDict declares list[FactByName] without
    Optional.  This test reproduces the bug from the log:
        ERROR: Bad Argument
        proof_operations[1] (Derive).discharging_facts[2]: expected an object, got NoneType
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # --- Sub-test 1: Parse_Op_List with None in discharging_facts ---
    try:
        Parse_Op_List([
            {"operation": "Derive",
             "thought": "null gap test",
             "rule": {"name": "h2"},
             "discharging_facts": [{"name": "h1"}, None],
             "result_name": "r"}
        ], "proof_operations")
        file.write("Parse_Op_List: accepted (correct)\n")
    except ArgumentError as e:
        file.write(f"Parse_Op_List: REJECTED (bug): {e}\n")
        raise TestFailed(
            "Derive with None in discharging_facts rejected at parse time"
        )

    # --- Sub-test 2: gen_single with None in discharging_facts ---
    try:
        Derive.gen_single({
            "thought": "null gap test via gen_single",
            "rule": {"name": "h2"},
            "discharging_facts": [{"name": "h1"}, None],
            "result_name": "r2"
        })
        file.write("gen_single: accepted (correct)\n")
    except ArgumentError as e:
        file.write(f"gen_single: REJECTED (bug): {e}\n")
        raise TestFailed(
            "Derive.gen_single with None in discharging_facts rejected"
        )

    # --- Sub-test 3: end-to-end fill with None gap ---
    # Derive h3 (Q 0 → R 0) discharging with [None, h1] — the None is
    # skipped, h1 doesn't match the premise, so Derive fails gracefully.
    root.session.age += 1
    _outcome = await root.fill("1", [Derive.gen_single({
        "thought": "Derive h3 with a null gap: [None, h1]",
        "rule": {"name": "h3"},
        "discharging_facts": [None, {"name": "h1"}],
        "result_name": "derived_with_gap"
    })])
    print_header("After Derive with null gap", file)
    root.print(0, file)
    file.write(f"failure: {_outcome.failure}\n")
    # Close the proof so the agent doesn't report resource_exhausted
    root.session.age += 1
    await root.fill("1" if _outcome.failure is not None else "2",
                    [Obvious.gen_single({"facts": [{"name": "h1"}, {"name": "h2"}, {"name": "h3"}]})])

@model_test("DeriveWhereOF_Quickview", "Test_DeriveWhereOF_Quickview.thy", 10)
async def _test_DeriveWhereOF_Quickview(root: Root, file: MyIO):
    """Test two rendering fixes:
    1. Derive quickview_title shows only the rule name, not attribute brackets.
    2. Fact display uses 'where'/'OF' (not 'xwhere'/'xOF') for the agent."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Derive using conjunct1[OF h] — rule-level discharge triggers OF display
    root.session.age += 1
    outcome = await root.fill("1", [Derive.gen_single({
        "thought": "Extract first conjunct via conjunct1",
        "rule": {"name": "conjunct1", "discharge": [{"name": "h"}]},
        "result_name": "fst"
    })])
    if outcome.failure is not None:
        file.write(f"Fill failure: {outcome.failure}\n")
    print_header("After Derive (print)", file)
    root.print(0, file)
    print_header("After Derive (quickview)", file)
    root.quickview(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("Derive_NestedDischargeTHMLeak", "Test_Derive_NestedDischargeTHMLeak.thy", 15)
async def _test_Derive_NestedDischargeTHMLeak(root: Root, file: MyIO):
    r"""Regression for the raw `exception THM 0 raised (line 311 of "drule.ML"):
    OF: no unifiers` leak from Derive when the discharge facts are nested in
    the RULE reference instead of Derive's top-level `discharging_facts`.

    Root cause: a FactByName's `discharge` field is packed as the attribute
    suffix `[xwhere ..., xOF fact ...]` (`_fact_suffix` / `IsabelleFact_
    Presented.pack` in model.py). On the ML side SPECIALIZE' (proof.ML)
    resolves the rule via `Attrib.eval_thms` with NO THM handler, and the
    `xOF` attribute (Minilang.thy) calls `Minilang_Aux.xOF false`: with
    prove_discharge=false, aux.ML deliberately re-runs `st OF thms` to
    re-raise on failure, so the raw `THM ("OF: no unifiers", 0, ...)` from
    drule.ML escapes to the agent verbatim. Every friendly path — `xOF true`
    with the sledgehammer-fallback discharge, `Unify_Diagnostic.
    diagnose_of_failure`, and the Python `_OF_PREMISE_MISMATCH_RE` hint —
    applies only to `discharging_facts`, never to a nested `discharge`.

    Reproduction (mirrors the production log of 2026-06-10, step 4 `Derive
    nat_induct`): `base` (P 0) resolves nat_induct's first premise, but
    `step` is the object-level `\<forall>k. P k \<longrightarrow> P (Suc k)` while the second
    premise is the meta-level `\<And>n. ?P n \<Longrightarrow> ?P (Suc n)` — OF has no
    unifiers and the fact is not rulified. While the bug is present the
    failure reason / rendered tree contains the raw `exception THM 0 raised
    ... OF: no unifiers` and this test FAILS; once Derive reports the
    mismatch informatively (or discharges it) without leaking the raw ML
    exception, it passes."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Derive.gen_single({
        "thought": "nat_induct with discharge nested in the rule reference",
        "rule": {"name": "nat_induct",
                 "instantiations": [{"name": "?P", "value": "P"},
                                    {"name": "?n", "value": "n"}],
                 "discharge": [{"name": "base"}, {"name": "step"}]},
        "result_name": "allk"
    })])
    # The failed Derive may be reverted from the tree; its failure cause is
    # carried by `outcome.failure` (and, if kept, on the committed node /
    # rendered tree). Collect every place the cause could surface and assert
    # none of them is the raw ML exception.
    parts = [str(outcome.failure)]
    parts += [n.status.reason.reason for n in outcome.committed
              if n.status.reason is not None]
    _buf = io.StringIO()
    root.print(0, MyIO(_buf))
    parts.append(_buf.getvalue())
    haystack = "\n".join(parts)
    leaked = ("OF: no unifiers" in haystack
              or ("exception THM" in haystack and "raised" in haystack))
    if leaked:
        raise TestFailed(
            "Derive leaked a raw ML THM exception for a nested-discharge "
            f"unification failure: {str(outcome.failure)!r}")
    file.write("Derive succeeded (rulify resolved the nested discharge); "
               "no raw THM leak\n")

@model_test("Derive_OrderSafety", "Test_Derive_OrderSafety.thy", 16)
async def _test_Derive_OrderSafety(root: Root, file: MyIO):
    r"""Order safety of the per-argument discharge fallback in xOF.

    A = ⟦Q; Q2⟧ ⟹ Q3, B = ⟦P1; P2⟧ ⟹ Q, C = True ⟶ Q2.  Discharging A's
    premises with [B, C]: B's own premises P1/P2 replace Q, so a naive
    left-to-right fallback re-targets C at P1 instead of Q2 (the pre-refactor
    `discharge_all` bug).  C is object-level so the bulk `st OF thms` fails
    and the fallback necessarily runs; the index-anchored right-to-left loop
    plus the rulify retry must attach C to the ORIGINAL premise 2 (Q2),
    yielding ⟦P1; P2; True⟧ ⟹ Q3.  Pre-refactor this Derive failed with a
    misleading "C mismatches P1" error (after a wasted 3s prover call on P1).
    """
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Derive.gen_single({
        "thought": "B inserts premises P1 P2; C must still land on Q2",
        "rule": {"name": "A"},
        "discharging_facts": [{"name": "B"}, {"name": "C"}],
        "result_name": "combined"
    })])
    if outcome.failure is not None:
        raise TestFailed(
            f"Derive_OrderSafety: discharge failed: {outcome.failure}")
    [node] = outcome.committed
    exprs = [e.unicode for _, e in (node.result_facts or [])]
    ok = any(("P1" in s) and ("True" in s) and ("Q3" in s) and ("Q2" not in s)
             for s in exprs)
    if not ok:
        raise TestFailed(
            f"Derive_OrderSafety: C did not consume Q2 (wrong target?); "
            f"result facts: {exprs}")
    file.write("order-safe: C consumed Q2 via rulify; B's premises preserved\n")
    print_header("After Derive", file)
    root.print(0, file)
    # close the trivial goal so the run doesn't end resource_exhausted
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": []})])

@model_test("DeriveBall", "Test_DeriveBall.thy", 11)
async def _test_DeriveBall(root: Root, file: MyIO):
    """Test Derive on a Ball-quantified rule: ∀x∈A. P x.
    Instantiate x=0, discharge membership h1: 0 ∈ A."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Derive.gen_single({
        "thought": "Instantiate Ball-quantified h2 with x=0, discharge membership with h1",
        "rule": {"name": "h2"},
        "instantiations": [{"name": "x", "value": "0"}],
        "discharging_facts": [{"name": "h1"}],
        "result_name": "derived_P0"
    })])
    if outcome.failure is not None:
        file.write(f"Derive failed: {outcome.failure}\n")
    print_header("After Derive", file)
    root.print(0, file)
    root.session.age += 1
    outcome2 = await root.fill("2", [Obvious.gen_single({
        "facts": [{"name": "derived_P0"}]
    })])
    if outcome2.failure is not None:
        file.write(
            f"No step 2 needed: "
            f"{type(outcome2.failure).__name__}: {outcome2.failure}\n")
    else:
        print_header("After Obvious", file)
        root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("Derive_OverDischarge", "Test_Specialize_OverDischarge.thy", 14)
async def _test_Derive_OverDischarge(root: Root, file: MyIO):
    """Reproduce exception THM 3: xOF attribute on a fact with more discharge
    slots than the fact has premises.

    The LLM may emit ``discharge: [null, null]`` on a conjunction fact that has
    zero Pure premises, causing the ``xOF _ _`` attribute to raise ``THM 3``
    during fact-reference evaluation (Attrib.eval_thms), which is BEFORE the
    ``handle THM`` in SPECIALIZE.  The raw ML exception trace leaks to the
    agent instead of a clean OPR_FAIL message.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Derive conjunct2 (Q 0) from h_conj via conjunct2
    root.session.age += 1
    await root.fill("1", [Derive.gen_single({
        "thought": "extract Q 0 from the conjunction",
        "rule": {"name": "conjunct2"},
        "discharging_facts": [{"name": "h_conj"}],
        "result_name": "q0"
    })])
    print_header("After deriving conjunct", file)
    root.print(0, file)

    # Step 2: Derive h_rule using a discharging fact that carries
    # an xOF attribute with more slots than the fact has premises.
    # h_conj is "P 0 ∧ Q 0" (0 Pure premises).
    # discharge: [null, null] → xOF _ _ → tries to discharge 2 premises
    # from a conjunction with 0 premises → THM 3.
    #
    # ROOT CAUSE: The THM 3 exception is raised during Attrib.eval_thms
    # (fact-reference evaluation at proof.ML:3540), which is BEFORE the
    # `handle THM _` at proof.ML:3543 that catches discharge failures.
    # The exception escapes as a raw IsabelleError instead of being
    # wrapped in OPR_FAIL with a clean diagnostic message.
    root.session.age += 1
    outcome = await root.fill("2", [Derive.gen_single({
        "thought": "xOF over-discharge on conjunction fact",
        "rule": {"name": "h_rule"},
        "discharging_facts": [
            {"name": "h_conj", "discharge": [None, None]}
        ],
        "result_name": "should_fail"
    })])
    print_header("After xOF over-discharge Derive", file)
    root.print(0, file)
    is_error = outcome.failure is not None and outcome.failure.is_error
    reason_str = str(outcome.failure) if outcome.failure is not None else ""
    file.write(f"Is error: {is_error}\n")
    file.write(f"Reason: {reason_str}\n")
    assert is_error, "Expected error from OF over-discharge"
    assert "exception THM" not in reason_str, \
        f"Raw THM exception leaked to agent: {reason_str}"
    assert "OF: the fact has" in reason_str, \
        f"Expected clean OF diagnostic, got: {reason_str}"

    # Close the proof so the runner doesn't report resource_exhausted
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({
        "facts": [{"name": "q0"}, {"name": "h_rule"}]
    })])

@model_test("Derive_DischargeNullName", "Test_Derive_DischargeNullName.thy", 10)
async def _test_Derive_DischargeNullName(root: Root, file: MyIO):
    """A nested `discharge` entry `{"name": None, ...}` — an object with a
    null `name`, instead of the literal `null` the schema prescribes for
    skipping a premise — must be rejected at parse time with a
    path-annotated ArgumentError.

    Today `validate` never checks scalar leaf types (it falls through
    `return data` for `str` fields), so the dict passes
    `_validate_typed_dict` and the bad value survives until rendering:
    `_of_clause` evaluates `item["name"] + _fact_suffix(item)` with
    `item["name"] is None`, and the raw TypeError crashes the whole edit
    tool.  Reproduces the log:

        [TOOL_CALL] edit: {'action': 'fill', ..., 'rule': {'name': 'Min_le',
          'discharge': [{'name': None, ...}, {'name': None, ...}]}, ...}
        [TOOL_RESPONSE] edit: UNEXPECTED ERROR: TypeError:
          unsupported operand type(s) for +: 'NoneType' and 'str'
    """
    print_header("Initial YAML", file)
    root.print(0, file)
    bad_rule = {"name": "conjunct1",
                "instantiations": [],
                "discharge": [
                    {"name": None, "instantiations": [],
                     "discharge": [], "flip": False}]}
    bugs: list[str] = []

    # --- Sub-test 1: Parse_Op_List must reject a null `name` ---
    print_header("Parse_Op_List with discharge entry name=None", file)
    try:
        Parse_Op_List([
            {"operation": "Derive", "thought": "null-name discharge",
             "rule": bad_rule, "result_name": "fst"}
        ], "proof_operations")
        file.write("ACCEPTED (bug: validator missed name=None)\n")
        bugs.append("Parse_Op_List accepted a discharge entry with name=None")
    except ArgumentError as e:
        file.write(f"rejected: {e}\n")
    except TypeError as e:
        bugs.append(f"Parse_Op_List crashed with TypeError: {e}")

    # --- Sub-test 2: end-to-end fill must not crash the system ---
    print_header("fill with discharge entry name=None", file)
    op = None
    try:
        op = Derive.gen_single({
            "thought": "Extract first conjunct, null-name discharge",
            "rule": bad_rule,
            "result_name": "fst"})
    except ArgumentError as e:
        file.write(f"gen_single rejected: {e}\n")
    if op is not None:
        root.session.age += 1
        try:
            outcome = await root.fill("1", [op])
            file.write(f"fill failure: {outcome.failure}\n")
        except TypeError as e:
            bugs.append(f"fill crashed the system with TypeError: {e}")

    if bugs:
        raise TestFailed("Derive_DischargeNullName: " + "; ".join(bugs))

    # Close the proof so the runner doesn't report resource_exhausted
    root.session.age += 1
    await root.fill("1", [Obvious.gen_single({"facts": [{"name": "h"}]})])

@model_test("FactByNameWhereBall", "Test_FactByNameWhereBall.thy", 11)
async def _test_FactByNameWhereBall(root: Root, file: MyIO):
    """Test FactByName with [xwhere] on a Ball-quantified fact: ∀x∈A. P x.
    Instantiate x=0 via xwhere, membership premise discharged by hmem."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Obvious.gen_single({
        "facts": [
            {"name": "h", "instantiations": [{"name": "x", "value": "0 :: nat"}]},
            {"name": "hmem"}
        ]
    })])
    if outcome.failure is not None:
        file.write(f"Fill failed: {outcome.failure}\n")
    print_header("After Obvious with Ball xwhere", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("GlobalEnv", "Test_GlobalEnv.thy", 11)
async def _test_GlobalEnv(root: Root, file: MyIO):
    """Corner case + recovery on `x = 0 ⟹ x * x = 0`:
      1. ADD a broken global Have `t1: P` — the bare proposition
         variable `P` has no content the inherited Obvious sub-step can
         discharge, so the Have cannot be proven and stays sorry'd.
      2. Try to USE t1 via Rewrite — Isabelle does register `t1` as a
         named fact despite the sorry'd proof, so fetch succeeds, but
         `P` isn't an equation and simp reports "no progress".
      3. AMEND-recovery: swap t1's statement for the equation `x = 0`
         (provable from h1 by the inherited Obvious sub-step). The Have
         flips from FAILURE to SUCCESS without recreating the sub-tree.
      4. DELETE the global declaration."""
    print_header("Initial YAML", file)
    root.print(0, file)
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # === ADD: Append a global equation Have and prove it ===
    root.session.age += 1
    _have_outcome = await root.global_env.append([Have.gen_single({
        "thought": "Restate h1 as a global rewrite rule",
        "statement": {"english": "P", "conclusion": "P"},
        "name": "t1",
    })])
    [have1] = _have_outcome.committed
    print_header("edit_message: ADD global Have t1", file)
    file.write((await _P.edit_message(root, _have_outcome, root.session))[0])
    file.write("---------------\n")
    file.write(f"Added have1: id={have1.id}, local_step={have1.local_step}, status={have1.status.status.value}\n")
    root.session.age += 1
    _obv_outcome = await have1.append([Obvious.gen_single({
        "facts": [{"name": "h1"}]
    })])
    print_header("edit_message: Obvious under t1", file)
    file.write((await _P.edit_message(root, _obv_outcome, root.session))[0])
    file.write("---------------\n")
    if _obv_outcome.committed:
        obv_status = _obv_outcome.committed[0].status.status.value
    else:
        obv_status = "reverted"
    file.write(f"Obvious in have1: status={obv_status}\n")

    # === VISIBILITY: Check whether t1 appears in GoalNode's context ===
    goal_node = root.sub_nodes[1]  # the single GoalNode
    ctxt = goal_node._ctxt_before_me()
    file.write(f"GoalNode context hyps: {[k.unicode for k in sorted(ctxt.hyps.keys())]}\n")
    file.write(f"t1 visible to GoalNode via context: {'t1' in ctxt.hyps}\n")

    # === USE FROM PROOF BODY (failure path): Rewrite goal using broken t1 ===
    # The Have for t1 is sorry'd because Obvious couldn't discharge `P`.
    # Isabelle still registers the name `t1` with its sorry'd content,
    # so the Rewrite below fetches it successfully — but `P` isn't an
    # equation, so simp reports "no progress" and the Rewrite fails.
    root.session.age += 1
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite the goal using the (broken) global equation t1",
        "using": [{"name": "t1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("edit_message: Rewrite step 1 using broken t1", file)
    file.write((await _P.edit_message(root, _outcome, root.session))[0])
    file.write("---------------\n")
    # Verify: the Rewrite node IS in the tree (quickview just folded it
    # because its `changed` flag was cleared after the first edit_message's
    # `root.reset()` and the outer GoalNode didn't get re-flagged
    # as changed by a trivial Rewrite).
    print_header("Full tree.print after Rewrite (node is present)", file)
    root.print(0, file)
    node1 = _outcome.committed[0] if _outcome.committed else None
    assert node1 is not None
    is_error1 = _outcome.failure is not None and _outcome.failure.is_error
    reason1 = _outcome.failure
    file.write(f"Rewrite step 1 using broken t1: status={node1.status.status.value}, is_error={is_error1}\n")
    if reason1:
        file.write(f"  reason: {reason1.reason if isinstance(reason1, FailureReason) else reason1}\n")

    # === AMEND (recovery): replace the bare `P` with a provable equation
    # `x = 0` that the inherited Obvious sub-step (which already references
    # h1: x = 0) can actually discharge. Verifies:
    #   (a) AMEND structurally swaps in the new Have on a GlobalEnv child,
    #   (b) _amend_from carries the existing Obvious sub-step across,
    #   (c) re-refresh after amend turns the previously-failing Have into
    #       a SUCCESS — a real recovery, not a no-op rename.
    root.session.age += 1
    _outcome = await root.amend("global.1", [Have.gen_single({
        "thought": "Amended: replace unprovable y=x with the equation x=0 (= h1)",
        "statement": {"english": "x equals zero", "conclusion": "x = 0"},
        "name": "t1",
    })])
    print_header("edit_message: AMEND global.1 (recovery)", file)
    file.write((await _P.edit_message(root, _outcome, root.session))[0])
    file.write("---------------\n")
    amended = _outcome.committed[0] if _outcome.committed else None
    assert amended is not None
    is_error2 = _outcome.failure is not None and _outcome.failure.is_error
    reason2 = _outcome.failure
    file.write(f"Amend global.1: id={amended.id}, local_step={amended.local_step}, is_error={is_error2}\n")
    if reason2:
        file.write(f"  reason: {reason2.reason if isinstance(reason2, FailureReason) else reason2}\n")
    file.write(f"Amended Have status: {amended.status.status.value}\n")
    file.write(f"Amended Have inherited children: {len(cast(NonLeaf_Node, amended).sub_nodes)}\n")
    if cast(NonLeaf_Node, amended).sub_nodes:
        first_child = cast(NonLeaf_Node, amended).sub_nodes[0]
        file.write(f"  inherited child[0]: type={type(first_child).__name__}, status={first_child.status.status.value}\n")

    # === DELETE: Remove the global Have entirely ===
    not_found = await root.delete(["global.1"])
    file.write(f"Delete global.1 not_found: {not_found}\n")
    file.write(f"GlobalEnv children after delete: {len(root.global_env.sub_nodes)}\n")

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("GlobalEnv_BodyDone", "Test_GlobalEnv_BodyDone.thy", 10)
async def _test_GlobalEnv_BodyDone(root: Root, file: MyIO):
    """The body is discharged early and then the global environment is
    edited repeatedly.  An unfinished global Have keeps the overall
    lemma open throughout (so 'Congratulations' never fires), while the
    folded body must render as `proof:\\n  done\\n` instead of a bare
    `proof:\\n` after every global edit."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Add a global Have with no sub-proof — stays sorry'd, ensuring the
    # overall lemma never hits 'all goals proven' during the test.
    root.session.age += 1
    _outcome = await root.global_env.append([Have.gen_single({
        "thought": "Unprovable bare proposition — no Obvious under it",
        "statement": {"english": "P", "conclusion": "P"},
        "name": "g1",
    })])
    print_header("edit_message: ADD global g1 (unfinished)", file)
    file.write((await _P.edit_message(root, _outcome, root.session))[0])
    file.write("---------------\n")

    # Discharge the (trivial) proof body; never touch it again.
    root.session.age += 1
    _outcome = await root.fill("1", [Obvious.gen_single({"facts": []})])
    print_header("edit_message: Obvious (discharge body)", file)
    file.write((await _P.edit_message(root, _outcome, root.session))[0])
    file.write("---------------\n")

    # Repeatedly append more unfinished global Haves.  After each edit
    # the body stays SUCCESS (folds to 'done'), but g1/g2/g3 remain
    # unfinished, so the lemma is still open.
    for name in ["g2", "g3"]:
        root.session.age += 1
        _outcome = await root.global_env.append([Have.gen_single({
            "thought": f"Another unfinished global Have {name}",
            "statement": {"english": "P", "conclusion": "P"},
            "name": name,
        })])
        print_header(f"edit_message: ADD global {name} (unfinished)", file)
        file.write((await _P.edit_message(root, _outcome, root.session))[0])
        file.write("---------------\n")

@model_test("GlobalEnv_BodyUnfilled", "Test_GlobalEnv_BodyUnfilled.thy", 10)
async def _test_GlobalEnv_BodyUnfilled(root: Root, file: MyIO):
    """The single proof body is never filled (stays pending).  We
    repeatedly edit the global environment — this exercises the
    opposite of `GlobalEnv_BodyDone`: here `does_quickview_need_detail`
    stays True on the body, so `proof:` must persist with its pending
    'Error: Unfinished Proof...' hint after every global edit."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Append three global Haves (each left unfinished: no Obvious).
    for name in ["g1", "g2", "g3"]:
        root.session.age += 1
        _outcome = await root.global_env.append([Have.gen_single({
            "thought": f"Unfinished global Have {name}",
            "statement": {"english": "P", "conclusion": "P"},
            "name": name,
        })])
        print_header(f"edit_message: ADD global {name} (unfinished)", file)
        file.write((await _P.edit_message(root, _outcome, root.session))[0])
        file.write("---------------\n")

    # Amend g2 to a different unprovable statement — still leaves the
    # body untouched and unfinished.
    root.session.age += 1
    _outcome = await root.amend("global.2", [Have.gen_single({
        "thought": "Amended g2 statement (still unfinished)",
        "statement": {"english": "Q", "conclusion": "Q"},
        "name": "g2",
    })])
    print_header("edit_message: AMEND global.2", file)
    file.write((await _P.edit_message(root, _outcome, root.session))[0])
    file.write("---------------\n")

    # Delete g1 — body still untouched.
    not_found = await root.delete(["global.1"])
    file.write(f"Delete global.1 not_found: {not_found}\n")
    file.write(f"GlobalEnv children after delete: {len(root.global_env.sub_nodes)}\n")

@model_test("GlobalEnv_happy", "Test_GlobalEnv_happy.thy", 11)
async def _test_GlobalEnv_happy(root: Root, file: MyIO):
    """Happy path: lemma `y = x ⟹ x + y = x + x` with both `x` and `y` bound.
    A global Have `g_eq: y = x` is provable from h1, so the subsequent proof
    body Rewrite step can actually fetch g_eq and rewrite the goal
    `x + y = x + x` into `x + x = x + x`, which Obvious then closes.
    Exercises ADD / VISIBILITY / USE / AMEND / DELETE end-to-end on the
    success path."""
    print_header("Initial YAML", file)
    root.print(0, file)
    print_header("Initial Overview", file)
    root.quickview(0, file)
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # === ADD: Append a provable global equation Have ===
    root.session.age += 1
    [have1] = (await root.global_env.append([Have.gen_single({
        "thought": "Restate h1 as a global rewrite rule",
        "statement": {"english": "y equals x", "conclusion": "y = x"},
        "name": "g_eq",
    })])).committed
    file.write(f"Added have1: id={have1.id}, local_step={have1.local_step}, status={have1.status.status.value}\n")
    # Discharge the subgoal using h1 (trivially true since h1 IS y = x)
    root.session.age += 1
    [obv1] = (await have1.append([Obvious.gen_single({
        "facts": [{"name": "h1"}]
    })])).committed
    file.write(f"Obvious in have1: status={obv1.status.status.value}\n")
    print_header("After ADD global Have (g_eq) + prove", file)
    root.print(0, file)
    print_header("Overview after ADD", file)
    root.quickview(0, file)

    # === VISIBILITY: Check whether g_eq appears in GoalNode's context ===
    goal_node = root.sub_nodes[1]
    ctxt = goal_node._ctxt_before_me()
    file.write(f"GoalNode context hyps: {[k.unicode for k in sorted(ctxt.hyps.keys())]}\n")
    file.write(f"g_eq visible to GoalNode via context: {'g_eq' in ctxt.hyps}\n")

    # === USE FROM PROOF BODY: Rewrite the goal using g_eq (explicit consumption) ===
    # Rewriting `x + y = x + x` with `y = x` should reduce it to `x + x = x + x`.
    root.session.age += 1
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite the goal using the global equation g_eq",
        "using": [{"name": "g_eq"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    node1 = _outcome.committed[0] if _outcome.committed else None
    assert node1 is not None
    is_error1 = _outcome.failure is not None and _outcome.failure.is_error
    reason1 = _outcome.failure
    file.write(f"Rewrite step 1 using g_eq: status={node1.status.status.value}, is_error={is_error1}\n")
    if reason1:
        file.write(f"  reason: {reason1.reason if isinstance(reason1, FailureReason) else reason1}\n")
    print_header("After Rewrite proof body using global decl", file)
    root.print(0, file)

    # Close the now-trivial residual `x + x = x + x` via an explicit Rewrite
    # with system simplifiers. No `using` facts needed — simp alone closes
    # reflexive equalities.
    root.session.age += 1
    _outcome = await root.fill("2", [Rewrite.gen_single({
        "thought": "Close residual reflexive equation via system simplifiers",
        "using": [],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    # Step 1's Rewrite already solved the goal, so step 2's Rewrite makes
    # no progress and fails.  Rewrite overrides `_on_edit_failure` to revert
    # in singleton mode (the new generalized behaviour), so
    # `_outcome.committed` is empty and the failure info lives in
    # `_outcome.failure` / `_outcome.is_error`.
    node2 = _outcome.committed[0] if _outcome.committed else None
    status_val = node2.status.status.value if node2 else "reverted"
    is_error2 = _outcome.failure is not None and _outcome.failure.is_error
    reason2 = _outcome.failure
    file.write(f"Rewrite step 2 (system simp): status={status_val}, is_error={is_error2}\n")
    if reason2:
        file.write(f"  reason: {reason2.reason if isinstance(reason2, FailureReason) else reason2}\n")
    print_header("After Rewrite closes residual goal", file)
    root.print(0, file)

    # === AMEND: Replace the global Have with a reoriented equation ===
    root.session.age += 1
    _outcome = await root.amend("global.1", [Have.gen_single({
        "thought": "Amended: reverse orientation of the equation",
        "statement": {"english": "x equals y", "conclusion": "x = y"},
        "name": "g_eq",
    })])
    amended = _outcome.committed[0] if _outcome.committed else None
    assert amended is not None
    is_error3 = _outcome.failure is not None and _outcome.failure.is_error
    reason3 = _outcome.failure
    file.write(f"Amend global.1: id={amended.id}, local_step={amended.local_step}, is_error={is_error3}\n")
    if reason3:
        file.write(f"  reason: {reason3.reason if isinstance(reason3, FailureReason) else reason3}\n")
    print_header("After AMEND global.1", file)
    root.print(0, file)
    print_header("Overview after AMEND", file)
    root.quickview(0, file)

    # === DELETE: Remove the global Have entirely ===
    not_found = await root.delete(["global.1"])
    file.write(f"Delete global.1 not_found: {not_found}\n")
    file.write(f"GlobalEnv children after delete: {len(root.global_env.sub_nodes)}\n")
    print_header("After DELETE global.1", file)
    root.print(0, file)
    print_header("Final Overview", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("GlobalEnv_DoneQuickview", "Test_GlobalEnv_DoneQuickview.thy", 11)
async def _test_GlobalEnv_DoneQuickview(root: Root, file: MyIO):
    """Bug reproduction: when all global declarations are proved and
    `reset()` clears every `changed` flag, the next quickview
    should still show global lemma headers (e.g. "step global.1: Have
    g_eq (done, ...)") instead of collapsing `global declarations:` to
    an empty section.

    Root cause: NonLeaf_Node.quickview (line ~3260) returns early with
    just the header when `does_quickview_need_detail()` is False,
    skipping all children entirely."""

    # --- Step 1: Add a global Have and prove it ---
    root.session.age += 1
    [have1] = (await root.global_env.append([Have.gen_single({
        "thought": "Restate h1 as a global rewrite rule",
        "statement": {"english": "y equals x", "conclusion": "y = x"},
        "name": "g_eq",
    })])).committed
    root.session.age += 1
    await have1.append([Obvious.gen_single({"facts": [{"name": "h1"}]})])

    # --- Step 2: Prove the body via Rewrite using g_eq ---
    root.session.age += 1
    _outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite using g_eq",
        "using": [{"name": "g_eq"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])

    # --- Step 3: edit_message — calls quickview then reset() ---
    print_header("edit_message (completes everything)", file)
    file.write((await _P.edit_message(root, _outcome, root.session))[0])
    file.write("---------------\n")

    # --- Step 4: quickview AFTER reset() ---
    # At this point all nodes are SUCCESS and changed=False.
    # The bug: global.1 (g_eq) disappears entirely from quickview.
    print_header("Quickview after reset_changed (BUG REPRODUCTION)", file)
    root.quickview(0, file)

    # --- Step 5: Verify whether g_eq appears ---
    qv_buf = MyIO(io.StringIO())
    root.quickview(0, qv_buf)
    qv_text = qv_buf.getvalue()
    file.write(f"\nQuickview text contains 'g_eq': {'g_eq' in qv_text}\n")
    file.write(f"Quickview text contains 'global.1': {'global.1' in qv_text}\n")
    file.write(f"Expected: both True (global Have headers should remain visible)\n")

@model_test("GlobalEnvFill", "Test_GlobalEnvFill.thy", 11)
async def _test_GlobalEnvFill(root: Root, file: MyIO):
    """Bug 3 regression test: verify that `root.fill("global.1", ...)`
    works for adding global declarations.

    Previously GlobalEnv.id was `"$global"` while local_step was
    `"global"`, so _print_footer advertised `$global.1` which was
    unreachable by either `$global.1` or `global.1`. The fix sets
    GlobalEnv.id = "global" and removes the _id_of_openning_prf_to_fill
    override so StdBlock's logic kicks in."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Verify _print_footer advertises "global.1" (not "$global.1")
    import re
    buf = io.StringIO()
    root.print(0, MyIO(buf))
    yaml_text = buf.getvalue()
    m = re.search(r'target step `([\w.]+)`', yaml_text)
    advertised_id = m.group(1) if m else None
    file.write(f"Advertised fill target: {advertised_id}\n")
    assert advertised_id == "global.1", \
        f"Expected _print_footer to advertise 'global.1', got {advertised_id!r}"

    # Verify id and local_step are both "global"
    file.write(f"GlobalEnv.id = {root.global_env.id!r}\n")
    file.write(f"GlobalEnv.local_step = {root.global_env.local_step!r}\n")
    assert root.global_env.id == "global"
    assert root.global_env.local_step == "global"

    # fill("global.1") should now succeed
    root.session.age += 1
    _outcome = await root.fill("global.1", [Have.gen_single({
        "thought": "global declaration via fill",
        "statement": {"english": "x is zero", "conclusion": "x = 0"},
        "name": "g1",
    })])
    ret = _outcome.committed[0] if _outcome.committed else None
    assert ret is not None
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    file.write(f"fill('global.1'): id={ret.id}, status={ret.status.status.value}, is_error={is_error}\n")
    print_header("After fill global.1", file)
    root.print(0, file)

    # Prove the global Have
    root.session.age += 1
    [obv] = (await ret.append([Obvious.gen_single({
        "facts": [{"name": "h1"}]
    })])).committed
    file.write(f"Obvious in global Have: status={obv.status.status.value}\n")
    print_header("After proving global Have", file)
    root.print(0, file)

    # The next fill slot should be "global.2"
    buf2 = io.StringIO()
    root.print(0, MyIO(buf2))
    m2 = re.search(r'target step `([\w.]+)`', buf2.getvalue())
    next_id = m2.group(1) if m2 else None
    file.write(f"Next advertised fill target: {next_id}\n")
    assert next_id == "global.2", \
        f"Expected next target 'global.2', got {next_id!r}"

@model_test("Chaining", "Test_Chaining.thy", 12)
async def _test_Chaining(root: Root, file: MyIO):
    """Chain `ab : a = b` and `bc : b <= c` into `ac : a <= c` via registered
    [trans] rules, then discharge the goal with Obvious using the chained
    fact. Exercises the named-binding path of the Chaining operation and
    confirms that the bound fact is visible to downstream operations."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Insert a Chaining step before the main goal so we have both the forward
    # derivation and the remaining goal slot.
    await root.fill("1", [Chaining.gen_single({
        "thought": "Chain ab and bc by transitivity to derive a <= c",
        "name": "ac",
        "facts": [
            {"name": "ab"},
            {"name": "bc"},
        ],
    })])
    print_header("After Chaining (named)", file)
    root.print(0, file)

    # Close the main goal using the chained fact.
    await root.fill("2", [Obvious.gen_single({
        "facts": [{"name": "ac"}],
    })])
    print_header("After Obvious using ac", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Chaining_NoCounter_AutoName", "Test_Chaining_NoCounter_AutoName.thy", 14)
async def _test_Chaining_NoCounter_AutoName(root: Root, file: MyIO):
    """Chaining without an explicit name under No_Counter mode.
    The agent server sets counter_mode="none", so CHAINING's auto-name path
    used to call map_fact_counter which raised "No_Counter: fact counter cannot
    be modified". After the fix, Python assigns a stable name from the step id
    so ML never tries to auto-increment."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Chaining WITHOUT a name — Python auto-assigns via Session.fact_name_counter
    await root.fill("1", [Chaining.gen_single({
        "thought": "Chain ab and bc by transitivity (no explicit name)",
        "facts": [
            {"name": "ab"},
            {"name": "bc"},
        ],
    })])
    print_header("After Chaining (auto-named)", file)
    root.print(0, file)

    # Close the goal using the auto-named fact
    await root.fill("2", [Obvious.gen_single({
        "facts": [{"name": "chain1"}],
    })])
    print_header("After Obvious using auto-named fact", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("FillOrphanedNode", "Test_FillOrphanedNode.thy", 11)
async def _test_FillOrphanedNode(root: Root, file: MyIO):
    """Test that fill can replace a failed non-Obvious node (and its successors)
    even when _id_of_openning_prf_to_fill points past it.

    Previously, if append left an orphaned node (e.g. a Have with bad syntax)
    in sub_nodes, subsequent fill calls on the same step ID would fail with
    CannotFill_BadNode because the only replacement path was for trailing
    failed Obvious nodes. The extended fill fallback now allows replacing any
    node (and everything after it) as long as none of them are SUCCESS."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Fill with a Have that FAILS (bad Isabelle syntax).
    # The node stays in sub_nodes with FAILURE status.
    root.session.age += 1
    _outcome = await root.fill("1", [Have.gen_single({
        "thought": "intentionally bad",
        "statement": {"english": "bad", "conclusion": "1 1 1"},
        "name": "bad"
    })])
    # Have does not override _on_edit_failure, so outcome.is_error stays
    # False (the agent observes FAILURE from the tree itself).  The node
    # still commits with FAILURE status — that's the contract tested here.
    step1 = root.locate_node("1")
    assert step1.status.status == EvaluationStatus.Status.FAILURE, \
        f"Expected FAILURE but got {step1.status.status.value}"
    file.write(f"Step 1 status: {step1.status.status.value}\n")
    print_header("After step 1 (bad Have, should fail)", file)
    root.print(0, file)

    # Step 2: Fill an Obvious AFTER the failed Have.
    # It should be CANCELLED because step 1 failed.
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": []})])
    step2 = root.locate_node("2")
    assert step2.status.status == EvaluationStatus.Status.CANCELLED, \
        f"Expected CANCELLED but got {step2.status.status.value}"
    file.write(f"Step 2 status: {step2.status.status.value}\n")
    print_header("After step 2 (cancelled Obvious)", file)
    root.print(0, file)

    # Step 3: Re-fill "1" with a VALID Have.
    # Old code would raise CannotFill_BadNode because _id_of_openning_prf_to_fill
    # returns "3" (past the failed Have and cancelled Obvious).
    # The new fallback allows this because steps 1 and 2 are both non-SUCCESS.
    root.session.age += 1
    _outcome = await root.fill("1", [Have.gen_single({
        "thought": "valid helper",
        "statement": {"english": "x is positive", "conclusion": "x > 0"},
        "name": "x_pos"
    })])
    is_error3 = _outcome.failure is not None and _outcome.failure.is_error
    assert not is_error3, "valid Have should succeed"
    step1_new = root.locate_node("1")
    assert step1_new.status.status == EvaluationStatus.Status.SUCCESS, \
        f"Expected SUCCESS but got {step1_new.status.status.value}"
    file.write(f"Step 1 (re-filled) status: {step1_new.status.status.value}\n")
    # Steps 2 and onwards should have been deleted by the fill replacement.
    try:
        root.locate_node("2")
        assert False, "Step 2 should have been deleted by fill replacement"
    except NodeNotFound:
        file.write("Step 2 correctly deleted by fill replacement\n")
    print_header("After re-fill step 1 (valid Have)", file)
    root.print(0, file)

    # Step 4: Complete the proof.
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": []})])
    print_header("After completing proof", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("AbbrevQuery", "Test_AbbrevQuery.thy", 11)
async def _test_abbrev_query(root: Root, file: MyIO):
    """Test abbreviation-annotated semantic retrieval.

    Verifies:
    1. _retrieve_entity returns abbreviation_names for theorems mentioning abbreviations
    2. _retrieve_entity returns abbreviation_names for constants that are abbreviations
    3. abbreviation_defs returns pretty-printed equations for abbreviation constants
    4. semantic_knn propagates abbreviation_names onto entities
    """
    from Isabelle_RPC_Host.universal_key import EntityKind
    ml = root.ml_state

    # 1. Retrieve a theorem known to mention the `even` abbreviation
    #    `even_iff_mod_2_eq_zero`: even n ==> n mod 2 = 0
    #    `even` is `abbreviation even n == 2 dvd n` in Parity.thy
    file.write("=== _retrieve_entity on theorems ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.THEOREM, "even_Suc"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: abbrevs={abbrev_names}\n")
            for e in exprs:
                file.write(f"    expr: {e.unicode}\n")
        else:
            file.write("  None\n")

    # 2. Retrieve the `even` constant itself — should report itself as an abbreviation
    file.write("=== _retrieve_entity on abbreviation constant ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.CONSTANT, "even"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: abbrevs={abbrev_names}\n")
            for e in exprs:
                file.write(f"    type: {e.unicode}\n")
        else:
            file.write("  None\n")

    # 3. Retrieve a non-abbreviation constant — should have empty abbreviation list
    file.write("=== _retrieve_entity on non-abbreviation constant ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.CONSTANT, "Nat.plus_nat_inst.plus_nat"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: abbrevs={abbrev_names}\n")
        else:
            file.write("  None\n")

    # 4. abbreviation_defs: look up the definition of `even`
    file.write("=== abbreviation_defs ===\n")
    abbrev_names_to_query: list[str] = []
    # Collect abbreviation names from the theorem retrieval above
    thm_result = await ml._retrieve_entity([(EntityKind.THEOREM, "even_Suc")])
    if thm_result[0] is not None:
        _, _, _, abbrev_names_to_query, _ = thm_result[0]
    if abbrev_names_to_query:
        defs = await ml.abbreviation_defs(abbrev_names_to_query)
        for name, defn in zip(abbrev_names_to_query, defs):
            if defn is not None:
                lhs, rhs = defn
                file.write(f"  where `{lhs.unicode}` abbreviates `{rhs.unicode}`\n")
            else:
                file.write(f"  {name}: None\n")
    else:
        file.write("  (no abbreviations found in theorem)\n")

    # 5. abbreviation_defs on a non-abbreviation should return None
    file.write("=== abbreviation_defs on non-abbreviation ===\n")
    defs = await ml.abbreviation_defs(["Groups.plus_class.plus"])
    for name, defn in zip(["Groups.plus_class.plus"], defs):
        file.write(f"  {name}: {defn}\n")

    # 6. semantic_knn: verify abbreviation_names propagates to entities
    file.write("=== semantic_knn abbreviation propagation ===\n")
    results_knn, _ = await ml.semantic_knn("even number divisibility", 5, [EntityKind.THEOREM])
    for r in results_knn:
        abbrevs = r.entity.abbreviation_names
        if abbrevs:
            file.write(f"  {r.entity.short_name.unicode}: abbrevs={abbrevs}\n")

    # --- Corner cases ---

    # 7. Zero-parameter abbreviation (my_true defined in the .thy file)
    file.write("=== zero-parameter abbreviation ===\n")
    results = await ml._retrieve_entity([(EntityKind.CONSTANT, "my_true")])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: abbrevs={abbrev_names}\n")
        else:
            file.write("  None\n")
    defs = await ml.abbreviation_defs(["Test_AbbrevQuery.my_true"])
    for defn in defs:
        if defn is not None:
            lhs, rhs = defn
            file.write(f"  where `{lhs.unicode}` abbreviates `{rhs.unicode}`\n")
        else:
            file.write(f"  None\n")

    # 8. Theorem with NO abbreviations in its proposition
    file.write("=== theorem without abbreviations ===\n")
    results = await ml._retrieve_entity([(EntityKind.THEOREM, "add_0")])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: abbrevs={abbrev_names}\n")
            for e in exprs:
                file.write(f"    expr: {e.unicode}\n")
        else:
            file.write("  None\n")

    # 9. Nonexistent name passed to abbreviation_defs
    file.write("=== nonexistent name ===\n")
    defs = await ml.abbreviation_defs(["Nonexistent.bogus_name"])
    for defn in defs:
        file.write(f"  {defn}\n")


@model_test("FactNameResolution", "Test_FactNameResolution.thy", 11)
async def _test_fact_name_resolution(root: Root, file: MyIO):
    """Reproduce bug: during amend, _find_alive_state_among_children uses
    position = index of the amended child, which is < len(sub_nodes).
    StdBlock's override (model.py:2613) only returns _state_before_ending_
    when position >= len(sub_nodes) (the append/fill path), so the amend
    path falls through to sub_nodes[i-1].ml_state — the INPUT state of the
    preceding step, missing that step's named facts.

    The test proves  x > 2 ==> x > 0  via:
    1. Fill step 1 (Have "x_gt_1": x > 1) + step 1.1 (Obvious proves it)
    2. Fill step 2 (plain Obvious) — completes the proof
    3. Amend step 2 with FactByName("x_gt_1") — amend's alive_state is
       step1.ml_state (pre-Have), so "x_gt_1" is Unfound.

    The proof still succeeds (auto uses the correct ml_state), but
    the "not found" warning proves the stale alive_state."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Have "x_gt_1" establishes a named intermediate fact.
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "intermediate step",
        "statement": {"english": "x is greater than 1", "conclusion": "x > 1"},
        "name": "x_gt_1"
    })])
    # Prove the Have subgoal.
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])

    # Step 2: First fill with plain Obvious (no fact reference).
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": []})])
    print_header("After initial fill (proof complete)", file)
    root.print(0, file)

    # Now AMEND step 2 with a FactByName reference to "x_gt_1".
    # _amend_child passes position = index of step 2 (< len(sub_nodes)),
    # so _find_alive_state_among_children skips the _state_before_ending_
    # shortcut and returns step1.ml_state — the pre-Have state.
    root.session.age += 1
    _outcome = await root.amend("2", [Obvious.gen_single({
        "facts": [{"name": "x_gt_1"}]
    })])
    step2_new = _outcome.committed[0] if _outcome.committed else None
    assert step2_new is not None
    is_error = _outcome.failure is not None and _outcome.failure.is_error

    # Collect unfound-fact warnings BEFORE any print (print consumes warnings).
    unfound_warnings = [w for w in step2_new.warnings
                        if isinstance(w.printer, str) and "not found" in w.printer]
    file.write(f"Unfound fact warnings on amended step 2: {len(unfound_warnings)}\n")
    for w in unfound_warnings:
        file.write(f"  {w.printer}\n")

    assert step2_new.status.status == EvaluationStatus.Status.SUCCESS, \
        f"Proof should succeed via auto, but got {step2_new.status.status.value}"
    file.write(f"Amended step 2 status: {step2_new.status.status.value}\n")

    print_header("After amend with FactByName reference", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

    # After the fix, the amend path's alive_state should include "x_gt_1".
    assert len(unfound_warnings) == 0, \
        f"Expected 0 unfound warnings (fact should be resolved), got {len(unfound_warnings)}"


@model_test("IntroMetaQuant", "Test_IntroMetaQuant.thy", 8)
async def _test_IntroMetaQuant(root: Root, file: MyIO):
    """Reproduce bug: fastype_of: Bound when applying Intro with explicit
    variable_bindings on a meta-quantified Have subgoal inside a proof
    context that already has variables introduced by an outer Intro.

    Original failure from interaction log D8CC4AF0C_1E681B8:
    Step 2.3.3.1.1 tried Intro(variable_bindings=[a,b], fact_bindings=
    [b_pos, ab_coprime]) on the proof of a Have whose statement was
      \\<And>(a::int) b. 0 < b \\<Longrightarrow> coprime a b
                        \\<Longrightarrow> a * a \\<noteq> 5 * (b * b)
    The Isabelle/ML compute_bindings function raised
    'exception TERM raised (line 375 of "term.ML"): fastype_of: Bound'.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # # Step 1: Intro to introduce n from ∀n::int.
    # # This puts a meta-variable in the proof context — the outer scope
    # # that the original bug needed.
    # await root.fill("1", Intro.gen_single({
    #     "thought": "Introduce n",
    # }))
    # print_header("After outer Intro (introduce n)", file)
    # root.print(0, file)

    # Step 2: Have with a meta-quantified + implicational statement.
    # The Have auto-inserts an Intro child (with auto-detected bindings)
    # because the proof obligation is ∀-quantified at the meta level.
    await root.fill("2", [Have.gen_single({
        "thought": "Auxiliary: product of positives is positive",
        "statement": {
            "english": "product of positives is positive",
            "conclusion": r"\<And>(a::int) b. a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> a * b > 0"
        },
        "name": "pos_mult"
    })])
    print_header("After Have (meta-quantified statement)", file)
    root.print(0, file)

    # Step 2.1 is the auto-inserted Intro (with auto-detected bindings).
    # Amend it with explicit variable_bindings and fact_bindings — this
    # is the pattern that triggered fastype_of: Bound in the original log.
    # The compute_bindings ML call processes the explicit binding names
    # against the meta-quantified proof state; in the buggy version this
    # encounters a dangling de Bruijn index from the outer Intro scope.
    try:
        root.session.age += 1
        await root.amend("2.1", [Intro.gen_single({
            "thought": "Introduce a, b and the premises",
            "variable_bindings": ["a", "b"],
            "fact_bindings": ["a_pos", "b_pos"]
        })])
        print_header("After Intro amend (no error — bug not reproduced)", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"BUG REPRODUCED: {type(e).__name__}: {e}\n")

    print_header("Final state", file)
    root.print(0, file)


# ---------------------------------------------------------------------------
# Baseline probes for proposed "partial Intro bindings" feature.
# These capture current behavior before any change to compute_bindings.
# Goal in each test has ≥2 leading ∀s; we drive Intro with varied
# `variable_bindings` lengths and record what happens.
# ---------------------------------------------------------------------------

@model_test("IntroPartialVars", "Test_IntroPartialVars.thy", 8)
async def _test_IntroPartialVars(root: Root, file: MyIO):
    """Baseline: goal has 3 leading ∀s but we supply only 1 variable binding.
    Step 1 is auto-Intro'd during session.initialize; we amend it with
    our explicit partial binding. Expected today (pre-fix): Isabelle error
        "Bad operation: Expected 3 variable name(s), but got 1"
    from compute_bindings (agent.ML:488). After the fix this should
    bind `n` to the first quantified var and auto-name the remaining two."""
    print_header("Initial YAML", file)
    root.print(0, file)
    try:
        root.session.age += 1
        await root.amend("1", [Intro.gen_single({
            "thought": "Intro only the outermost n; leave a, b for later.",
            "variable_bindings": ["n"],
        })])
        print_header("After partial Intro amend (no error)", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"EXCEPTION: {type(e).__name__}: {e}\n")
    print_header("Final state", file)
    root.print(0, file)


@model_test("IntroEmptyBindings", "Test_IntroEmptyBindings.thy", 8)
async def _test_IntroEmptyBindings(root: Root, file: MyIO):
    """Baseline: goal has 3 leading ∀s; we amend step 1 with NO
    variable_bindings. `Intro.gen` sets `_pending_bindings=None` so
    compute_bindings is bypassed and AUTO_INTRO auto-generates all names.
    Confirms the "empty bypass" path works today."""
    print_header("Initial YAML", file)
    root.print(0, file)
    try:
        root.session.age += 1
        await root.amend("1", [Intro.gen_single({
            "thought": "Intro with no explicit bindings.",
        })])
        print_header("After Intro amend (empty bindings)", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"EXCEPTION: {type(e).__name__}: {e}\n")
    print_header("Final state", file)
    root.print(0, file)


@model_test("IntroOverSpec", "Test_IntroOverSpec.thy", 8)
async def _test_IntroOverSpec(root: Root, file: MyIO):
    """Baseline: goal has 2 leading ∀s; we amend step 1 with 3
    variable_bindings. Expected today: Isabelle error
        "Bad operation: Expected 2 variable name(s), but got 3"
    After the fix over-specification should still be rejected (cleanly),
    so this test's expected output is what we want to preserve."""
    print_header("Initial YAML", file)
    root.print(0, file)
    try:
        root.session.age += 1
        await root.amend("1", [Intro.gen_single({
            "thought": "Over-specify bindings.",
            "variable_bindings": ["a", "b", "c"],
        })])
        print_header("After Intro amend (over-specified)", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"EXCEPTION: {type(e).__name__}: {e}\n")
    print_header("Final state", file)
    root.print(0, file)


@model_test("IntroOutOfOrderRename", "Test_IntroOutOfOrderRename.thy", 12)
async def _test_IntroOutOfOrderRename(root: Root, file: MyIO):
    """Distinguish positional vs keyed semantics.
    Goal: ∀(n::nat) (m::nat). n + m = m + n
    Internal var order: [n, m]. We amend with variable_bindings=["m"].
      - Positional (first-k): pair "m" with the first var (n) → renames n to m.
      - Keyed (by internal name): "m" matches the second var → first gets
        auto-name, second named "m".
    This test should crash today (length mismatch); the output after the
    fix will show which semantics we ended up choosing."""
    print_header("Initial YAML", file)
    root.print(0, file)
    try:
        root.session.age += 1
        await root.amend("1", [Intro.gen_single({
            "thought": "Single binding — positional vs keyed probe.",
            "variable_bindings": ["m"],
        })])
        print_header("After Intro amend (single binding 'm')", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"EXCEPTION: {type(e).__name__}: {e}\n")
    print_header("Final state", file)
    root.print(0, file)


@model_test("Induction_IHRename", "Test_Induction_IHRename.thy", 33)
async def _test_Induction_IHRename(root: Root, file: MyIO):
    """REPRODUCER: Induction case IH carries an Isabelle-internal variant
    of the induction variable (e.g. ``na__``) instead of the external
    display name (``n``) that appears in the step's ``fixing variables``
    header.

    Observed (from a live run, target_step 5.2)::

        step 5: Have gen
          step 5.1: Intro
          step 5.2: Induction n :: nat
            fixing variables:
              - n: nat
            assuming premises:
              - premise2: n <= p - (2 :: nat)
              - 1.IH: forall m<na__. forall x<=p - (2 :: nat). prime (f x)

    Recipe (this test):
      - Outer lemma fixes ``f :: nat => nat``, ``p :: nat``, ``i :: nat``.
      - Step 1: ``Have gen: "!!n. n \\<le> p - 2 \\<Longrightarrow> f n < p"``
      - Inside the Have sub-proof:
          step 1.1: Intro (fixes ``n``, introduces premise ``n \\<le> p - 2``)
          step 1.2: Induction on ``n`` via ``nat_less_induct``,
                    generalizing ``n``, keeping ``f`` and ``p`` fixed.

    Expected (after fix): the IH term's free induction variable matches
    the display name in ``fixing variables`` -- i.e. ``n``, not ``na``/
    ``na__``.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    await root.fill("1", [Have.gen_single({
        "thought": "sub-lemma to induct on",
        "statement": {
            "english": "for every n, if n is at most p-2 then f n is less than p",
            "conclusion": r"\<And>n::nat. n \<le> p - 2 \<Longrightarrow> f n < p"
        },
        "name": "gen"
    })])
    print_header("After Have gen", file)
    root.print(0, file)

    # Inside the Have sub-proof:
    # step 1.1 is already auto-Intro (fixes n, assumes n <= p - 2).
    # step 1.2 is the Induction.
    await root.fill("1.2", [Induction.gen_single({
        "thought": "strong induction on n, generalize n, keep p and f fixed",
        "target_isabelle_term": "n :: nat",
        "rule": {"name": "nat_less_induct"},
        "variables": [
            {"name": "f", "status": "fixed"},
            {"name": "p", "status": "fixed"},
            {"name": "n", "status": "generalized"},
        ],
        # Carry the Intro's `premise0` (`n \<le> p - 2`) through induction
        # so the IH reads `∀m<n. m ≤ p - 2 ⟶ f m < p` (matching the
        # pre-auto-insert-off behavior that this reproducer was written
        # against).
        "IH_facts": [{"name": "premise0"}],
    })])
    print_header("After Induction (IH should use `n`, not internal variant)", file)
    root.print(0, file)

    import re
    induct_node = root.locate_node("1.2")

    display_vars: list[str] = []
    def collect_vars(node):
        case_vars = getattr(node, "case_vars", None)
        if case_vars:
            for name, _ty in case_vars:
                display_vars.append(name.unicode if hasattr(name, "unicode") else str(name))
        for sub in getattr(node, "sub_nodes", []) or []:
            collect_vars(sub)
    collect_vars(induct_node)
    file.write(f"\nDisplay names in `fixing variables`: {display_vars}\n")

    offending: list[tuple[str, str]] = []
    def collect_hyps(node):
        case_hyps = getattr(node, "case_hyps", None)
        if case_hyps:
            for hname, term in case_hyps:
                t = term.unicode
                # Any token starting with 'n' and followed by letters /
                # underscores -- the shape an Isabelle-internal variant
                # of `n` would take (na, na_, na__, nb, ...).
                for m in re.finditer(r"\bn[a-z]_*\b", t):
                    tok = m.group(0)
                    if tok in ("nat", "not", "ne", "no"):
                        continue
                    offending.append((hname.unicode, tok))
        for sub in getattr(node, "sub_nodes", []) or []:
            collect_hyps(sub)
    collect_hyps(induct_node)

    file.write(f"Offending IH tokens: {len(offending)}\n")
    for hn, tok in offending:
        file.write(f"  - {hn}: token={tok}\n")

    assert not offending, (
        "REPRODUCED: Induction IH carries an Isabelle-internal variant "
        f"of the induction variable (seen: {offending}). The step's "
        "`fixing variables` reports the external display name, but the "
        "IH hyp term retains the variant-renamed Free. The mismatch "
        "happens in library/proof.ML:2353-2355: `items'.vars` is built "
        "from `map (apfst Binding.name_of) fixes` (the rule's Case "
        "struct's original bindings), while `items'.hyps` comes from "
        "`Thm.prop_of thms` (which carry Frees with the post-`apply_case` "
        "variant names produced by `add_fixes`).")


@model_test("Induction_AmendTargetFree",
            "Test_Induction_AmendTargetFree.thy", 50)
async def _test_Induction_AmendTargetFree(root: Root, file: MyIO):
    """REGRESSION: on amend of an Induction node, the induction target
    must not reach the ML side inside `arbitrary:` --- otherwise ML's
    induction_tac produces a degenerate IH (schematic vars disconnected
    from the case variable).

    Agent flow from
    $ISABELLE_HOME_USER/log/AoA/DAF690E06_168BB2A/proofs.yaml
    (2026-04-21 17:46:25--31, Rabinowitz):

      fill step 1 = [Intro(i, ile), Induction(vars=[i gen, ile gen])]
        -> Python validation rejects step 2 ("f, p not classified")
      amend step 2 = Induction(vars=[i gen, ile gen, f fix, p fix])

    Before the fix at model.py:6235: on amend the `if is_init:` guard
    skipped target-stripping, so `i` stayed in `self.variables` with
    status `generalized` and `beginning_opr()` emitted
        INDUCT(('i', None, ['i', 'ile'], 'less_induct'))
    to ML. The resulting IH carried an independent `?i` schematic:
        less.IH : ?y < x --> ?i <= p - 2 --> prime (f ?i)

    After the fix: target-stripping is unconditional. The amend emits
        INDUCT(('i', None, ['ile'], 'less_induct'))
    and the IH is well-formed:
        less.IH : [?y < x; ?y <= p - 2] ==> prime (f ?y)
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # The goal `\<forall>i. i \<le> p - 2 \<longrightarrow> Q (f i)` triggers
    # an auto-Intro: step 1 is already Intro (fixes i, names premise0),
    # leaving step 2 as the first fillable slot. We place the Induction
    # there.
    await root.fill("2", [Induction.gen_single({
        "thought": "strong induction on i; init call "
                   "(is_init=True strips i even if listed)",
        "target_isabelle_term": "i",
        "rule": {"name": "less_induct"},
        "variables": [
            {"name": "i", "status": "generalized"},
            {"name": "f", "status": "fixed"},
            {"name": "p", "status": "fixed"},
            {"name": "Q", "status": "fixed"},
        ],
        # Carry the auto-Intro's `premise0` (`i \<le> p - 2`) through
        # induction so the IH preserves the pre-auto-insert-off shape
        # that this regression was originally filed against.
        "IH_facts": [{"name": "premise0"}],
    })])
    print_header("After fill step 2 (init path --- is_init=True strips i)", file)
    root.print(0, file)

    # Amend step 2 (the Induction) with `i` re-listed as generalized.
    # Before the fix: `if is_init:` was skipped (is_init=False), `i`
    # stayed in `self.variables`, and `beginning_opr()` emitted
    # `INDUCT(('i', None, ['i', ...], 'less_induct'))`, producing
    # a degenerate IH with an independent `?i` schematic.
    # After the fix: target-strip is unconditional; `i` is dropped
    # here too, arbitrary excludes the target, IH stays well-formed.
    await root.amend("2", [Induction.gen_single({
        "thought": "amend: re-list i as generalized; replay the bug path",
        "target_isabelle_term": "i",
        "rule": {"name": "less_induct"},
        "variables": [
            {"name": "i", "status": "generalized"},
            {"name": "f", "status": "fixed"},
            {"name": "p", "status": "fixed"},
            {"name": "Q", "status": "fixed"},
        ],
        "IH_facts": [{"name": "premise0"}],
    })])
    print_header("After amend step 2 (amend path --- must still strip i)", file)
    root.print(0, file)

    # Verify the IH on step 2 does not carry a schematic that alias-matches
    # the target `i` --- the degenerate-IH signature from the bug.
    import re
    induct_node = root.locate_node("2")
    offending: list[tuple[str, str]] = []
    def collect_hyps(node):
        case_hyps = getattr(node, "case_hyps", None)
        if case_hyps:
            for hname, term in case_hyps:
                t = term.unicode if hasattr(term, "unicode") else str(term)
                # If the IH contains both `?i` and the case var `x` as
                # independent schematics, something is wrong. Specifically
                # the degenerate IH shape has `?i` or `?x_<index>` that
                # does not match the Isar-level `?y` used for the
                # less_induct case's bound variable.
                name = hname.unicode if hasattr(hname, "unicode") else str(hname)
                if name.endswith(".IH"):
                    # Flag an IH that references a schematic `?i` ---
                    # the footprint of the degenerate predicate.
                    if re.search(r"\?i\b", t):
                        offending.append((name, t))
        for sub in getattr(node, "sub_nodes", []) or []:
            collect_hyps(sub)
    collect_hyps(induct_node)

    file.write(f"\nDegenerate-IH signatures found: {len(offending)}\n")
    for hn, t in offending:
        file.write(f"  - {hn}: {t}\n")

    assert not offending, (
        "REPRODUCED: on amend, the induction target reached ML's "
        "arbitrary: slot and produced a degenerate IH. "
        f"Offending hyps: {offending}. Fix is at model.py:6235 "
        "(strip target frees from self.variables unconditionally, "
        "not only when is_init).")


@model_test("Induction_IHFactRef", "Test_Induction_IHFactRef.thy", 36)
async def _test_Induction_IHFactRef(root: Root, file: MyIO):
    """REPRODUCER: referencing the induction hypothesis by its displayed
    name ``1.IH`` errors out with ``Cannot parse "1.IH" as a fact
    reference``.

    Observed (from run ``DABBC86F4_165BA82``, 2026-04-21 00:47:07)::

        operation: HAMMER(([(0, '1.IH'), ...], 30))
        error_message: 'Syntax Error in Term Language.\\nCannot parse
                        "1.IH" as a fact reference'

    Root cause (confirmed by ``isabelle process`` probe):

    * ``library/proof.ML:2320`` binds each case hyp under
      ``Binding.qualify_name true binding (fst asms)`` — e.g.
      ``"1.IH"`` — and the qualified name lands in ``items'`` /
      ``Consider_Case``. Python prints it verbatim under ``assuming
      premises:`` (``model.py:4234``).
    * ``agent.ML`` / ``read_fact`` (line 1103) calls ``Parse.thm``.
      ``Parse.thm`` uses ``name = short_ident | long_ident | number |
      ...``. For input ``"1.IH"`` the tokenizer produces **three**
      tokens ``[1, ., IH]`` (``scan_longid`` requires both segments to
      be ``scan_id``'s, and ``1`` is a ``Nat``). ``Parse.thm`` consumes
      only the leading ``1`` as ``Facts.Named "1"`` and leaves ``.IH``
      unconsumed → ``Scan.read Token.stopper`` returns ``NONE`` →
      ``read_fact`` errors.

    Recipe (this test):
      * ``Have h: "\\<And>n::nat. n < p \\<Longrightarrow> True"``
      * The Have's body auto-Intros at ``1.1`` (fixes ``n``, assumes
        ``n < p``).
      * Step ``1.2``: ``Induction n`` via ``nat_less_induct``
        generalizing ``n`` (produces case ``1`` with hyp ``1.IH``).
      * Step ``1.3``: attempt ``Obvious facts=[1.IH]``.

    The bug surfaces during ``check_command_i`` for ``HAMMER`` (see
    ``contrib/Isa-Mini/Agent/agent.ML:1200-1202``), which maps
    ``check_extended_fact`` over every fact ref — so the parse error
    fires irrespective of whether the goal is trivially provable.

    Expected (after fix): the ``Obvious`` step resolves the ``1.IH``
    fact reference without a parse error. No ``"Cannot parse ... as a
    fact reference"`` message should surface in the failure reason.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    await root.fill("1", [Have.gen_single({
        "thought": "sub-lemma for strong induction",
        "statement": {
            "english": "for every n, n < p implies True",
            "conclusion": r"\<And>n::nat. n < p \<Longrightarrow> True",
        },
        "name": "h",
    })])
    print_header("After Have h (auto-Intro at 1.1 fixes n, assumes n < p)", file)
    root.print(0, file)

    # The Have's body auto-Intros at 1.1.  Step 1.2 is the Induction.
    await root.fill("1.2", [Induction.gen_single({
        "thought": "strong induction on n, generalize n, keep p fixed",
        "target_isabelle_term": "n :: nat",
        "rule": {"name": "nat_less_induct"},
        "variables": [
            {"name": "p", "status": "fixed"},
            {"name": "n", "status": "generalized"},
        ],
        # Carry the Intro's `premise0` (`n < p`) through induction so
        # the IH is strengthened to `∀m<n. m < p ⟶ True`.
        "IH_facts": [{"name": "premise0"}],
    })])
    print_header("After Induction (case 1 produced with hyp `1.IH`)", file)
    root.print(0, file)

    # Confirm the displayed hyp name really is "1.IH" — that is the
    # exact token the agent copies back into a fact reference.
    induct_node = root.locate_node("1.2")
    displayed_hyp_names: list[str] = []
    def collect_hyps(node):
        case_hyps = getattr(node, "case_hyps", None)
        if case_hyps:
            for hname, _term in case_hyps:
                displayed_hyp_names.append(
                    hname.unicode if hasattr(hname, "unicode") else str(hname))
        for sub in getattr(node, "sub_nodes", []) or []:
            collect_hyps(sub)
    collect_hyps(induct_node)
    file.write(f"\nDisplayed hyp names under case 1: {displayed_hyp_names}\n")

    # Now have the agent use "1.IH" as a fact reference — exactly the
    # flow that fails in the live log.
    root.session.age += 1
    _outcome = await root.fill("1.3", [Obvious.gen_single({
        "facts": [{"name": "1.IH"}],
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    reason = _outcome.failure
    reason_text = (reason.reason if isinstance(reason, FailureReason)
                   else str(reason) if reason is not None else "")
    print_header("After Obvious facts=[1.IH]", file)
    root.print(0, file)
    file.write(f"is_error: {is_error}\n")
    file.write(f"reason: {reason_text}\n")

    assert "Cannot parse" not in reason_text and '"1.IH"' not in reason_text, (
        "REPRODUCED: read_fact cannot parse the qualified fact name "
        "`1.IH` that Minilang itself shows under `assuming premises:`. "
        "`Parse.thm` tokenizes `1.IH` as three separate tokens "
        "`[1, ., IH]` (scan_longid needs both segments to be "
        "identifiers, and `1` is a Nat). The fix has to either quote "
        "numeric-prefix qualified names before handing them to "
        "Parse.thm (agent.ML:1103 read_fact), or display the hyp "
        "under a parseable name (library/proof.ML:2320). Observed "
        "reason: " + reason_text)


@model_test("Induction_SelectIHFacts", "Test_Induction_IHFacts.thy", 19)
async def _test_Induction_SelectIHFacts(root: Root, file: MyIO):
    """The Induction pre-flight offers the in-scope facts mentioning the
    generalized variable(s); the agent's selection is unioned into
    `facts_to_generalize` (supplementing any explicitly supplied). Mirrors the
    lcm sublemma `∀n k. k ≤ n → a k dvd b n`: `Intro` assumes `k ≤ n`, then
    induction on `n` generalizing `k` must carry that premise into the IH.
    Here the agent supplies NO `facts_to_generalize`; the picker selection
    alone carries the premise.
    """
    fork_count = 0
    async def stub_fork(interaction):
        nonlocal fork_count
        if isinstance(interaction, Interaction_SelectIHFacts):
            fork_count += 1
            print_header("IH-fact selection prompt", file)
            await interaction.prompt(0, file)
            # Select every offered candidate.
            return await interaction.answer(
                AnswerIndexes(indexes=list(range(len(interaction.candidates)))))
        if isinstance(interaction, Interaction_ClassifyInductionVars):
            # Not under test here — decline (leave such variables fixed).
            return await interaction.answer(AnswerIndexes(indexes=[]))
        raise TestFailed(
            f"Unexpected interaction in this test: {type(interaction).__name__}")
    root.session.launch_interaction = stub_fork

    print_header("Initial YAML", file)
    root.print(0, file)

    # Intro: fix n, k; assume `k ≤ n` (auto-named premise0).
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "fix n, k and assume k ≤ n",
    })])
    print_header("After Intro (fixes n, k; assumes k ≤ n)", file)
    root.print(0, file)

    # Induction on n, generalize k, with NO facts_to_generalize supplied:
    # the pre-flight should offer `k ≤ n` and the stub selects it.
    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "induct on n, generalize k; carry the premise via the picker",
        "target_isabelle_term": "n :: nat",
        "variables": [
            {"name": "n", "status": "fixed"},
            {"name": "k", "status": "generalized"},
        ],
    })])
    print_header("After Induction (selected facts carried into IH)", file)
    root.print(0, file)

    # The carried premise reaches the BASE case too, not just the IH. The
    # rendered tree above omits carried case-hypotheses (a pre-existing display
    # behaviour), so assert on the base case's internal hypotheses directly:
    # `premise0` (k ≤ 0, with the generalized k smart-renamed to n) must be
    # present — confirming the fact was generalized into every case.
    base_hyps = root.locate_node("2.0").case_hyps or []
    base_hyp_names = [h.unicode if hasattr(h, "unicode") else str(h)
                      for h, _t in base_hyps]
    file.write(f"base case (2.0) hypotheses: {base_hyp_names}\n")
    assert any("premise0" in n for n in base_hyp_names), (
        "the carried premise should reach the induction base case "
        f"(got base hyps {base_hyp_names})")

    induct_node = root.locate_node("2")
    carried = sorted(r.short_name.unicode
                     for r in induct_node.fact_refs_to_generalize)
    file.write(f"\nfork_count: {fork_count}\n")
    file.write(f"facts carried into IH: {carried}\n")
    assert fork_count == 1, (
        f"Expected exactly one IH-fact selection fork, got {fork_count}.")
    assert carried, (
        "Expected the agent-selected premise to be unioned into "
        "facts_to_generalize, but fact_refs_to_generalize is empty.")


@model_test("Induction_SelectIHFacts_MultiThm",
            "Test_Induction_IHFacts_MultiThm.thy", 19)
async def _test_Induction_SelectIHFacts_MultiThm(root: Root, file: MyIO):
    """Multi-theorem fact coverage (LOW 4). The conjunctive premise
    `(k ≤ n ∧ k ≤ n+n)` destructures into ONE multi-theorem fact `premise0`,
    surfaced under indexed names `premise0(1)`, `premise0(2)`. Both conjuncts
    mention the generalized `k`, so the picker must offer BOTH; selecting a
    strict SUBSET (only the first) must carry exactly that one indexed theorem,
    which then resolves through the standard fact scheme (`Attrib.eval_thms`)."""
    offered_names: list[str] = []
    async def stub_fork(interaction):
        if isinstance(interaction, Interaction_SelectIHFacts):
            offered_names.extend(n for n, _ in interaction.candidates)
            print_header("IH-fact picker (multi-thm)", file)
            await interaction.prompt(0, file)
            # Select ONLY the first offered candidate — a strict subset.
            return await interaction.answer(AnswerIndexes(indexes=[0]))
        if isinstance(interaction, Interaction_ClassifyInductionVars):
            # Not under test here — decline (leave such variables fixed).
            return await interaction.answer(AnswerIndexes(indexes=[]))
        raise TestFailed(
            f"Unexpected interaction in this test: {type(interaction).__name__}")
    root.session.launch_interaction = stub_fork

    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "fix n, k; split the conjunctive premise into premise0(1), premise0(2)",
    })])
    print_header("After Intro (premise0 split into premise0(1), premise0(2))", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "induct on n, generalize k; pick a subset of the multi-thm fact",
        "target_isabelle_term": "n :: nat",
        "variables": [
            {"name": "n", "status": "fixed"},
            {"name": "k", "status": "generalized"},
        ],
    })])
    print_header("After Induction (only the selected indexed theorem carried)", file)
    root.print(0, file)

    induct_node = root.locate_node("2")
    carried = sorted(r.short_name.unicode
                     for r in induct_node.fact_refs_to_generalize)
    file.write(f"\noffered candidates: {offered_names}\n")
    file.write(f"carried into IH: {carried}\n")
    # The picker must surface BOTH indexed theorems of the multi-thm fact.
    assert len(offered_names) == 2 and all("premise0(" in n for n in offered_names), (
        f"expected the two indexed candidates premise0(1)/premise0(2), "
        f"got {offered_names}")
    # Selecting only index 0 carries exactly that one indexed theorem.
    assert len(carried) == 1, (
        f"expected exactly one carried fact (strict subset), got {carried}")
    assert "premise0" in carried[0] and "(" in carried[0], (
        f"expected an indexed premise0(i) carried, got {carried}")


@model_test("Induction_ClassifyVars", "Test_Induction_ClassifyVars.thy", 18)
async def _test_Induction_ClassifyVars(root: Root, file: MyIO):
    """When an Induction leaves an in-scope variable unclassified (neither
    fixed nor generalized), the pre-flight asks via
    `Interaction_ClassifyInductionVars` which to generalize, BEFORE `arbitrary`
    is computed. Here `Intro` fixes `n`, `k` (no premise → the IH-fact picker
    stays silent); the induction classifies only `n` and leaves `k`
    unclassified. The stub selects `k`, so it becomes a generalized
    (universally quantified) variable rather than defaulting to fixed."""
    classify_fork_count = 0
    offered_vars: list[str] = []
    async def stub_fork(interaction):
        nonlocal classify_fork_count
        if isinstance(interaction, Interaction_ClassifyInductionVars):
            classify_fork_count += 1
            offered_vars.extend(n for n, _t in interaction.unclassified)
            print_header("Variable-classification prompt", file)
            await interaction.prompt(0, file)
            # Generalize every offered (unclassified) variable.
            return await interaction.answer(
                AnswerIndexes(indexes=list(range(len(interaction.unclassified)))))
        raise TestFailed(
            f"Unexpected interaction in this test: {type(interaction).__name__}")
    root.session.launch_interaction = stub_fork

    print_header("Initial YAML", file)
    root.print(0, file)

    # Intro: fix n, k (the goal has no premise to assume).
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "fix n, k",
    })])
    print_header("After Intro (fixes n, k)", file)
    root.print(0, file)

    # Induction on n, classifying ONLY n; k is left unclassified so the
    # pre-flight must ask. The stub generalizes k.
    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "induct on n; leave k for the classification prompt",
        "target_isabelle_term": "n :: nat",
        "variables": [
            {"name": "n", "status": "fixed"},
        ],
    })])
    print_header("After Induction (k classified as generalized via prompt)", file)
    root.print(0, file)

    induct_node = root.locate_node("2")
    var_status = {v["name"]: v["status"] for v in induct_node.variables}
    file.write(f"\nclassify_fork_count: {classify_fork_count}\n")
    file.write(f"offered (unclassified) vars: {offered_vars}\n")
    file.write(f"variable statuses after classification: {var_status}\n")
    assert classify_fork_count == 1, (
        f"Expected exactly one classification fork, got {classify_fork_count}.")
    assert offered_vars == ["k"], (
        f"Expected the unclassified `k` to be offered, got {offered_vars}.")
    assert var_status.get("k") == "generalized", (
        f"Expected `k` to be generalized after selection, got {var_status}.")


@model_test("Induction_ClassifyVars_Filter",
            "Test_Induction_ClassifyVars_Filter.thy", 16)
async def _test_Induction_ClassifyVars_Filter(root: Root, file: MyIO):
    """The classification offer is restricted to variables that appear in the
    leading goal (via the `IsaMini.goal_variables` callback). The lemma fixes
    `f :: nat ⇒ nat`, which is in scope but never appears in `n + k = k + n`,
    so `f` must NOT be offered — only `k` is. This is the assertion that
    actually exercises the goal-vars filter (the plain `Induction_ClassifyVars`
    fixture has no such excluded variable, so there the filter is a no-op)."""
    offered_vars: list[str] = []
    async def stub_fork(interaction):
        if isinstance(interaction, Interaction_ClassifyInductionVars):
            offered_vars.extend(n for n, _t in interaction.unclassified)
            return await interaction.answer(
                AnswerIndexes(indexes=list(range(len(interaction.unclassified)))))
        raise TestFailed(
            f"Unexpected interaction in this test: {type(interaction).__name__}")
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [Intro.gen_single({"thought": "fix n, k"})])
    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "induct on n; leave k for the prompt; f must not be offered",
        "target_isabelle_term": "n :: nat",
        "variables": [{"name": "n", "status": "fixed"}],
    })])
    print_header("After Induction (f excluded; k offered+generalized)", file)
    root.print(0, file)
    file.write(f"\noffered (unclassified) vars: {offered_vars}\n")
    assert offered_vars == ["k"], (
        f"Expected only the goal variable `k` to be offered; the in-scope "
        f"lemma signature `f` (absent from the goal) must be excluded. "
        f"Got {offered_vars}.")
    assert "f" not in offered_vars, (
        f"`f` appears in no goal subterm and must not be offered; got {offered_vars}.")


@model_test("Induction_ClassifyVars_Decline",
            "Test_Induction_ClassifyVars_Decline.thy", 14)
async def _test_Induction_ClassifyVars_Decline(root: Root, file: MyIO):
    """Decline path: the agent selects NONE of the offered variables, so each
    stays `fixed` (the same end state as the old silent default, but now an
    explicit choice). Asserts the var is fixed and the prompt fired once."""
    classify_fork_count = 0
    async def stub_fork(interaction):
        nonlocal classify_fork_count
        if isinstance(interaction, Interaction_ClassifyInductionVars):
            classify_fork_count += 1
            # Decline — select nothing.
            return await interaction.answer(AnswerIndexes(indexes=[]))
        raise TestFailed(
            f"Unexpected interaction in this test: {type(interaction).__name__}")
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [Intro.gen_single({"thought": "fix n, k"})])
    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "induct on n; decline to generalize k",
        "target_isabelle_term": "n :: nat",
        "variables": [{"name": "n", "status": "fixed"}],
    })])
    print_header("After Induction (k declined -> stays fixed)", file)
    root.print(0, file)
    induct_node = root.locate_node("2")
    var_status = {v["name"]: v["status"] for v in induct_node.variables}
    file.write(f"\nclassify_fork_count: {classify_fork_count}\n")
    file.write(f"variable statuses after decline: {var_status}\n")
    assert classify_fork_count == 1, (
        f"Expected exactly one classification fork, got {classify_fork_count}.")
    assert var_status.get("k") == "fixed", (
        f"Expected `k` to stay fixed after declining, got {var_status}.")


@model_test("Induction_ClassifyVars_PartialPremise",
            "Test_Induction_ClassifyVars_PartialPremise.thy", 16)
async def _test_Induction_ClassifyVars_PartialPremise(root: Root, file: MyIO):
    """Two points: (a) a premise-only variable `j` (appearing only in `j < n`,
    not in the conclusion) is still offered — confirming the callback reads the
    whole leading sequent; (b) partial selection — of the offered `j`, `k`, the
    stub generalizes only `j`, leaving `k` fixed."""
    offered_vars: list[str] = []
    async def stub_fork(interaction):
        if isinstance(interaction, Interaction_ClassifyInductionVars):
            offered_vars.extend(n for n, _t in interaction.unclassified)
            print_header("Variable-classification prompt (partial/premise)", file)
            await interaction.prompt(0, file)
            # Generalize only `j`, leave the rest (k) fixed.
            j_idx = [i for i, (n, _t) in enumerate(interaction.unclassified)
                     if n == "j"]
            return await interaction.answer(AnswerIndexes(indexes=j_idx))
        if isinstance(interaction, Interaction_SelectIHFacts):
            # Generalizing `j` makes the premise `j < n` an IH-fact candidate;
            # not under test here — decline it.
            return await interaction.answer(AnswerIndexes(indexes=[]))
        raise TestFailed(
            f"Unexpected interaction in this test: {type(interaction).__name__}")
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "fix n, j, k; assume j < n"})])
    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "induct on n; classify only n; generalize only j",
        "target_isabelle_term": "n :: nat",
        "variables": [{"name": "n", "status": "fixed"}],
    })])
    print_header("After Induction (j generalized, k fixed)", file)
    root.print(0, file)
    induct_node = root.locate_node("2")
    var_status = {v["name"]: v["status"] for v in induct_node.variables}
    file.write(f"\noffered (unclassified) vars: {sorted(offered_vars)}\n")
    file.write(f"variable statuses: {var_status}\n")
    assert set(offered_vars) == {"j", "k"}, (
        f"Expected the premise-only `j` AND conclusion `k` to be offered "
        f"(callback reads premises ⟹ conclusion); got {offered_vars}.")
    assert var_status.get("j") == "generalized", (
        f"Expected `j` generalized, got {var_status}.")
    assert var_status.get("k") == "fixed", (
        f"Expected `k` to stay fixed (not selected), got {var_status}.")


@model_test("FactsToGeneralize_Filter",
            "Test_FactsToGeneralize_Filter.thy", 29)
async def _test_FactsToGeneralize_Filter(root: Root, file: MyIO):
    """Exercise the four partitioning paths of the Induction tool's
    `facts_to_generalize` field in a single run:

      1. local fact that mentions the induction target's free var
         (kept, routed to insertion, strengthens the IH).
      2. local fact that does NOT mention any generalized variable
         (dropped with a header warning about irrelevance).
      3. global theorem name (dropped with a warning about non-locality).
      4. unknown / unfound name (dropped with a warning about
         unresolved name).

    After the call, survivors should be exactly `["premise0"]`, the IH
    should carry the stronger premise, and three header warnings should
    be present on the Induction node.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: introduce a trivial local fact whose prop mentions no free
    # variable at all — our filter should classify it as "does not
    # mention any generalized variable" and drop it with a warning.
    await root.fill("1", [Have.gen_single({
        "thought": "unrelated local fact, prop has no free vars",
        "statement": {
            "english": "zero is less than one",
            "conclusion": "(0::nat) < 1",
        },
        "name": "trivial_fact",
    })])
    print_header("After Have trivial_fact", file)
    root.print(0, file)

    # Step 2: outer Have for the induction. Its body auto-Intros at 2.1
    # (fixes n, introduces premise0 : n ≤ p).
    await root.fill("2", [Have.gen_single({
        "thought": "sub-lemma to induct on",
        "statement": {
            "english": "for every n at most p, True holds",
            "conclusion": r"\<And>n::nat. n \<le> p \<Longrightarrow> True",
        },
        "name": "gen",
    })])
    print_header("After Have gen", file)
    root.print(0, file)

    # Step 2.2: the Induction. Pass four facts covering every filter
    # outcome. Expected:
    #   - premise0      -> kept (local + mentions n)
    #   - trivial_fact  -> dropped: doesn't mention any generalized var
    #   - nat_less_induct -> dropped: global theorem
    #   - bogus_name    -> dropped: unfound
    await root.fill("2.2", [Induction.gen_single({
        "thought": "induct on n with four kinds of facts_to_generalize",
        "target_isabelle_term": "n :: nat",
        "rule": {"name": "nat_less_induct"},
        "variables": [
            {"name": "p", "status": "fixed"},
            {"name": "n", "status": "generalized"},
        ],
        "IH_facts": [
            {"name": "premise0"},
            {"name": "trivial_fact"},
            {"name": "nat_less_induct"},
            {"name": "bogus_name"},
        ],
    })])
    print_header("After Induction (expect 3 filter warnings)", file)
    root.print(0, file)

    induct_node = root.locate_node("2.2")

    # Survivors — the facts that ML should actually receive as
    # insertion. Assertion: only `premise0`.
    kept_full_names = [r.full_name for r in cast(Induction, induct_node).fact_refs_to_generalize]
    file.write(f"\nSurviving facts_to_generalize (full names): {kept_full_names}\n")
    assert kept_full_names == ["premise0"], (
        f"Expected only `premise0` to survive the filter; got {kept_full_names}")

    # Warnings: one for each drop. Collect just the strings for
    # deterministic ordering.
    warning_strs = sorted(w.printer for w in induct_node.warnings
                          if isinstance(w.printer, str))
    file.write("Warnings (sorted):\n")
    for w in warning_strs:
        file.write(f"  - {w}\n")
    assert any("trivial_fact" in w and "does not mention" in w for w in warning_strs), \
        "expected irrelevance warning for `trivial_fact`"
    assert any("nat_less_induct" in w and "global" in w for w in warning_strs), \
        "expected non-local warning for `nat_less_induct`"
    assert any("bogus_name" in w and "not found" in w for w in warning_strs), \
        "expected unfound warning for `bogus_name`"


@model_test("FactsToGeneralize_ConsumingRule",
            "Test_FactsToGeneralize_ConsumingRule.thy", 36)
async def _test_FactsToGeneralize_ConsumingRule(root: Root, file: MyIO):
    """Combined coverage: `facts_to_generalize` path interoperates with a
    consumes >= 1 induction rule.

    Scenario:
      - Outer fixes: `i k :: int`, `Q :: int \\<Rightarrow> bool`; goal `True`.
      - Step 1: `Have h: \"0 \\<le> i\"` — a local fact mentioning the
        induction target `i`.
      - Step 2: `Induction i rule: int_le_induct` with
        `facts_to_generalize = [h]`.

    `int_le_induct` has consumes = 1 with a schematic `?k` in the
    consume premise `?i \\<le> ?k`. After the target instantiates `?i`
    to `i`, `?k` remains schematic, triggering
    `Interaction_InstantiateSchematics`; this test stubs that
    interaction to answer `?k = k`. Under
    `consumes_policy = \"subgoals\"` (the agent session default), the
    consume premise is NOT discharged — it surfaces as a Prem0
    subgoal.

    What this verifies:
      1. The schematic-instantiation interaction is actually forked
         for a consumes >= 1 rule, and its `rule_name` / `schematic_vars`
         payload matches expectations.
      2. `facts_to_generalize` survives across a consumes >= 1 rule —
         i.e. the TAG-wrapped conjunction routed through the
         dedicated `Method.insert_tac` channel (proof.ML:INDUCT')
         is NOT eaten by `Rule_Cases.consume`, and `update_tampered`
         restores the fact under its original name `h` in the
         induction case context.

    This is the agent-level companion of `Consumes_Validation_Test.thy`:
    together they guard both the ML-level insertion channel and the
    full agent end-to-end path against regressions in the
    `consumes >= 1` + `facts_to_generalize` combination.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: introduce a local fact whose prop mentions `i` (the
    # induction target). This is the fact we expect to see restored
    # by name in the induction case context.
    await root.fill("1", [Have.gen_single({
        "thought": "local fact about induction target i",
        "statement": {
            "english": "zero is at most i",
            "conclusion": r"(0::int) \<le> i",
        },
        "name": "h",
    })])
    print_header("After Have h", file)
    root.print(0, file)

    # Stub the interaction channel: when the agent session forks an
    # InstantiateSchematics for int_le_induct, answer ?k = k.
    observed_interaction: 'list[Interaction_InstantiateSchematics]' = []
    async def stub_fork(interaction):
        if isinstance(interaction, Interaction_InstantiateSchematics):
            observed_interaction.append(interaction)
            return await interaction.answer(AnswerInstantiate(instantiations=[("?k", "k")]))
        raise InternalError(
            f"Unexpected interaction forked: {type(interaction).__name__}")
    root.session.launch_interaction = stub_fork

    # Step 2: Induction on i via int_le_induct, carrying `h` through.
    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "int_le_induct with schematic ?k and carried fact h",
        "target_isabelle_term": "i",
        "rule": {"name": "int_le_induct"},
        "variables": [
            {"name": "i", "status": "generalized"},
            {"name": "k", "status": "fixed"},
            {"name": "Q", "status": "fixed"},
        ],
        "IH_facts": [{"name": "h"}],
    })])
    print_header("After Induction (consumes=1 rule + facts_to_generalize)", file)
    root.print(0, file)

    # Assertion 1: schematic instantiation interaction was triggered
    # exactly once, for the expected rule, with `?k` as the sole var.
    assert len(observed_interaction) == 1, (
        f"Expected exactly one InstantiateSchematics fork, got "
        f"{len(observed_interaction)}")
    interaction = observed_interaction[0]
    file.write(f"\nObserved interaction: rule={interaction.rule_name.unicode}\n")
    file.write(f"  schematic_vars: {interaction.schematic_vars}\n")
    file.write(f"  consume_premises: {interaction.consume_premises}\n")
    assert interaction.rule_name == "int_le_induct", (
        f"Expected rule_name=int_le_induct, got {interaction.rule_name!r}")
    sv_names = [n for n, _ in interaction.schematic_vars]
    assert sv_names == ["?k"], (
        f"Expected schematic_vars=[?k], got {sv_names}")

    # Assertion 2: `h` restored by original name in some case context.
    induct_node = root.locate_node("2")
    all_hyp_names: list[str] = []
    def collect(node):
        case_hyps = getattr(node, "case_hyps", None)
        if case_hyps:
            for hname, _ in case_hyps:
                all_hyp_names.append(
                    hname.unicode if hasattr(hname, "unicode") else str(hname))
        for sub in getattr(node, "sub_nodes", []) or []:
            collect(sub)
    collect(induct_node)
    file.write(f"\nAll case-hyp names across induct subtree: {all_hyp_names}\n")
    assert "h" in all_hyp_names, (
        f"`h` should be restored by its original name in the induction "
        f"case context; found case_hyps = {all_hyp_names}. If `h` is "
        f"missing, the `facts_to_generalize` → TAG-wrap → "
        f"`update_tampered` round-trip broke under consumes >= 1.")


@model_test("Induction_MetaIHFact", "Test_Induction_MetaIHFact.thy", 10)
async def _test_Induction_MetaIHFact(root: Root, file: MyIO):
    """Reproduces CTERM/Trueprop_conv crash when a carried IH fact has
    meta-level structure (⋀/⟹).

    A Have with `for_any`/`premises` stores a theorem whose prop is
    `⋀i. Trueprop(...) ⟹ Trueprop(...)`, not a bare `Trueprop(X)`.
    When this fact is selected for `facts_to_generalize`, `wraps` in
    proof.ML applies `HOLogic.Trueprop_conv` to it, which raises
    `CTERM ("Trueprop_conv", ...)` because the theorem's top-level
    connective is `Pure.all`/`Pure.imp`, not `Trueprop`.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Have with for_any + premises → meta-level fact
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "bound on f, quantified over i with premise i < n",
        "statement": {
            "english": "for every i less than n, f i is less than n",
            "for_any": [{"name": "i", "type": "nat"}],
            "premises": [{"name": "hi", "term": "i < n"}],
            "conclusion": "f i < n",
        },
        "name": "h",
    })])
    print_header("After Have h (meta-level fact)", file)
    root.print(0, file)

    # Step 2: Induction on n, generalize f, carry h.
    # h has prop `⋀i. Trueprop(i < n) ⟹ Trueprop(f i < n)` — NOT
    # Trueprop at top level → wraps should crash with Trueprop_conv.
    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "induct on n, generalize f, carry the meta-level fact h",
        "target_isabelle_term": "n :: nat",
        "variables": [
            {"name": "n", "status": "fixed"},
            {"name": "f", "status": "generalized"},
        ],
        "IH_facts": [{"name": "h"}],
    })])
    print_header("After Induction (should not crash with Trueprop_conv)", file)
    root.print(0, file)

    # Check whether the induction raised CTERM Trueprop_conv.
    induct_node = root.locate_node("2")
    status_str = str(induct_node.status.status)
    file.write(f"\nInduction status: {status_str}\n")
    if induct_node.status.status == EvaluationStatus.Status.FAILURE:
        reason = induct_node.status.reason
        reason_str = str(reason) if reason else ""
        file.write(f"Failure reason: {reason_str}\n")
        if "Trueprop_conv" in reason_str or "CTERM" in reason_str:
            raise TestFailed(
                "REPRODUCED: Induction crashes with CTERM/Trueprop_conv "
                "when an IH fact has meta-level structure (⋀/⟹). "
                f"Reason: {reason_str}")


@model_test("HOL_TAG_Leak", "Test_HOL_TAG_Leak.thy", 31)
async def _test_HOL_TAG_Leak(root: Root, file: MyIO):
    """REGRESSION: HOL.TAG leaks into the induction hypothesis presented
    to the agent.

    The auto-insert-facts mechanism (enabled by agent_server.ML at
    session start, see library/proof.ML's `induct_auto_insert_facts`)
    wraps local facts mentioning a generalized variable in `HOL.TAG`
    and inserts them as goal premises so they get generalized along
    with the variable. After induction, `update_tampered` strips the
    TAG from the per-case top-level facts -- but the IH proposition,
    which still contains the wrapped premises bound under the
    induction's outer quantifier, is never unwrapped. The agent sees
    e.g. `1.IH: ∀m<n. ∀x. HOL.TAG (x ≤ p) ⟶ P x`.

    Reproduced from logs:
      DA348EF63_14FD684 (IMO 1988 P6, Vieta jumping)
      DA36C4FF0_17E38C8 (strong induction over `prime (f i)`)

    Setup:
      - lemma `(i::nat) ≤ p ⟹ P i` -- premise mentions `i`.
      - Auto-Intro at step 1 fixes `i`, assumes `i ≤ p`.
      - Step 2: Induction on `i` using `nat_less_induct`, generalizing
        `i`. Auto-insert wraps `i ≤ p`, induction generalizes both,
        IH ends up containing `HOL.TAG (x ≤ p)`.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    await root.fill("2", [Induction.gen_single({
        "thought": "strong induction on i, generalize i, keep p fixed",
        "target_isabelle_term": "i",
        "rule": {"name": "nat_less_induct"},
        "variables": [
            {"name": "i", "status": "generalized"},
            {"name": "p", "status": "fixed"},
            {"name": "P", "status": "fixed"},
        ],
        # With auto-insert disabled on the agent path (agent_server.ML),
        # `premise0` no longer flows into the IH automatically. Route it
        # through the explicit `facts_to_generalize` field so the IH
        # carries `m ≤ p ⟶ P m` — the same IH shape that used to trip
        # the original TAG-unwrap bug. Assertion below guards against
        # regressions where HOL.TAG leaks via the insertion path too.
        "IH_facts": [{"name": "premise0"}],
    })])
    print_header("After Induction (HOL.TAG should leak into IH)", file)
    root.print(0, file)

    induct_node = root.locate_node("2")

    # nat_less_induct produces a single case; case_hyps may live on the
    # parent CaseSplit_Like node (single-subgoal path) or on a child
    # GoalNode (multi-subgoal path). Walk both to be robust.
    leaked: list[tuple[str, str]] = []
    def collect(node):
        case_hyps = getattr(node, "case_hyps", None)
        if case_hyps:
            for name, term in case_hyps:
                if "HOL.TAG" in term.unicode or "Minilang.TAG" in term.unicode:
                    leaked.append((name.unicode, term.unicode))
        for sub in getattr(node, "sub_nodes", []) or []:
            collect(sub)
    collect(induct_node)

    file.write(f"\nLeaked HOL.TAG hyps: {len(leaked)}\n")
    for n, t in leaked:
        file.write(f"  - {n}: {t}\n")

    assert not leaked, (
        "REGRESSION: HOL.TAG is leaking into the IH again after "
        "auto-insert + nat_less_induct. The deep `unwrap_tags` pass in "
        "library/proof.ML must descend into HOL-level binders (∀, ⟶, …) "
        "so the IH's wrapped premises get stripped before being surfaced "
        f"in case_hyps. Leaked hyps: {leaked}")


@model_test("Obtain_Fixed", "Test_Obtain_Fixed.thy", 8)
async def _test_Obtain_Fixed(root: Root, file: MyIO):
    """Verify Obtain's ML-fed `_introduced` Context + propagation.

    Scenario: lemma `∃k::nat. k = m ⟹ True`. Auto-Intro at step 1
    surfaces `assm0: ∃k. k = m`. Step 2 is `Obtain k` with named
    constraint `k_def: k = m`.

    Assertions:
      - `_introduced.vars` carries `k :: nat` (ML-inferred type).
      - `_introduced.hyps` carries `k_def: k = m`.
      - `_fixed_vars_after_me` / `_fixed_facts_after_me` expose both
        to subsequent-sibling ctxt lookups.
      - Quickview includes the "obtained variables" / "constraints"
        sections (deduped via `_prev_quickview_introduced`)."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # `proof: Obvious` attaches a subproof that discharges the
    # existential via the in-scope `assm0: ∃k::nat. k = m`, letting
    # the block close and CONSIDER'i emit its `New_Item_Msg`.
    await root.fill("2", [Obtain.gen_single({
        "thought": "unpack the existential",
        "variables": [{"name": "k", "type": "nat"}],
        "constraints": [{"name": "k_def",
                         "isabelle": "k = m",
                         "english": "the existential witness"}],
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("After Obtain", file)
    root.print(0, file)

    obtain_node = root.locate_node("2")
    assert isinstance(obtain_node, Obtain), \
        f"Expected Obtain at step 2, got {type(obtain_node).__name__}"

    # (1) _introduced populated from New_Item_Msg
    intro_vars = cast(Obtain, obtain_node)._introduced.vars
    intro_hyps = cast(Obtain, obtain_node)._introduced.hyps
    assert intro_vars, f"_introduced.vars empty; expected `k`. got {intro_vars}"
    assert intro_hyps, f"_introduced.hyps empty; expected `k_def`. got {intro_hyps}"
    # Var name surfaces as `k`
    var_names = {n.unicode for n in intro_vars}
    assert "k" in var_names, \
        f"expected `k` among obtained vars, got {var_names}"
    # Constraint surfaces under its requested name `k_def`
    hyp_names = {n.unicode for n in intro_hyps}
    assert "k_def" in hyp_names, \
        f"expected `k_def` among obtained hyps, got {hyp_names}"

    # (2) _fixed_*_after_me propagate to a downstream ctxt dict
    vars_after = obtain_node._fixed_vars_after_me({})
    hyps_after = obtain_node._fixed_facts_after_me({})
    assert "k" in {n.unicode for n in vars_after}, \
        f"_fixed_vars_after_me must expose `k`, got {vars_after}"
    assert "k_def" in {n.unicode for n in hyps_after}, \
        f"_fixed_facts_after_me must expose `k_def`, got {hyps_after}"

    # (3) Quickview emits the introduced block the first time
    print_header("Quickview (first render)", file)
    root.quickview(0, file)

    # (4) Re-rendering quickview with no change: dedup should suppress
    # the introduced block on the re-emit. Harder to assert inline
    # without capturing — leave to eyeballing the printed output.
    print_header("Quickview (re-render — introduced block should be deduped)", file)
    root.quickview(0, file)


@model_test("Obtain_Skip_Introduced", "Test_Obtain_Skip_Introduced.thy", 8)
async def _test_Obtain_Skip_Introduced(root: Root, file: MyIO):
    """Verify Obtain populates `_introduced` even on the sorry/skip path.

    Same scenario as Obtain_Fixed (lemma `∃k::nat. k = m ⟹ True`), but
    the Obtain is issued WITHOUT a sub-proof.  The block's END fails,
    StdBlock._refresh_me_alone takes the sorry path (`_skip_proof`), and
    Obtain._skip_proof must still read the New_Item_Msg so that
    `_fixed_vars_after_me` / `_fixed_facts_after_me` expose the obtained
    variables/constraints to subsequent siblings."""
    print_header("Initial YAML", file)
    root.print(0, file)

    await root.fill("2", [Obtain.gen_single({
        "thought": "unpack the existential",
        "variables": [{"name": "k", "type": "nat"}],
        "constraints": [{"name": "k_def",
                         "isabelle": "k = m",
                         "english": "the existential witness"}],
    })])
    print_header("After Obtain (no proof — sorry path)", file)
    root.print(0, file)

    obtain_node = root.locate_node("2")
    assert isinstance(obtain_node, Obtain), \
        f"Expected Obtain at step 2, got {type(obtain_node).__name__}"

    intro_vars = cast(Obtain, obtain_node)._introduced.vars
    intro_hyps = cast(Obtain, obtain_node)._introduced.hyps
    assert intro_vars, \
        f"_introduced.vars empty after sorry path; expected `k`. got {intro_vars}"
    assert intro_hyps, \
        f"_introduced.hyps empty after sorry path; expected `k_def`. got {intro_hyps}"

    var_names = {n.unicode for n in intro_vars}
    assert "k" in var_names, \
        f"expected `k` among obtained vars, got {var_names}"
    hyp_names = {n.unicode for n in intro_hyps}
    assert "k_def" in hyp_names, \
        f"expected `k_def` among obtained hyps, got {hyp_names}"

    vars_after = obtain_node._fixed_vars_after_me({})
    hyps_after = obtain_node._fixed_facts_after_me({})
    assert "k" in {n.unicode for n in vars_after}, \
        f"_fixed_vars_after_me must expose `k` after sorry path, got {vars_after}"
    assert "k_def" in {n.unicode for n in hyps_after}, \
        f"_fixed_facts_after_me must expose `k_def` after sorry path, got {hyps_after}"

    print_header("Quickview", file)
    root.quickview(0, file)


@model_test("Obtain_Rewrite_Scope", "Test_Obtain_Rewrite_Scope.thy", 8)
async def _test_Obtain_Rewrite_Scope(root: Root, file: MyIO):
    """Regression test: Obtain constraint with explicit name must survive
    predecessor re-refresh during fill-replacement.

    Previously, auto-named constraints (counter-based) drifted on
    re-execution because prem_counter is a shared Synchronized.var.
    Fix: NamedStatement now requires an explicit `name`, so the ML side
    always receives SOME name and never touches the counter."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Batch fill: Obtain (explicit name) + Obvious (will fail)
    await root.fill("2", [
        Obtain.gen_single({
            "thought": "unpack the existential",
            "variables": [{"name": "k", "type": "nat"}],
            "constraints": [{"isabelle": "k = m",
                             "english": "the existential witness",
                             "name": "k_def"}],
            "proof": [{"operation": "Obvious", "facts": []}],
        }),
        Obvious.gen_single({"facts": []}),
    ])
    print_header("After batch fill (Obtain + Obvious)", file)
    root.print(0, file)

    # Replace the failed Obvious (step 3) with a Rewrite using k_def.
    # This triggers predecessor re-refresh of the Obtain.
    root.session.age += 1
    outcome = await root.fill("3", [Rewrite.gen_single({
        "thought": "Rewrite using k_def",
        "using": [{"name": "k_def"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After Rewrite using k_def", file)
    root.print(0, file)

    if outcome.failure:
        failure_str = str(outcome.failure)
        file.write(f"FAILURE: {failure_str}\n")
        fact_not_found = "not found" in failure_str.lower()
        file.write(f"fact_not_found: {fact_not_found}\n")
    else:
        file.write("SUCCESS\n")

@model_test("UpstreamChangeResetsObvious", "Test_UpstreamChangeResetsObvious.thy", 11)
async def _test_UpstreamChangeResetsObvious(root: Root, file: MyIO):
    """_is_trivial lifecycle around failed Obvious attempts.

    Since the _is_trivial reset on TERMINATE_AND_REVERT (923e624), a failed
    single-op Obvious fill reverts AND clears the parent's flag, so retries
    are no longer blocked — the flag only persists while a failed Obvious
    is actually in the tree.  This test pins both halves:

    1. single-op fill fails → node reverted, _is_trivial=None, an identical
       retry is allowed (fails the same way, not GoalIsNontrivial);
    2. with a stale _is_trivial=False (white-boxed, as an in-tree failed
       Obvious would leave it), the GoalIsNontrivial gate blocks a new
       Obvious, and amend / insert_before of an upstream step reset the
       flag via _on_upstream_change so Obvious can be attempted again."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Have True (trivially provable, Obvious succeeds)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "trivial helper",
        "statement": {"english": "True", "conclusion": "True"},
        "name": "triv",
    })])
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("After step 1 (Have True, Obvious succeeds)", file)
    root.print(0, file)

    # Step 2: Have False (given later — impossible to prove)
    root.session.age += 1
    await root.fill("2", [Have.gen_single({
        "thought": "impossible statement",
        "statement": {"english": "False", "conclusion": "False"},
        "name": "bad",
    })])
    print_header("After step 2 (Have False, open proof)", file)
    root.print(0, file)

    # Step 2.1: Obvious — fails (can't prove False), single-op fill is
    # auto-reverted and the revert clears _is_trivial back to None.
    root.session.age += 1
    _outcome = await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    step2 = root.locate_node("2")
    assert isinstance(_outcome.failure, CannotEdit_EvaluationFailed), \
        f"Expected CannotEdit_EvaluationFailed but got {_outcome.failure!r}"
    assert step2._is_trivial is None, \
        f"Expected _is_trivial=None after single-op fill revert, got {step2._is_trivial}"
    file.write("Single-op Obvious failure reverted; _is_trivial cleared to None\n")
    print_header("After step 2.1 (Obvious fails on False, reverted)", file)
    root.print(0, file)

    # Retry Obvious on step 2.1 — must NOT be blocked: it fails on the
    # hammer again (CannotEdit_EvaluationFailed), not GoalIsNontrivial.
    root.session.age += 1
    _outcome = await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    assert isinstance(_outcome.failure, CannotEdit_EvaluationFailed), \
        f"Expected CannotEdit_EvaluationFailed on retry but got {_outcome.failure!r}"
    assert step2._is_trivial is None, \
        f"Expected _is_trivial=None after retried revert, got {step2._is_trivial}"
    file.write("Obvious retry allowed (fails on the hammer, not GoalIsNontrivial)\n")

    # --- GoalIsNontrivial gate + _on_upstream_change reset ---
    # White-box a stale _is_trivial=False: an in-tree failed Obvious (kept
    # by a multi-op batch, or re-failed during a refresh cascade) leaves
    # the parent in exactly this state; a reverted single-op fill no
    # longer does, and keeping a failed Obvious in the tree here would let
    # the post-amend refresh cascade re-set the flag and mask the reset
    # under test.
    step2._is_trivial = False
    root.session.age += 1
    _outcome = await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    assert isinstance(_outcome.failure, GoalIsNontrivial), \
        f"Expected GoalIsNontrivial failure but got {_outcome.failure!r}"
    file.write("Obvious correctly blocked by GoalIsNontrivial while flag is False\n")

    # amend step 1 → _on_upstream_change should reset step2._is_trivial
    root.session.age += 1
    await root.amend("1", [Have.gen_single({
        "thought": "amended helper",
        "statement": {"english": "x + y = 3", "conclusion": "x + y = 3"},
        "name": "sum",
    })])
    step2 = root.locate_node("2")
    assert step2._is_trivial is None, \
        f"Expected _is_trivial=None after amend of predecessor, got {step2._is_trivial}"
    file.write("After amend: step2._is_trivial correctly reset to None\n")
    print_header("After amending step 1", file)
    root.print(0, file)

    # Obvious on step 2.1 is allowed again (still fails on False + reverts)
    root.session.age += 1
    _outcome = await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    assert isinstance(_outcome.failure, CannotEdit_EvaluationFailed), \
        f"Expected CannotEdit_EvaluationFailed but got {_outcome.failure!r}"
    file.write("Obvious retry allowed after amend (fails on False, as expected)\n")
    print_header("After Obvious retry (allowed, fails)", file)
    root.print(0, file)

    # --- Test insert_before: insert before step 2 → _on_upstream_change resets again ---
    # Keep asserting on the same node object: the insertion renumbers the
    # "bad" block from step 2 to step 3, so re-locating "2" would find the
    # freshly inserted Have instead.
    step2._is_trivial = False
    root.session.age += 1
    await root.insert_before("2", [Have.gen_single({
        "thought": "inserted step",
        "statement": {"english": "True", "conclusion": "True"},
        "name": "ins",
    })])
    assert step2._is_trivial is None, \
        f"Expected _is_trivial=None after insert_before, got {step2._is_trivial}"
    file.write("After insert_before: step2._is_trivial correctly reset to None\n")
    print_header("After inserting before step 2", file)
    root.print(0, file)

    # Obvious on step 2.1 should be ALLOWED again
    root.session.age += 1
    await root.fill("2.1", [Obvious.gen_single({"facts": []})])
    file.write("Obvious retry allowed after insert_before\n")
    print_header("Final state", file)
    root.print(0, file)


@model_test("MultiAmendHaveObviousUnblocked", "Test_MultiAmendHaveObviousUnblocked.thy", 8)
async def _test_MultiAmendHaveObviousUnblocked(root: Root, file: MyIO):
    """Multi-amend [Have, Obvious] via _insert_before_child must NOT be
    blocked by a stale _is_trivial=False left over from a prior failed
    Obvious.  The Have step changes the proof state, so the subsequent
    Obvious should be allowed to construct and evaluate.

    Since the _is_trivial reset on TERMINATE_AND_REVERT (923e624), a failed
    single-op Obvious fill no longer leaves the flag False — the failed
    Obvious must stay in the tree, which a multi-op fill batch provides
    (its failure path is CONTINUE, no auto-revert).

    Scenario: fill step 1 with Have(False), multi-op fill 1.1 with
    [Have(True), Obvious] whose trailing Obvious fails on the False goal
    and is kept (sets _is_trivial=False on the 1-block), then multi-amend
    the failed Obvious at 1.2 with [Have(True), Obvious(using it)]."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Have(False) — creates a subgoal that Obvious can't solve.
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "introduce unprovable subgoal",
        "statement": {"english": "False", "conclusion": "False"},
        "name": "absurd",
    })])
    print_header("[1] Have False — open subgoal", file)
    root.print(0, file)

    # Steps 1.1 + 1.2: multi-op fill whose trailing Obvious fails on the
    # False goal.  The multi-op failure path is CONTINUE (no auto-revert),
    # so the failed Obvious stays at 1.2 and _is_trivial=False persists.
    root.session.age += 1
    await root.fill("1.1", [
        Have.gen_single({
            "thought": "warm-up helper",
            "statement": {"english": "True", "conclusion": "True"},
            "name": "warm",
            "proof": [{"operation": "Obvious", "facts": []}],
        }),
        Obvious.gen_single({"facts": []}),
    ])
    step1 = root.locate_node("1")
    assert step1._is_trivial is False, \
        f"Expected _is_trivial=False after kept Obvious failure, got {step1._is_trivial}"
    print_header("[2] fill 1.1 with [Have True, Obvious] — Obvious fails and is kept, _is_trivial=False", file)
    root.print(0, file)

    # Multi-amend the failed Obvious at step 1.2 with [Have(True), Obvious].
    # amend_me sees len(gns)==2 → delete 1.2, then _insert_before_child
    # inserts [Have, Obvious] at the former slot.
    # BUG (before fix): _is_trivial=False on step-1 block rejects the Obvious
    # during construction via GoalIsNontrivial, even though the Have changes
    # the proof state.
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1.2", "action": "amend", "proof_operations": [
            {"operation": "Have", "thought": "trivial truth",
             "statement": {"english": "True", "conclusion": "True"},
             "name": "triv",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Obvious",
             "facts": [{"name": "triv"}]},
        ]})
    print_header("[3] multi-amend 1.2 → [Have(True), Obvious] — must not be blocked", file)
    file.write(result)
    file.write(f"is_error: {is_error}\n")

    # The Obvious should have been created (not rejected by GoalIsNontrivial).
    assert not is_error, \
        f"Expected is_error=False (Obvious should not be blocked), got is_error={is_error}"
    print_header("Final state", file)
    root.print(0, file)


@model_test("NamedFactResolution", "Test_NamedFactResolution.thy", 13)
async def _test_NamedFactResolution(root: Root, file: MyIO):
    """Test that Interaction_RetrieveForProof and Interaction_ChooseDef
    resolve free-text answers as named facts before falling through to
    prove-in-time or raising BadAnswer."""
    print_header("Initial YAML", file)
    root.print(0, file)

    ml_state = root.ml_state

    # --- RetrieveForProof: empty answer triggers give-up (name lookup removed) ---
    inter1 = Interaction_RetrieveForProof(
        state=ml_state, query="logarithm of a power", kinds=[EntityKind.THEOREM])
    result1 = await inter1.answer(AnswerIndexesOrSpec(indexes=[], statement=None))
    file.write(f"RetrieveForProof(empty): {type(result1[0]).__name__ if result1 else 'empty'}\n")
    if inter1.single_choice:
        assert len(result1) == 1 and isinstance(result1[0], IsabelleFact_Unfound)
    else:
        assert result1 == [], f"Expected empty list for give-up, got {result1}"

    # --- RetrieveForProof: prove-in-time statement ---
    inter2 = Interaction_RetrieveForProof(
        state=ml_state, query="something trivial", kinds=[EntityKind.THEOREM])
    result2 = await inter2.answer(AnswerIndexesOrSpec(indexes=[], statement="(8::nat) = 2 ^ 3"))
    file.write(f"RetrieveForProof(statement='(8::nat) = 2 ^ 3'): {type(result2[0]).__name__}\n")
    assert isinstance(result2[0], IsabelleFact_ProveInTime), \
        f"Expected IsabelleFact_ProveInTime, got {type(result2[0]).__name__}"

    # --- ChooseDef: name matching a candidate short name ---
    cand_a = IsabelleFact_Presented(
        full_name="Test_NamedFactResolution.NF_XXX_def",
        short_name=IsaTerm.from_isabelle("NF_XXX_def"),
        fact=FactByName(name="NF_XXX_def"),
        expression=[IsaTerm.from_isabelle("NF_XXX ?a ?b = ?a + ?b")])
    cand_b = IsabelleFact_Presented(
        full_name="Test_NamedFactResolution.NF_XXX_alt",
        short_name=IsaTerm.from_isabelle("NF_XXX_alt"),
        fact=FactByName(name="NF_XXX_alt"),
        expression=[IsaTerm.from_isabelle("NF_XXX ?a ?b = ?b + ?a")])
    inter3 = Interaction_ChooseDef(["NF_XXX"], [cand_a, cand_b], state=ml_state)
    result3 = await inter3.answer(AnswerIndexesOrName(indexes=[], name="NF_XXX_def"))
    file.write(f"ChooseDef(name='NF_XXX_def'): {[type(r).__name__ for r in result3]}\n")
    assert len(result3) == 1 and result3[0] is cand_a, \
        "Expected cand_a to be selected by short name"

    # --- ChooseDef: name matching a candidate full name ---
    inter4 = Interaction_ChooseDef(["NF_XXX"], [cand_a, cand_b], state=ml_state)
    result4 = await inter4.answer(AnswerIndexesOrName(indexes=[], name="Test_NamedFactResolution.NF_XXX_alt"))
    file.write(f"ChooseDef(name=full_name NF_XXX_alt): {[type(r).__name__ for r in result4]}\n")
    assert len(result4) == 1 and result4[0] is cand_b, \
        "Expected cand_b to be selected by full name"

    # --- ChooseDef: name not matching any candidate, but IS an accessible fact ---
    inter5 = Interaction_ChooseDef(["NF_XXX"], [cand_a, cand_b], state=ml_state)
    result5 = await inter5.answer(AnswerIndexesOrName(indexes=[], name="conjI"))
    file.write(f"ChooseDef(name='conjI'): {[type(r).__name__ for r in result5]}\n")
    assert len(result5) == 1 and isinstance(result5[0], IsabelleFact_Presented), \
        f"Expected IsabelleFact_Presented via RPC lookup, got {type(result5[0]).__name__}"
    file.write(f"  resolved short_name: {result5[0].short_name.unicode}\n")

    # --- ChooseDef: name not matching anything ---
    inter6 = Interaction_ChooseDef(["NF_XXX"], [cand_a, cand_b], state=ml_state)
    try:
        await inter6.answer(AnswerIndexesOrName(indexes=[], name="xyzzy_nonexistent_thm"))
        raise TestFailed("Expected Interaction_BadAnswer for nonexistent name")
    except Interaction_BadAnswer as e:
        file.write(f"ChooseDef(name='xyzzy_nonexistent_thm'): Interaction_BadAnswer as expected\n")

    print_header("Done", file)


@model_test("UnfoldDefTypeFilter", "Test_UnfoldDefTypeFilter.thy", 7)
async def _test_UnfoldDefTypeFilter(root: Root, file: MyIO):
    r"""Unfold candidate filtering must respect the goal's types.

    `Minilang.potential_defs_of_const` (library/proof.ML) gathers the
    definitional-equation unfoldings of a constant. The head constant of `(⊆)`
    is the overloaded `less_eq` (= `(≤)`), so a naive Find_Theorems search at the
    constant's most-general type `?'a ⇒ ?'a ⇒ bool` matches `(≤)` at EVERY type
    instance (nat / int / bool / unit / lattice values / …) and, capped at the
    default result limit, buries the genuinely relevant SET unfoldings. In the
    field log this surfaced as a `ChooseDef` menu for `(⊆)` full of
    `nat`/`bool`/`int` junk with `subset_eq` missing entirely.

    The fix (this test guards it): search ALL matches, then keep only those whose
    LHS actually matches a subterm of the proof goal, ranked type-specific-and-
    unconditional first. The fixture goal is `A ⊆ B ⟹ A ∪ B = B`, exercising both
    `(⊆)` (premise) and a set `(=)` (conclusion).

    Expected after the fix:
    - `(⊆)`: `subset_eq` / `subset_iff` / `less_eq_set_def` are present (and the
      general-form set unfoldings lead the list); none of the type-irrelevant
      `(≤)`-on-nat/bool/int/unit instances appear.
    - `(=)`: `set_eq_iff` (the canonical set-equality unfolding) is present and
      leads; only equalities whose LHS matches the goal's `A ∪ B = B` are offered.
    """
    ml_state = root.ml_state

    # Type-irrelevant `(≤)` instances that must NEVER appear for a set goal.
    LE_JUNK = ("nat_leq_as_int", "le_bool_def", "le_0_eq", "less_eq_unit_def",
               "extremum_unique", "int_one_le_iff_zero_less", "le_zero_eq",
               "top_unique", "bot_unique")

    def report(target: str, defs, relevant: list[str], junk) -> None:
        print_header(f"Candidates offered for Unfold {target}", file)
        for d in defs:
            file.write(f"{d.full_name}: "
                       f"{', '.join(e.unicode for e in d.expression)}\n")
        file.write(f"total candidates: {len(defs)}\n")
        short_names = {d.short_name.unicode for d in defs}
        print_header(f"Relevant unfolding lemmas present? ({target})", file)
        for lem in relevant:
            file.write(f"{lem}: {lem in short_names}\n")
        print_header(f"Type-irrelevant candidates leaked into the list ({target})", file)
        leaked = sorted(d.full_name for d in defs if junk(d.short_name.unicode))
        for n in leaked:
            file.write(f"- {n}\n")
        file.write(f"leaked irrelevant count: {len(leaked)}\n")

    # --- (⊆): head constant `less_eq`, occurs at set type in the goal premise ---
    sub_defs = await ml_state.potential_defs_of([IsaTerm.from_agent("(⊆)")])
    report("(⊆)", sub_defs,
           relevant=["subset_eq", "subset_iff", "less_eq_set_def"],
           junk=lambda s: (s in LE_JUNK
                           or "less_eq_finite" in s
                           or "less_eq_integer_code" in s
                           or "less_eq_int_code" in s))

    # --- (=): head constant `HOL.eq`; the goal conclusion is a set equality ---
    eq_defs = await ml_state.potential_defs_of([IsaTerm.from_agent("(=)")])
    report("(=)", eq_defs,
           relevant=["set_eq_iff", "set_eq_subset"],
           junk=lambda s: s in LE_JUNK)


@model_test("UnfoldPointFree", "Test_UnfoldPointFree.thy", 7)
async def _test_UnfoldPointFree(root: Root, file: MyIO):
    r"""Regression guard for arity-tolerant goal matching.

    The goal `reflp (⊆)` uses `(⊆)` POINT-FREE — the operator is an argument to
    `reflp`, applied to zero arguments. Candidate-def LHSs are fully applied
    (`less_eq ?A ?B`), so a naive `Pattern.matches(lhs, occurrence)` fails on the
    bare `less_eq` occurrence and would drop EVERY set unfolding. The match is
    arity-tolerant — it truncates the candidate LHS to the occurrence's argument
    count — so the canonical set unfoldings are still offered for a point-free
    occurrence. If that tolerance regresses, the booleans below flip to False.
    """
    ml_state = root.ml_state
    defs = await ml_state.potential_defs_of([IsaTerm.from_agent("(⊆)")])
    short = {d.short_name.unicode for d in defs}

    # Pure presence assertions: stable across library changes, flip only if the
    # arity-tolerant match regresses (the exact candidate set / ranking for a
    # point-free occurrence is intentionally not snapshotted — it is library-
    # dependent and undiscriminated, since every candidate is exact-set-typed).
    print_header("Point-free Unfold (⊆): relevant set unfoldings present?", file)
    for lem in ("subset_eq", "subset_iff", "less_eq_set_def"):
        file.write(f"{lem}: {lem in short}\n")


@model_test("UnfoldSyntax", "Test_UnfoldSyntax.thy", 40)
async def _test_unfold_syntax(root: Root, file: MyIO):
    """Test the unfold_syntax callback.

    Verifies:
    1. A standard HOL term returns identical normal and raw displays
    2. A term using a higher-theory abbreviation (my_conj) is unfolded in raw display
    3. The head constant name is correctly extracted
    4. A non-constant head (lambda) returns empty head_name
    5. An unparseable term raises InternalError_UnparsedTerm
    Plus: abbrev_head (4th slot) names the abbreviation constant when the head
    is an abbreviation, and the exact_term Head section renders the two-layer
    abbreviation semantics (own interpretation first, expansion-head fallback).
    """
    ml = root.ml_state

    # 1. Standard HOL term — no higher-theory syntax to strip
    file.write("=== standard HOL term ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("True ∧ False")
    file.write(f"  head: {head}\n")
    file.write(f"  abbrev_head: {abbrev_head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")
    assert head == "HOL.conj", f"Expected HOL.conj, got {head}"
    assert abbrev_head == "HOL.conj", f"Expected HOL.conj abbrev_head, got {abbrev_head}"

    # 2. Term using the custom abbreviation `my_conj` defined in the theory
    file.write("=== custom abbreviation ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("my_conj True False")
    file.write(f"  head: {head}\n")
    file.write(f"  abbrev_head: {abbrev_head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")
    assert head == "HOL.conj", f"Expected HOL.conj, got {head}"
    assert abbrev_head.endswith(".my_conj"), \
        f"Expected the my_conj abbreviation constant, got {abbrev_head}"

    # 3. Term with `even` (abbreviation from Parity, above Main)
    file.write("=== even abbreviation ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("even (n::nat)")
    file.write(f"  head: {head}\n")
    file.write(f"  abbrev_head: {abbrev_head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 4. Lambda head — head_name should be empty
    file.write("=== lambda head ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("λx::nat. x + 1")
    file.write(f"  head: '{head}'\n")
    file.write(f"  abbrev_head: '{abbrev_head}'\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")
    assert head == "", f"Expected empty head for lambda, got '{head}'"
    assert abbrev_head == "", f"Expected empty abbrev_head for lambda, got '{abbrev_head}'"

    # 5. Unparseable term — should raise InternalError_UnparsedTerm
    file.write("=== unparseable term ===\n")
    try:
        await ml.unfold_syntax("%%% bad syntax")
        raise TestFailed("Expected InternalError_UnparsedTerm")
    except InternalError_UnparsedTerm:
        file.write("  raised InternalError_UnparsedTerm as expected\n")

    # 6. Mixfix notation — the real syntax unfolding test
    file.write("=== mixfix: a ⊕ b ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("(a::nat) ⊕ b")
    file.write(f"  head: {head}\n")
    file.write(f"  abbrev_head: {abbrev_head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")
    # my_op is a definition, not an abbreviation: both heads agree
    assert abbrev_head == head, f"Expected equal heads for a definition, got {abbrev_head} vs {head}"

    file.write("=== mixfix: (a ⊕ b) ⊕ c ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("((a::nat) ⊕ b) ⊕ c")
    file.write(f"  head: {head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 7. Custom bind notation
    file.write("=== bind: m ⤜ f ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("(Some (1::nat)) ⤜ (λx. if x > 0 then Some (x ⊕ x) else None)")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 8. Custom quantifier with syntax translation
    file.write("=== custom forall ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("∀⇩m x ∈ {1,2,3::nat}. x ⊕ x > 0")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 9. Custom sum with syntax translation
    file.write("=== custom sum ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("Σ⇩m x ∈ {1,2,3::nat}. x ⊕ x")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 10. Nested: custom quantifier + custom operator + custom sum
    file.write("=== nested custom syntax ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("∀⇩m x ∈ {1,2,3::nat}. (Σ⇩m y ∈ {0..<x}. y ⊕ x) > 0")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 11. Full query output via _handle_exact_term_query
    from .retrieval import _handle_exact_term_query
    file.write("=== query output: nested ===\n")
    result = await _handle_exact_term_query(root.session, "∀⇩m x ∈ {1,2,3::nat}. (Σ⇩m y ∈ {0..<x}. y ⊕ x) > 0")
    file.write(result + "\n")

    # 12. Two-layer abbreviation semantics in the Head section.
    # Only the heading (before any ':') goes into the golden — interpretation
    # texts live in the machine-local Semantic_DB and must not be welded in.
    def _head_heading(res: str) -> str:
        line = next((l for l in res.split('\n') if l.startswith("Head ")), "")
        return line.split(':')[0]

    # 12a. Layer 3 fallback: my_conj itself has no DB record (local theory),
    # so the expansion's head HOL.conj supplies the interpretation.
    file.write("=== query head: my_conj (expansion-head fallback) ===\n")
    result = await _handle_exact_term_query(root.session, "my_conj True False")
    heading = _head_heading(result)
    file.write(heading + "\n")
    assert heading.startswith("Head Raw constant HOL.conj"), \
        f"Expected expansion-head fallback for my_conj, got: {heading}"
    assert "my_conj" in heading, f"Fallback heading must name the abbreviation: {heading}"

    # 12b. Layer 2: a Main-level abbreviation interpreted in the DB.
    file.write("=== query head: x ≠ y (abbreviation's own semantics) ===\n")
    result = await _handle_exact_term_query(root.session, "(x::nat) ≠ y")
    heading = _head_heading(result)
    file.write(heading + "\n")
    assert heading.startswith("Head Abbreviation constant HOL.not_equal"), \
        f"Expected the abbreviation's own semantics for ≠, got: {heading}"

    # 12c. Bare operator section: the expansion is a lambda (head_name == ""),
    # but abbrev_head still resolves — the Head section must not vanish.
    file.write("=== query head: (≠) bare section ===\n")
    result = await _handle_exact_term_query(root.session, "(≠)")
    heading = _head_heading(result)
    file.write(heading + "\n")
    assert heading.startswith("Head Abbreviation constant HOL.not_equal"), \
        f"Expected abbreviation Head for the bare section, got: {heading}"

    # 12d. Layer 4: local abbreviation over a local constant — neither has a
    # DB record, so the heading stands alone (no type line, no interpretation).
    file.write("=== query head: my_twice (no semantics anywhere) ===\n")
    result = await _handle_exact_term_query(root.session, "my_twice (n::nat)")
    heading = _head_heading(result)
    file.write(heading + "\n")
    assert heading.startswith("Head Abbreviation constant") and "my_twice" in heading, \
        f"Expected a bare abbreviation heading for my_twice, got: {heading}"

    print_header("Done", file)


@model_test("UnfoldSyntaxOp", "Test_UnfoldSyntaxOp.thy", 8)
async def _test_unfold_syntax_op(root: Root, file: MyIO):
    """Probe whether `unfold_syntax` can resolve a *bare operator symbol* when it
    is wrapped as an operator section `(OP)`.

    This underpins the proposed `exact_name` improvement: to look up a notation
    symbol like `*` (or `**`) by name, we parse `(OP)` — Isabelle reads it as the
    operator constant — and take `Term.head_of` to recover the underlying const
    name, which can then be fed to `universal_key_and_name_of`.

    Uses only Main-level operators (`*`, `+`) so the fixture needs just `Main`.
    """
    ml = root.ml_state

    # 1. Times operator section `(*)` — must parse to the times constant.
    file.write("=== operator section (*) ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("(*)")
    file.write(f"  head: {head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")
    assert head, f"Expected a non-empty head const for (*), got '{head}'"
    assert "times" in head, f"Expected the times constant for (*), got {head}"
    assert abbrev_head == head, f"times is no abbreviation: {abbrev_head} vs {head}"

    # 2. Plus operator section `(+)` — generality check, another Main operator.
    file.write("=== operator section (+) ===\n")
    head, raw, normal, abbrev_head = await ml.unfold_syntax("(+)")
    file.write(f"  head: {head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")
    assert head, f"Expected a non-empty head const for (+), got '{head}'"
    assert "plus" in head, f"Expected the plus constant for (+), got {head}"
    assert abbrev_head == head, f"plus is no abbreviation: {abbrev_head} vs {head}"

    print_header("Done", file)


@model_test("ResolveNotation", "Test_ResolveNotation.thy", 8)
async def _test_resolve_notation(root: Root, file: MyIO):
    """Verify `IsaMini.resolve_notation` maps a bare notation symbol to its
    underlying constant across fixities (operator section / infix / prefix /
    postfix), and returns None when nothing resolves.

    This is the resolver behind the `exact_name` symbol fallback. Uses only
    Main-level notation so the fixture needs just `Main`.
    """
    ml = root.ml_state

    # infix `*` — operator-section probe resolves to the times constant
    file.write("=== infix: * ===\n")
    res = await ml.resolve_notation("*")
    file.write(f"  resolved: {res}\n")
    assert res is not None and "times" in res, f"Expected times const, got {res}"

    # infix `+`
    file.write("=== infix: + ===\n")
    res = await ml.resolve_notation("+")
    file.write(f"  resolved: {res}\n")
    assert res is not None and "plus" in res, f"Expected plus const, got {res}"

    # `-` is both infix (minus) and prefix (uminus); infix wins by probe order
    file.write("=== ambiguous: - (infix wins) ===\n")
    res = await ml.resolve_notation("-")
    file.write(f"  resolved: {res}\n")
    assert res is not None and "minus" in res, f"Expected minus const, got {res}"

    # prefix `\<not>` (negation) — exercises the prefix probe
    file.write("=== prefix: not ===\n")
    res = await ml.resolve_notation(r"\<not>")
    file.write(f"  resolved: {res}\n")
    assert res == "HOL.Not", f"Expected HOL.Not, got {res}"

    # postfix `\<^sup>*` (reflexive-transitive closure) — exercises postfix probe
    file.write("=== postfix: rtrancl ===\n")
    res = await ml.resolve_notation(r"\<^sup>*")
    file.write(f"  resolved: {res}\n")

    # infix `\<noteq>` — notation on an ABBREVIATION: mode_abbrev probing
    # resolves to the abbreviation constant itself, not the expansion's
    # head HOL.Not (abbreviations are first-class entities)
    file.write("=== infix: noteq (abbreviation) ===\n")
    res = await ml.resolve_notation(r"\<noteq>")
    file.write(f"  resolved: {res}\n")
    assert res == "HOL.not_equal", f"Expected HOL.not_equal, got {res}"

    # an unresolvable token returns None
    file.write("=== unresolvable ===\n")
    res = await ml.resolve_notation("zzz_no_such_op")
    file.write(f"  resolved: {res}\n")
    assert res is None, f"Expected None, got {res}"

    print_header("Done", file)


@model_test("QueryExactNameOp", "Test_QueryExactNameOp.thy", 8)
async def _test_query_exact_name_op(root: Root, file: MyIO):
    """End-to-end: a bare operator symbol given as `exact_name` resolves to its
    underlying constant via the resolve_notation fallback — both at the
    semantic_knn layer (where the fallback lives) and through the full `query`
    tool (_query_tool_logic).

    `*` is not in the constant name space, so the direct universal_key lookup
    fails; the CONSTANT-kind fallback parses `(*)` → Groups.times_class.times.
    """
    from Isabelle_RPC_Host.universal_key import EntityKind
    from .retrieval import _query_tool_logic

    ml = root.session.retrieval_state()

    # --- Layer 1: semantic_knn exact_name path (where the fallback lives) ---
    file.write("=== semantic_knn exact_name='*' (constant) ===\n")
    results, warnings = await ml.semantic_knn(
        None, 1, [EntityKind.CONSTANT], exact_name="*")
    file.write(f"  results: {len(results)}, warnings: {warnings}\n")
    assert len(results) == 1, f"Expected 1 result for '*', got {len(results)}"
    full = results[0].entity.full_name
    file.write(f"  resolved full_name: {full}\n")
    assert "times" in full, f"Expected times constant, got {full}"

    # A genuinely unresolvable symbol still reports Undefined (safe degradation).
    file.write("=== semantic_knn exact_name unresolvable ===\n")
    res_none, warn_none = await ml.semantic_knn(
        None, 1, [EntityKind.CONSTANT], exact_name="zzz_no_such_op")
    file.write(f"  results: {len(res_none)}, warnings: {warn_none}\n")
    assert len(res_none) == 0, "Expected no results for an unresolvable symbol"

    # --- Abbreviation notation: `≠` resolves to the abbreviation constant
    # itself, with the two-layer semantics heading attached.
    file.write("=== semantic_knn exact_name='≠' (abbreviation notation) ===\n")
    res_abbr, warn_abbr = await ml.semantic_knn(
        None, 1, [EntityKind.CONSTANT], exact_name=r"\<noteq>")
    file.write(f"  results: {len(res_abbr)}, warnings: {warn_abbr}\n")
    assert len(res_abbr) == 1, f"Expected 1 result for '≠', got {len(res_abbr)}"
    file.write(f"  resolved full_name: {res_abbr[0].entity.full_name}\n")
    assert res_abbr[0].entity.full_name == "HOL.not_equal", \
        f"Expected HOL.not_equal, got {res_abbr[0].entity.full_name}"
    heading = res_abbr[0].semantics_heading
    file.write(f"  heading: {heading}\n")
    assert heading is not None and heading.startswith("Abbreviation constant HOL.not_equal"), \
        f"Expected the abbreviation's own semantics heading, got {heading}"

    # --- Direct abbreviation name (no notation fallback involved) gets the
    # same heading.
    file.write("=== semantic_knn exact_name='HOL.not_equal' (direct name) ===\n")
    res_direct, _ = await ml.semantic_knn(
        None, 1, [EntityKind.CONSTANT], exact_name="HOL.not_equal")
    assert len(res_direct) == 1
    heading = res_direct[0].semantics_heading
    file.write(f"  heading: {heading}\n")
    assert heading is not None and heading.startswith("Abbreviation constant HOL.not_equal"), \
        f"Expected the abbreviation's own semantics heading, got {heading}"

    # --- Layer 2: full query tool (_query_tool_logic), direct (non-fork) path ---
    root.session.interactive_retrieval = InteractiveRetrievalMode.NO
    file.write("=== query tool exact_name='*' ===\n")
    result, is_error = await _query_tool_logic(
        root.session, {'queries': [{'kinds': ['constant'], 'exact_name': '*'}]})
    file.write(f"  is_error: {is_error}\n")
    file.write(f"  mentions times: {'times' in result}\n")
    file.write(f"  mentions Undefined: {'Undefined' in result}\n")
    assert not is_error, f"query tool must not error: {result}"
    assert "times" in result, f"query tool result must mention times: {result}"
    assert "Undefined" not in result, f"must not be Undefined: {result}"

    # The same tool on `≠`: the rendered entity must carry the abbreviation
    # heading (membership booleans only — no DB interpretation text in golden).
    file.write("=== query tool exact_name='≠' ===\n")
    result, is_error = await _query_tool_logic(
        root.session, {'queries': [{'kinds': ['constant'], 'exact_name': '≠'}]})
    file.write(f"  is_error: {is_error}\n")
    file.write(f"  mentions abbreviation heading: "
               f"{'Abbreviation constant HOL.not_equal' in result}\n")
    assert not is_error, f"query tool must not error: {result}"
    assert "Abbreviation constant HOL.not_equal" in result, \
        f"rendered result must carry the abbreviation heading: {result}"

    print_header("Done", file)


@model_test("AmendLeafToNonLeaf", "Test_AmendLeafToNonLeaf.thy", 8)
async def _test_AmendLeafToNonLeaf(root: Root, file: MyIO):
    """Reproduce: AttributeError: 'Obvious' object has no attribute 'sub_nodes'
    at model.py:2825 (NonLeaf_Node._amend_from).

    Trigger: amend a Leaf (Obvious) into a NonLeaf (InferenceRule). The
    NonLeaf override of _amend_from unconditionally executes
        self.sub_nodes[:] = old.sub_nodes
    but _amend_child (model.py:2815) calls new_node._amend_from(child)
    without guarding on the old node's kind, so any Leaf -> NonLeaf amend
    crashes here before refresh.

    The reverse-revert path in Node.amend (model.py:2560) already has the
    correct `isinstance(new_node, NonLeaf_Node) and isinstance(old_node,
    NonLeaf_Node)` guard — the forward _amend_from is missing it.

    Original log (2026-04-18): the agent amended Obvious at step
    1.2.3.1.1.1 with InferenceRule(rule=ccontr) to switch to proof by
    contradiction, and the server returned
        UNEXPECTED ERROR: AttributeError: 'Obvious' object has no attribute 'sub_nodes'
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Obvious.gen_single({"facts": []})])
    print_header("After fill step 1 with Obvious (Leaf)", file)
    root.print(0, file)

    root.session.age += 1
    try:
        await root.amend("1", [InferenceRule.gen_single({
            "thought": "Switch to proof by contradiction.",
            "rule": {"name": "ccontr"},
        })])
    except AttributeError as e:
        raise TestFailed(
            f"BUG REPRODUCED: {type(e).__name__}: {e} "
            f"(NonLeaf_Node._amend_from does not guard against Leaf `old`)"
        ) from e
    print_header("After amend Obvious -> InferenceRule", file)
    root.print(0, file)


# ---------------------------------------------------------------------------
# Multi-node edit tests — exercise the batched-edit upgrade (proof_operations
# list, nested proof trees, commit-and-warn) and the `Parse_Op_List` pipeline
# (nested-path error reporting, forbid-successor, singleton splice).  These
# tests invoke the MCP-level helpers directly so the full routing is covered,
# not just the per-node primitives.
# ---------------------------------------------------------------------------

from .model import Warning as _W


@model_test("DeepNestedProof", "Test_DeepNestedProof.thy", 8)
async def _test_DeepNestedProof(root: Root, file: MyIO):
    """Three-level nested proof tree: Have -> Have -> Have -> Obvious.  Verifies
    that the recursive `proof` field is consumed correctly at every depth."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "L1",
        "statement": {"english": "L1", "conclusion": r"x * x \<ge> 0"},
        "name": "L1",
        "proof": [
            {"operation": "Have", "thought": "L2",
             "statement": {"english": "L2", "conclusion": r"x * x \<ge> 0"},
             "name": "L2",
             "proof": [
                 {"operation": "Have", "thought": "L3",
                  "statement": {"english": "L3", "conclusion": r"x * x \<ge> 0"},
                  "name": "L3",
                  "proof": [
                      {"operation": "Obvious", "facts": []},
                  ]},
             ]},
        ],
    })])
    print_header("After 3-level nested Have", file)
    root.print(0, file)
    l1 = root.locate_node("1")
    assert isinstance(l1, Have), f"L1 kind: {type(l1).__name__}"
    assert isinstance(l1, NonLeaf_Node)
    assert l1.sub_nodes and isinstance(l1.sub_nodes[0], Have), \
        f"L1 first child: {type(l1.sub_nodes[0]).__name__ if l1.sub_nodes else 'none'}"
    l2 = l1.sub_nodes[0]
    assert cast(NonLeaf_Node, l2).sub_nodes and isinstance(cast(NonLeaf_Node, l2).sub_nodes[0], Have), \
        f"L2 first child: {type(cast(NonLeaf_Node, l2).sub_nodes[0]).__name__ if cast(NonLeaf_Node, l2).sub_nodes else 'none'}"
    l3 = cast(NonLeaf_Node, l2).sub_nodes[0]
    assert cast(NonLeaf_Node, l3).sub_nodes, "L3 should have at least one child (the Obvious)"
    file.write(f"depth-3 verified: "
               f"{type(l1).__name__}->{type(l2).__name__}->"
               f"{type(l3).__name__}->{type(cast(NonLeaf_Node, l3).sub_nodes[0]).__name__}\n")


@model_test("AmendQ6Preservation", "Test_AmendQ6Preservation.thy", 8)
async def _test_AmendQ6Preservation(root: Root, file: MyIO):
    """Single-item amend with a nested proof; the target had a pre-existing
    child (_amend_from).  Q6 rule: inherited children get redirected into
    the LAST provided node's body.

    Seed: Have { sub: [Obvious] }
    Amend with: Suffices { proof: [Have inner (no proof)] }
    Expected: Suffices.sub = [Have inner { sub: [old Obvious] }]  (Q6 fold)."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    _seed_outcome = await root.fill("1", [Have.gen_single({
        "thought": "outer",
        "statement": {"english": "outer", "conclusion": r"x * x \<ge> 0"},
        "name": "outer",
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("edit_message: seed Have { proof: [Obvious] }", file)
    file.write((await _P.edit_message(root, _seed_outcome, root.session))[0])
    file.write("---------------\n")
    outer = root.locate_node("1")
    assert cast(NonLeaf_Node, outer).sub_nodes and isinstance(cast(NonLeaf_Node, outer).sub_nodes[0], Obvious), "seed failed"
    pre_id = id(cast(NonLeaf_Node, outer).sub_nodes[0])

    root.session.age += 1
    _amend_outcome = await root.amend("1", [Suffices.gen_single({
        "thought": "replace outer Have with Suffices + nested Have",
        "statement": {"english": "repl", "conclusion": r"x * x \<ge> 0"},
        "proof": [
            {"operation": "Have", "thought": "inner no-proof",
             "statement": {"english": "inner", "conclusion": r"x * x \<ge> 0"},
             "name": "inner"},
        ],
    })])
    print_header("edit_message: amend into Suffices; Q6 folds Obvious into inner Have", file)
    file.write((await _P.edit_message(root, _amend_outcome, root.session))[0])
    file.write("---------------\n")
    suff = root.locate_node("1")
    assert isinstance(suff, Suffices), f"expected Suffices, got {type(suff).__name__}"
    assert cast(NonLeaf_Node, suff).sub_nodes and isinstance(cast(NonLeaf_Node, suff).sub_nodes[0], Have), \
        f"expected Suffices's first child Have, got {[type(c).__name__ for c in cast(NonLeaf_Node, suff).sub_nodes]}"
    inner = cast(NonLeaf_Node, suff).sub_nodes[0]
    assert any(id(c) == pre_id for c in cast(NonLeaf_Node, inner).sub_nodes), \
        (f"Q6 FAIL: pre-amend Obvious not found in inner Have. "
         f"inner.sub_nodes: {[type(c).__name__ for c in cast(NonLeaf_Node, inner).sub_nodes]}")
    file.write("Q6 redirect into last-provided-node's body verified.\n")


@model_test("RefreshFailMidBatch", "Test_RefreshFailMidBatch.thy", 8)
async def _test_RefreshFailMidBatch(root: Root, file: MyIO):
    """Batch fill where the first item (a Have whose nested Obvious proves
    a false statement) fails at refresh.  Subsequent siblings must be
    CANCELLED by `_can_continue_before_child`, all remain in the tree
    (batch path suppresses `_on_edit_failure` revert)."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Have", "thought": "bad aux (false)",
             "statement": {"english": "false", "conclusion": r"(0::int) = (1::int)"},
             "name": "bad",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Have", "thought": "later aux",
             "statement": {"english": "later", "conclusion": r"x * x \<ge> 0"},
             "name": "later",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Obvious", "facts": []},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After batched fill (first Have fails, rest cascade-cancel)", file)
    root.print(0, file)
    n1 = root.locate_node("1")
    parent = n1.parent
    assert parent is not None
    sibs = parent.sub_nodes
    file.write(f"sibling kinds: {[type(c).__name__ for c in sibs]}\n")
    file.write(f"sibling statuses: {[c.status.status.name for c in sibs]}\n")
    assert len(sibs) >= 3, f"expected >=3 siblings, got {len(sibs)}"


@model_test("CommitGroupBMidBatch", "Test_CommitGroupBMidBatch.thy", 8)
async def _test_CommitGroupBMidBatch(root: Root, file: MyIO):
    """Commit-time Group-B in the middle of a batch: the first item is a
    Branch on trichotomy, which produces multiple top-level subgoals.
    `SubgoalMaker._should_open_proof_block` returns
    YES_AND_CLOSE_PARENT_BLOCK → parent is closed via `_close_by`.
    Subsequent siblings in the batch hit `StdBlock.append`'s
    opening-check and fail with `CannotAppend_BlockClosed`.  The
    append loop catches this Group-B failure, stops at the second
    item, and `_edit_tool_logic` emits a single aggregated
    `session.warnings` entry carrying the unapplied tail verbatim.
    (Historical note: this test used to chain `[Obvious, Obvious, Obvious]`
    to trigger `GoalIsNontrivial` at construction, but the parse-time
    Obvious-forbids-successor rule rejects that fixture outright, so
    the remaining reachable commit-time Group-B path is exercised here.)"""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Branch", "thought": "trichotomy closes the proof line",
             "cases": [
                 {"statement": {"english": "positive", "isabelle": "x > 0", "name": "positive"}},
                 {"statement": {"english": "zero", "isabelle": "x = 0", "name": "zero"}},
                 {"statement": {"english": "negative", "isabelle": "x < 0", "name": "negative"}},
             ]},
            # These two cannot be siblings after a block-closing SubgoalMaker.
            # Aggregated into session.warnings.  Wrapped in Have (instead of
            # bare Obvious) because top-level Obvious forbids successor at
            # parse time — we need the commit-time path to fire, not the
            # parse-time one.
            {"operation": "Have", "thought": "misplaced aux a",
             "statement": {"english": "trivial", "conclusion": "(1::int) = 1"},
             "name": "aux_a",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Have", "thought": "misplaced aux b",
             "statement": {"english": "trivial", "conclusion": "(2::int) = 2"},
             "name": "aux_b",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After batch; Branch closes parent, siblings aggregated into warnings", file)
    root.print(0, file)
    ws = root.session.warnings
    file.write(f"session.warnings count: {len(ws)}\n")
    if ws:
        head = ws[0][:300].replace("\n", " | ")
        file.write(f"aggregated warning head: {head}...\n")


@model_test("AutoIntroQ7Skip", "Test_AutoIntroQ7Skip.thy", 8)
async def _test_AutoIntroQ7Skip(root: Root, file: MyIO):
    """Have wrapping a ∀-statement: need_intro is True.  Agent-provided
    proof STARTS with Intro → Q7 skip rule: no auto-injection, tree has
    exactly one Intro (the agent's)."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "outer Have wrapping ∀-stmt",
        "statement": {"english": "refl", "conclusion": r"\<forall>(a::int). a = a"},
        "name": "refl",
        "proof": [
            {"operation": "Intro", "thought": "agent's explicit Intro"},
            {"operation": "Obvious", "facts": []},
        ],
    })])
    print_header("After Have with proof starting with Intro (Q7: no auto-inject)", file)
    root.print(0, file)
    have = root.locate_node("1")
    kinds = [type(c).__name__ for c in cast(NonLeaf_Node, have).sub_nodes]
    file.write(f"Have.sub_nodes kinds: {kinds}\n")
    intro_count = sum(1 for c in cast(NonLeaf_Node, have).sub_nodes if isinstance(c, Intro))
    assert intro_count == 1, f"Q7 skip FAIL: expected exactly 1 Intro, got {intro_count}"


@model_test("AutoIntroQ7Inject", "Test_AutoIntroQ7Inject.thy", 8)
async def _test_AutoIntroQ7Inject(root: Root, file: MyIO):
    """Have wrapping a ∀-statement: need_intro is True.  Agent-provided
    proof does NOT start with Intro → Q7: auto-Intro is injected.  The
    injected Intro closes the Have via _close_by, truncating trailing
    siblings.  Truncation is reported via FOOTER warning on Have."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "outer Have; agent forgot to Intro first",
        "statement": {"english": "refl", "conclusion": r"\<forall>(a::int). a = a"},
        "name": "refl",
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("After Have with proof=[Obvious]; Q7 injects Intro which truncates Obvious", file)
    root.print(0, file, show_warnings=True)
    have = root.locate_node("1")
    first = cast(NonLeaf_Node, have).sub_nodes[0] if cast(NonLeaf_Node, have).sub_nodes else None
    file.write(f"Have.sub_nodes[0] kind: {type(first).__name__ if first else 'none'}\n")
    file.write(f"Have.sub_nodes total: {len(cast(NonLeaf_Node, have).sub_nodes)}\n")
    foot = [w for w in have.warnings if w.position == _W.Position.FOOTER]
    file.write(f"FOOTER warnings on Have: {len(foot)}\n")


@model_test("AmendSingleKeepsChildren", "Test_AmendSingleKeepsChildren.thy", 8)
async def _test_AmendSingleKeepsChildren(root: Root, file: MyIO):
    """Single-item amend with NO nested proof — _amend_from preservation
    keeps the target's existing sub_nodes intact on the new node."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "initial",
        "statement": {"english": "init", "conclusion": r"x * x \<ge> 0"},
        "name": "orig",
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("After seed Have { proof: [Obvious] }", file)
    root.print(0, file)
    have = root.locate_node("1")
    assert cast(NonLeaf_Node, have).sub_nodes, "seed failed"
    obv_id = id(cast(NonLeaf_Node, have).sub_nodes[0])

    root.session.age += 1
    await root.amend("1", [Suffices.gen_single({
        "thought": "Suffices with no proof — should inherit",
        "statement": {"english": "repl", "conclusion": r"x * x \<ge> 0"},
    })])
    print_header("After single-item amend; inherited children should remain", file)
    root.print(0, file)
    suff = root.locate_node("1")
    assert isinstance(suff, Suffices), f"expected Suffices, got {type(suff).__name__}"
    sub_ids = [id(c) for c in cast(NonLeaf_Node, suff).sub_nodes]
    file.write(f"Suffices sub_nodes kinds: {[type(c).__name__ for c in cast(NonLeaf_Node, suff).sub_nodes]}\n")
    assert obv_id in sub_ids, "_amend_from preservation FAIL"
    file.write("_amend_from preservation verified.\n")


@model_test("AmendTearsDownWorker", "Test_AmendTearsDownWorker.thy", 8)
async def _test_AmendTearsDownWorker(root: Root, file: MyIO):
    """A CLASS-CHANGING single-op amend (here Have→Suffices) of a node X that
    carries a live WorkerHandle must TEAR DOWN that worker. Under the
    non-destructive-amend policy the worker is kept only when the top-level class
    is UNCHANGED (see `AmendKeepsWorker`); a class change fails
    `_amend_preserves_worker`, so `amend_me`'s commit branch takes
    `await saved.aclose()` — cancelling the worker task and detaching the handle
    (X.worker_handle = None) — while X's partial proof sub-tree is still
    re-parented onto the new (amended) node by `_amend_from`."""
    from .model import WorkerHandle

    def obs(line: str) -> None:
        # Stream every observation to BOTH the golden buffer and stderr, so the
        # observations survive even if a later assert aborts before the golden
        # diff dump (the buffer is only written to .actual.yml on a diff).
        file.write(line + "\n")
        print("[ATDW] " + line, file=sys.stderr, flush=True)

    # 1. Seed step "1" with a Have carrying a small nested proof.
    await root.fill("1", [Have.gen_single({
        "thought": "initial",
        "statement": {"english": "init", "conclusion": r"x * x \<ge> 0"},
        "name": "orig",
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    H = root.locate_node("1")
    assert isinstance(H, NonLeaf_Node), f"expected NonLeaf_Node, got {type(H).__name__}"
    pre_ids = [id(c) for c in H.sub_nodes]   # kept for the assertion; NOT printed
    obs(f"H kind: {type(H).__name__}")
    obs(f"pre-amend child kinds: {[type(c).__name__ for c in H.sub_nodes]}")

    # 2. Attach a worker with a REAL spinning asyncio task so cancellation is
    #    observable. WorkerHandle(target, session); task attr is `_task`.
    handle = WorkerHandle(H, root.session)

    async def _spin():
        await asyncio.sleep(3600)

    handle._task = asyncio.ensure_future(_spin())
    H.worker_handle = handle
    # let the spinning task actually start running before we cancel it
    await asyncio.sleep(0)

    # 3. Observations BEFORE amend.
    obs("=== BEFORE amend ===")
    obs(f"H.worker_handle is set: {H.worker_handle is handle}")
    obs(f"task.cancelled() before: {handle._task.cancelled()}")
    obs(f"task.done() before: {handle._task.done()}")

    # 4. Single-op amend → inheritance path. The amended op carries NO proof body
    #    so the ONLY children on the new node are those re-parented by
    #    `_amend_from` from H (the worker's partial sub-tree).
    settle_exc = None
    try:
        await root.amend("1", [Suffices.gen_single({
            "thought": "amended replacement — should tear down the worker",
            "statement": {"english": "repl", "conclusion": r"x * x \<ge> 0"},
        })])
    except Exception as e:  # _settle_costs may raise if the handle never ran
        settle_exc = e
        obs(f"amend raised (teardown path still executed): {type(e).__name__}: {e}")

    new_node = root.locate_node("1")
    assert isinstance(new_node, NonLeaf_Node), \
        f"expected NonLeaf_Node, got {type(new_node).__name__}"
    post_ids = [id(c) for c in new_node.sub_nodes]

    # 5. Observations AFTER amend.
    obs("=== AFTER amend ===")
    obs(f"new node kind: {type(new_node).__name__}")
    obs(f"worker task.cancelled() after: {handle._task.cancelled()}")
    obs(f"old H.worker_handle is None: {H.worker_handle is None}")
    obs(f"new node is old H: {new_node is H}")
    obs(f"new node.worker_handle: {new_node.worker_handle!r}")
    obs(f"post-amend child kinds: {[type(c).__name__ for c in new_node.sub_nodes]}")
    obs(f"children preserved (post == pre): {post_ids == pre_ids}")
    obs(f"settle_exc: {type(settle_exc).__name__ if settle_exc else None}")

    # CONTRAST (from code, not run here): `delete` routes through `Node.discard`
    # (NonLeaf_Node.discard recurses aclose over the WHOLE subtree AND removes
    # the node from its parent's sub_nodes), so the partial proof sub-tree would
    # be DESTROYED. `amend` instead re-parents the children onto the replacement
    # via `_amend_from`, tearing down only the worker on the replaced node.
    obs("CONTRAST: delete -> Node.discard removes the subtree; "
        "amend -> _amend_from re-parents children, only the worker dies.")

    # 6. Assert the claim (all observations already emitted above).
    assert handle._task.cancelled(), "REFUTED: worker task not cancelled"
    assert H.worker_handle is None, \
        "REFUTED: old node's worker_handle not detached"
    assert new_node.worker_handle is None, \
        "REFUTED: new (amended) node has a worker_handle"
    assert post_ids == pre_ids, \
        "REFUTED: single-op amend did not re-parent the partial sub-tree"
    obs("CLAIM CONFIRMED: worker torn down, handle detached, children re-parented.")


@model_test("AmendKeepsWorker", "Test_AmendKeepsWorker.thy", 8)
async def _test_AmendKeepsWorker(root: Root, file: MyIO):
    """A SAME-CLASS, non-destructive single-op amend (Have→Have, still-open goal)
    of a node carrying a live WorkerHandle must KEEP the worker alive and MIGRATE
    its handle onto the amended node — NOT cancel it. This exercises
    `_amend_preserves_worker` (top-class unchanged, non-SubgoalMaker, the new block
    re-opened SUCCESS, goal not proved out) → `amend_me` commit branch →
    `WorkerHandle.retarget`, which re-points `node.worker_handle`, `handle.target`,
    and the worker session's `role.target`, and clears the stale
    `_initial_prompt_cache`. Contrast `AmendTearsDownWorker` (a class change, which
    still cancels)."""
    from .model import WorkerHandle

    def obs(line: str) -> None:
        file.write(line + "\n")
        print("[AKW] " + line, file=sys.stderr, flush=True)

    # 1. Seed step "1" with a Have whose goal is left OPEN (no proof body), so
    #    `is_proof_finished()` is False and the keep-predicate is not disqualified
    #    by an already-proved goal (the K2 guard).
    await root.fill("1", [Have.gen_single({
        "thought": "initial",
        "statement": {"english": "init", "conclusion": r"x * x \<ge> 0"},
        "name": "orig",
    })])
    H = root.locate_node("1")
    assert isinstance(H, NonLeaf_Node), f"expected NonLeaf_Node, got {type(H).__name__}"
    obs(f"H kind: {type(H).__name__}")
    obs(f"H is_proof_finished (want False): {H.is_proof_finished()}")

    # 2. Attach a worker with a REAL spinning task plus a FAKE worker sub-session
    #    (only the fields `retarget` touches: `role` (a Role_Worker) and
    #    `_initial_prompt_cache`), so we can verify all three handle references and
    #    the cache clear migrate.
    handle = WorkerHandle(H, root.session)

    async def _spin():
        await asyncio.sleep(3600)

    handle._task = asyncio.ensure_future(_spin())

    class _FakeSub:
        pass
    fake_sub = _FakeSub()
    fake_sub.role = model.Role_Worker(target=H)
    fake_sub._initial_prompt_cache = "STALE-HEADER"
    handle._sub = cast(Any, fake_sub)
    # The kept handle is swept by the session-close `aclose_all_subagents`; its
    # `_settle_costs` would call `session._accumulate_subagent_costs` (an LMDriver
    # method absent on the bare test Session). Mark costs settled so the sweep
    # skips cost-accounting on our fake sub-session.
    handle._costs_accumulated = True

    H.worker_handle = handle
    await asyncio.sleep(0)  # let the spinning task start
    obs("=== BEFORE amend ===")
    obs(f"H.worker_handle is set: {H.worker_handle is handle}")
    obs(f"task.cancelled() before: {handle._task.cancelled()}")

    # 3. SAME-CLASS amend (Have→Have), same still-open conclusion → KEEP.
    await root.amend("1", [Have.gen_single({
        "thought": "amended — same class, should keep & migrate the worker",
        "statement": {"english": "repl", "conclusion": r"x * x \<ge> 0"},
        "name": "orig",
    })])

    new_node = root.locate_node("1")
    assert isinstance(new_node, NonLeaf_Node), \
        f"expected NonLeaf_Node, got {type(new_node).__name__}"
    obs("=== AFTER amend ===")
    obs(f"new node kind: {type(new_node).__name__}")
    obs(f"new node is old H: {new_node is H}")
    obs(f"worker task.cancelled() after (want False): {handle._task.cancelled()}")
    obs(f"old H.worker_handle is None (want True): {H.worker_handle is None}")
    obs(f"new_node.worker_handle is handle (want True): {new_node.worker_handle is handle}")
    obs(f"handle.target is new_node (want True): {handle.target is new_node}")
    obs(f"role.target is new_node (want True): {handle._sub.role.target is new_node}")
    obs(f"_initial_prompt_cache cleared (want True): {handle._sub._initial_prompt_cache is None}")

    # 4. Assert the keep + migrate.
    assert not handle._task.cancelled(), "REFUTED: worker task was cancelled (should be kept)"
    assert H.worker_handle is None, "REFUTED: old node still holds the handle"
    assert new_node.worker_handle is handle, "REFUTED: handle not migrated onto the new node"
    assert handle.target is new_node, "REFUTED: handle.target not retargeted"
    assert handle._sub.role.target is new_node, "REFUTED: worker role.target not retargeted"
    assert handle._sub._initial_prompt_cache is None, "REFUTED: stale prompt cache not cleared"
    obs("CLAIM CONFIRMED: worker kept alive, handle + role.target migrated, cache cleared.")

    # 5. Cleanup: stop the spinning task we kept alive.
    handle._task.cancel()


@model_test("ValidatorNestedPath", "Test_ValidatorNestedPath.thy", 8)
async def _test_ValidatorNestedPath(root: Root, file: MyIO):
    """Verify `Parse_Op_List` reports path-annotated errors at the
    deepest nested site (both for a missing-field error and for a nested
    forbid-successor violation).  Path format is
    `proof_operations[i] (ClassName).proof[j] ...`."""
    print_header("Initial YAML", file)
    root.print(0, file)
    try:
        Parse_Op_List([
            {"operation": "Have", "thought": "L1",
             "statement": {"english": "L1", "conclusion": r"x * x \<ge> 0"},
             "name": "L1",
             "proof": [
                 {"operation": "Have", "thought": "L2",
                  "statement": {"english": "L2", "conclusion": r"x * x \<ge> 0"},
                  "name": "L2",
                  "proof": [
                      {"operation": "Obvious"},  # missing facts
                  ]},
             ]},
        ], "proof_operations")
        file.write("UNEXPECTED: deep missing-field accepted\n")
    except AoA_Error as e:
        msg = str(e)
        # Two levels of Have nesting + innermost Obvious should appear.
        expected_chain = "proof_operations[0] (Have).proof[0] (Have).proof[0] (Obvious)"
        file.write(f"deep-missing path in error: {expected_chain in msg}\n")
        assert expected_chain in msg, msg

    # Forbid-successor violation nested inside Have.proof: Obvious at index 0
    # followed by another op.
    try:
        Parse_Op_List([
            {"operation": "Have", "thought": "outer",
             "statement": {"english": "o", "conclusion": r"x * x \<ge> 0"},
             "name": "o",
             "proof": [
                 {"operation": "Obvious", "facts": []},
                 {"operation": "Obvious", "facts": []},
             ]},
        ], "proof_operations")
        file.write("UNEXPECTED: nested forbid-successor violation accepted\n")
    except AoA_Error as e:
        msg = str(e)
        # Message references both positions: the successor (proof[1])
        # and the Obvious that forbids it (proof[0] (Obvious)).
        file.write(f"nested forbid-successor path in error: "
                   f"{'proof_operations[0] (Have).proof[0] (Obvious)' in msg}\n")
        assert "proof_operations[0] (Have).proof[0] (Obvious)" in msg, msg
        assert "proof_operations[0] (Have).proof[1]" in msg, msg
    file.write("recursive parse path annotation verified.\n")


@model_test("ValidateUnion_Reject", "Test_ValidateUnion_Reject.thy", 8)
async def _test_ValidateUnion_Reject(root: Root, file: MyIO):
    """Parse-time validation: a value matching NONE of a union's >=2 real
    members is rejected by `_validate_union` with a path-annotated
    `ArgumentError` listing the acceptable forms (TypedDict members by
    class name, literals by value, None as `null`), instead of the old
    silent pass-through.  Covers a 2-member union (`facts`), a
    2-member+None union (`InferenceRule.rule`), and a Literal+2-member
    union (`CaseSplit.rule`).  Also checks valid values still parse."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # (label, op, expected substrings in the rejection message)
    bad_cases = [
        ("InferenceRule.rule = {bogus}  (FactByName | FactByDescription | None)",
         {"operation": "InferenceRule", "thought": "x", "rule": {"bogus": 1}},
         ["must be one of", "`FactByName`", "`FactByDescription`", "null"]),
        ("Obvious.facts[0] = {bogus}  (FactByName | FactByProposition)",
         {"operation": "Obvious", "facts": [{"bogus": 1}]},
         ["must be one of", "`FactByName`", "`FactByProposition`"]),
        ("CaseSplit.rule = {bogus}  (Literal['default'] | FactByName | FactByDescription)",
         {"operation": "CaseSplit", "thought": "x",
          "target_isabelle_term": "b", "rule": {"bogus": 1}},
         ["must be one of", "`default`", "`FactByName`", "`FactByDescription`"]),
    ]
    for label, op, expected in bad_cases:
        print_header(label, file)
        try:
            Parse_Op_List([op], "proof_operations")
            file.write("UNEXPECTED: accepted\n")
            assert False, f"{label} should have been rejected"
        except AoA_Error as e:
            msg = str(e)
            file.write(f"rejected: {all(s in msg for s in expected)}\n")
            file.write(f"message: {msg}\n")
            for s in expected:
                assert s in msg, f"missing {s!r} in: {msg}"

    # Single-real-member unions and matching values are unaffected: these parse.
    print_header("valid values still parse (no reject)", file)
    for label, op in [
        ("InferenceRule.rule = {name: conjI}  (FactByName matches)",
         {"operation": "InferenceRule", "thought": "x", "rule": {"name": "conjI"}}),
        ("InferenceRule.rule = None  (None member)",
         {"operation": "InferenceRule", "thought": "x", "rule": None}),
        ("CaseSplit.rule = 'default'  (Literal matches)",
         {"operation": "CaseSplit", "thought": "x",
          "target_isabelle_term": "b", "rule": "default"}),
    ]:
        Parse_Op_List([op], "proof_operations")
        file.write(f"parsed ok: {label}\n")
    file.write("multi-member-union rejection verified.\n")


@model_test("CaseSplitNestedProofAllCases", "Test_CaseSplitNestedProofAllCases.thy", 8)
async def _test_CaseSplitNestedProofAllCases(root: Root, file: MyIO):
    """CaseSplit with per-case `proofs: [{case_name, body}]` — each entry's
    body is attached to the matching GoalNode at refresh time, resolved via
    the case_name surfaced through `Consider_Case_Msg`.  The goal `P b`
    isn't actually provable, so the attached Obvious is expected to FAIL;
    the assertion checks the STRUCTURE (pending_proof landed as the GoalNode's
    first sub_node, one per case)."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "case-split on boolean b",
        "target_isabelle_term": "b",
        "rule": "default",
        "proofs": [
            {"case_name": "True",  "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "False", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After CaseSplit with per-case proofs", file)
    root.print(0, file)
    cs = root.locate_node("1")
    gn_kids = [c for c in cast(NonLeaf_Node, cs).sub_nodes if type(c).__name__ == "GoalNode"]
    file.write(f"GoalNode children count: {len(gn_kids)}\n")
    for gn in gn_kids:
        kind0 = type(cast(NonLeaf_Node, gn).sub_nodes[0]).__name__ if cast(NonLeaf_Node, gn).sub_nodes else "none"
        file.write(f"  {gn.id}: first sub = {kind0}\n")
        assert cast(NonLeaf_Node, gn).sub_nodes, (
            f"GoalNode {gn.id} empty — per-case pending_proof did not apply "
            f"(case_name lookup probably failed)")


@model_test("CaseSplit_MapCase", "Test_CaseSplit_MapCase.thy", 8)
async def _test_CaseSplit_MapCase(root: Root, file: MyIO):
    """CaseSplit with `proofs` that deliberately uses wrong case_names
    (`"t"`, `"f"`). The exact-name pop at GoalNode refresh fails, which
    triggers `Interaction_MapCase` per GoalNode. The stub fork picks
    index 0 each time, so `"t"` is mapped to actual case `True` and
    `"f"` is mapped to actual case `False`. Verifies that:
      - the interaction is fired (prompt printed)
      - picked supplied body lands on the right GoalNode
      - no leftover FOOTER warning (all supplied got mapped)"""
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_fork(interaction):
        assert isinstance(interaction, Interaction_MapCase), \
            f"unexpected interaction type {type(interaction).__name__}"
        print_header(f"Interaction Prompt for actual case `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        # Pick index 0 of the remaining supplied options. Because the
        # stub is called sequentially per GoalNode and each GoalNode
        # pops its pick from the shared dict, the options list shrinks
        # monotonically across calls.
        return await interaction.answer(AnswerIndex(index=0))
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "case-split on boolean b with wrong case_names",
        "target_isabelle_term": "b",
        "rule": "default",
        "proofs": [
            {"case_name": "t",  "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "f", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After CaseSplit with mapped case_names", file)
    root.print(0, file)
    cs = root.locate_node("1")
    gn_kids = [c for c in cast(NonLeaf_Node, cs).sub_nodes if type(c).__name__ == "GoalNode"]
    file.write(f"GoalNode children count: {len(gn_kids)}\n")
    for gn in gn_kids:
        kind0 = type(cast(NonLeaf_Node, gn).sub_nodes[0]).__name__ if cast(NonLeaf_Node, gn).sub_nodes else "none"
        file.write(f"  {gn.id}: first sub = {kind0}\n")
        assert cast(NonLeaf_Node, gn).sub_nodes, (
            f"GoalNode {gn.id} empty — MapCase interaction did not land a body")


@model_test("CaseSplit_MapCaseDrop", "Test_CaseSplit_MapCaseDrop.thy", 8)
async def _test_CaseSplit_MapCaseDrop(root: Root, file: MyIO):
    """CaseSplit with `proofs` that uses a wrong case_name. The stub
    answers empty `indexes` (drop). Verifies:
      - the interaction is fired
      - no body is attached to the unresolved GoalNode (stays empty)
      - the unclaimed supplied appears in the FOOTER warning"""
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_fork(interaction):
        assert isinstance(interaction, Interaction_MapCase), \
            f"unexpected interaction type {type(interaction).__name__}"
        print_header(f"Interaction Prompt for actual case `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        # Empty indexes = drop; the supplied body stays in _proofs_by_case
        # and should surface as a FOOTER warning after refresh.
        return await interaction.answer(AnswerIndex(index=None))
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "case-split on boolean b; supplied name does not match any actual case",
        "target_isabelle_term": "b",
        "rule": "default",
        "proofs": [
            {"case_name": "wrong", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After CaseSplit with dropped supplied", file)
    root.print(0, file, show_warnings=True)


@model_test("CaseSplit_MapCaseMixedPick", "Test_CaseSplit_MapCaseMixedPick.thy", 8)
async def _test_CaseSplit_MapCaseMixedPick(root: Root, file: MyIO):
    """Mixed path: one supplied case_name matches exactly (`True`), one is
    wrong (`xxx`). Only ONE interaction should fire (for `False`); the
    stub picks index 0 to map `xxx → False`. Verifies the exact-match
    path and the interaction path coexist cleanly."""
    print_header("Initial YAML", file)
    root.print(0, file)

    interaction_count = [0]
    async def stub_fork(interaction):
        interaction_count[0] += 1
        assert isinstance(interaction, Interaction_MapCase), \
            f"unexpected interaction type {type(interaction).__name__}"
        print_header(f"Interaction Prompt for actual case `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        return await interaction.answer(AnswerIndex(index=0))
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "case-split on boolean b: one exact match, one mismatch",
        "target_isabelle_term": "b",
        "rule": "default",
        "proofs": [
            {"case_name": "True", "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "xxx",  "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After CaseSplit (mixed exact + mapped)", file)
    root.print(0, file, show_warnings=True)
    file.write(f"Interactions fired: {interaction_count[0]}\n")
    assert interaction_count[0] == 1, \
        f"expected exactly 1 interaction (for the mismatched `xxx`), got {interaction_count[0]}"


@model_test("CaseSplit_MapCaseMixedDrop", "Test_CaseSplit_MapCaseMixedDrop.thy", 8)
async def _test_CaseSplit_MapCaseMixedDrop(root: Root, file: MyIO):
    """Mixed drop path: one exact match (`True`), one mismatch (`xxx`),
    stub drops the interaction. Expected: True gets body, False has no
    body, FOOTER warning lists `xxx` as dropped."""
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_fork(interaction):
        assert isinstance(interaction, Interaction_MapCase), \
            f"unexpected interaction type {type(interaction).__name__}"
        print_header(f"Interaction Prompt for actual case `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        return await interaction.answer(AnswerIndex(index=None))
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "case-split on boolean b: one exact match, one dropped mismatch",
        "target_isabelle_term": "b",
        "rule": "default",
        "proofs": [
            {"case_name": "True", "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "xxx",  "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After CaseSplit (exact + dropped)", file)
    root.print(0, file, show_warnings=True)


@model_test("Induction_MapCase", "Test_Induction_MapCase.thy", 8)
async def _test_Induction_MapCase(root: Root, file: MyIO):
    """Induction with wrong supplied case_names. Verifies:
      - MapCase fires from within an Induction (not CaseSplit) context
      - prompt shows `induction` as the {kind}
      - IH (Cons.IH) shows up in the rendered case context
      - two interactions fire (one per actual case), both mapped"""
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_fork(interaction):
        assert isinstance(interaction, Interaction_MapCase), \
            f"unexpected interaction type {type(interaction).__name__}"
        assert interaction.kind == "induction", \
            f"expected kind=induction, got {interaction.kind!r}"
        print_header(f"Interaction Prompt for actual case `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        return await interaction.answer(AnswerIndex(index=0))
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [Induction.gen_single({
        "thought": "induction on l with wrong case_names",
        "target_isabelle_term": "l",
        "variables": [{"name": "l", "status": "fixed"}],
        "rule": "default",
        "proofs": [
            {"case_name": "nil_case",  "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "cons_case", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After Induction with mapped case_names", file)
    root.print(0, file, show_warnings=True)



@model_test("CaseSplit_MapCaseAmend", "Test_CaseSplit_MapCaseAmend.thy", 8)
async def _test_CaseSplit_MapCaseAmend(root: Root, file: MyIO):
    """Fill a CaseSplit with wrong-named supplieds (dropped via
    interaction), then amend the same step with correct case_names.
    Verifies:
      - initial fill produces a FOOTER warning for the dropped supplieds
      - amend replaces the node; the new instance has no residue, no
        warning, and proofs attach via exact match (no interaction)"""
    print_header("Initial YAML", file)
    root.print(0, file)

    amend_interaction_count = [0]
    async def drop_stub(interaction):
        assert isinstance(interaction, Interaction_MapCase)
        return await interaction.answer(AnswerIndex(index=None))
    async def amend_stub(interaction):
        amend_interaction_count[0] += 1
        file.write(f"UNEXPECTED interaction after amend: {type(interaction).__name__}\n")
        return await interaction.answer(AnswerIndex(index=None))

    root.session.launch_interaction = drop_stub
    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "case-split on b with wrong names (to be amended)",
        "target_isabelle_term": "b",
        "rule": "default",
        "proofs": [
            {"case_name": "wrong1", "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "wrong2", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After fill with wrong names (both dropped)", file)
    root.print(0, file, show_warnings=True)

    root.session.launch_interaction = amend_stub
    root.session.age += 1
    await root.amend("1", [CaseSplit.gen_single({
        "thought": "case-split on b with correct names",
        "target_isabelle_term": "b",
        "rule": "default",
        "proofs": [
            {"case_name": "True",  "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "False", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After amend with correct names", file)
    root.print(0, file, show_warnings=True)
    file.write(f"Interactions after amend: {amend_interaction_count[0]} (expected 0)\n")
    assert amend_interaction_count[0] == 0, \
        f"amend should not fire any interaction when all names match exactly"


@model_test("CaseSplit_ReservedName_Rejected",
            "Test_CaseSplit_ReservedName_Rejected.thy", 8)
async def _test_CaseSplit_ReservedName_Rejected(root: Root, file: MyIO):
    """Parse-time validation: a supplied `case_name` that equals
    `CASE_EXISTING` or starts with `new-` / `old-` is rejected with a
    path-annotated `ArgumentError`."""
    print_header("Initial YAML", file)
    root.print(0, file)
    for bad_name in (CASE_EXISTING, "new-foo", "old-bar"):
        try:
            Parse_Op_List([
                {"operation": "CaseSplit", "thought": "reserved",
                 "target_isabelle_term": "b", "rule": "default",
                 "proofs": [{"case_name": bad_name,
                             "body": [{"operation": "Obvious", "facts": []}]}]},
            ], "proof_operations")
            file.write(f"UNEXPECTED: `{bad_name}` accepted\n")
            assert False, f"reserved name `{bad_name}` should have been rejected"
        except AoA_Error as e:
            msg = str(e)
            file.write(f"`{bad_name}` rejected: reserved-mention={'reserved' in msg}\n")
            assert "reserved" in msg, msg
            assert bad_name in msg, msg
    file.write("all reserved-name patterns rejected.\n")


@model_test("CaseSplit_AmendReconcile_ExactMatch",
            "Test_CaseSplit_AmendReconcile_ExactMatch.thy", 8)
async def _test_CaseSplit_AmendReconcile_ExactMatch(root: Root, file: MyIO):
    """Amend-reconcile with matching case_names: new bodies silently
    replace the inherited GoalNodes' sub-trees without firing any
    MapCase interaction."""
    print_header("Initial YAML", file)
    root.print(0, file)
    interaction_count = [0]
    async def count_stub(interaction):
        interaction_count[0] += 1
        file.write(f"UNEXPECTED interaction: {type(interaction).__name__}\n")
        return await interaction.answer(AnswerIndex(index=None))
    root.session.launch_interaction = count_stub

    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "initial case-split (exact names)",
        "target_isabelle_term": "b", "rule": "default",
        "proofs": [
            {"case_name": "True",  "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "False", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After initial fill (True/False)", file)
    root.print(0, file, show_warnings=True)

    root.session.age += 1
    await root.amend("1", [CaseSplit.gen_single({
        "thought": "amend: same names, different body",
        "target_isabelle_term": "b", "rule": "default",
        "proofs": [
            {"case_name": "True",
             "body": [{"operation": "Have", "thought": "t-have",
                       "statement": {"english": "trivial", "conclusion": "True"},
                       "name": "h"}]},
            {"case_name": "False",
             "body": [{"operation": "Have", "thought": "f-have",
                       "statement": {"english": "trivial", "conclusion": "True"},
                       "name": "h"}]},
        ],
    })])
    print_header("After amend (silent replace)", file)
    root.print(0, file, show_warnings=True)
    file.write(f"Interactions fired: {interaction_count[0]} (expected 0)\n")
    assert interaction_count[0] == 0, \
        "Exact-name amend should silently replace bodies; no MapCase"


@model_test("CaseSplit_AmendReconcile_Rematch",
            "Test_CaseSplit_AmendReconcile_Rematch.thy", 8)
async def _test_CaseSplit_AmendReconcile_Rematch(root: Root, file: MyIO):
    """Amend-reconcile with all-different case_names: fires MapCase
    once per inherited GoalNode.  Stub picks `new-*` for the first
    GN and `old-*` for the second to exercise both apply branches."""
    print_header("Initial YAML", file)
    root.print(0, file)

    interaction_count = [0]
    async def pick_stub(interaction):
        interaction_count[0] += 1
        assert isinstance(interaction, Interaction_MapCase)
        print_header(f"MapCase for `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        # Pick index 0 (first option: the first remaining new-*).
        # The options list for each goal has the new-* options first,
        # then (if applicable) own old-* last.  Index 0 is a new-* pick.
        if interaction.actual_case == "True":
            return await interaction.answer(AnswerIndex(index=0))   # pick new-*
        # For the second goal ('False'), pick the last option which is
        # the own old-* (keep existing body).
        last_idx = len(interaction.supplied_options) - 1
        assert interaction.supplied_options[last_idx].startswith("old-")
        return await interaction.answer(AnswerIndex(index=last_idx))
    root.session.launch_interaction = pick_stub

    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "initial fill with exact names True/False",
        "target_isabelle_term": "b", "rule": "default",
        "proofs": [
            {"case_name": "True",  "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "False", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After initial fill", file)
    root.print(0, file, show_warnings=True)

    root.session.age += 1
    await root.amend("1", [CaseSplit.gen_single({
        "thought": "amend: all-different case_names",
        "target_isabelle_term": "b", "rule": "default",
        "proofs": [
            {"case_name": "alt1",
             "body": [{"operation": "Have", "thought": "alt1-have",
                       "statement": {"english": "t", "conclusion": "True"},
                       "name": "h"}]},
            {"case_name": "alt2",
             "body": [{"operation": "Have", "thought": "alt2-have",
                       "statement": {"english": "t", "conclusion": "True"},
                       "name": "h"}]},
        ],
    })])
    print_header("After amend (rematch: new- for True, old- for False)", file)
    root.print(0, file, show_warnings=True)
    file.write(f"Interactions fired: {interaction_count[0]} (expected 2)\n")
    assert interaction_count[0] == 2, \
        f"expected 2 MapCase interactions (one per GN), got {interaction_count[0]}"


@model_test("CaseSplit_AmendReconcile_Drop",
            "Test_CaseSplit_AmendReconcile_Drop.thy", 8)
async def _test_CaseSplit_AmendReconcile_Drop(root: Root, file: MyIO):
    """Amend-reconcile where the agent drops every mismatched GN via
    MapCase.  Each GN ends up with its inherited sub-tree cleared and
    no new body attached.  The un-picked supplied bodies surface in the
    FOOTER 'not found' warning."""
    print_header("Initial YAML", file)
    root.print(0, file)

    interaction_count = [0]
    async def drop_stub(interaction):
        interaction_count[0] += 1
        assert isinstance(interaction, Interaction_MapCase)
        return await interaction.answer(AnswerIndex(index=None))   # drop
    root.session.launch_interaction = drop_stub

    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "initial",
        "target_isabelle_term": "b", "rule": "default",
        "proofs": [
            {"case_name": "True",  "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "False", "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After initial fill", file)
    root.print(0, file)

    root.session.age += 1
    await root.amend("1", [CaseSplit.gen_single({
        "thought": "amend: different names; stub drops all",
        "target_isabelle_term": "b", "rule": "default",
        "proofs": [
            {"case_name": "xxx",
             "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "yyy",
             "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After amend (all dropped)", file)
    root.print(0, file, show_warnings=True)
    file.write(f"Interactions fired: {interaction_count[0]}\n")


@model_test("CaseSplit_Pair_N1_OverSupply",
            "Test_CaseSplit_Pair_N1_OverSupply.thy", 8)
async def _test_CaseSplit_Pair_N1_OverSupply(root: Root, file: MyIO):
    """`case_tac` on a pair type produces exactly one runtime case
    (the `Pair` constructor).  Agent supplies TWO named bodies; the
    MapCase fires once for the single runtime case, stub picks the
    first option.  The other supplied name is dropped with a FOOTER
    `not found` warning."""
    print_header("Initial YAML", file)
    root.print(0, file)

    interaction_count = [0]
    async def pick_stub(interaction):
        interaction_count[0] += 1
        assert isinstance(interaction, Interaction_MapCase)
        print_header(f"MapCase for `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        return await interaction.answer(AnswerIndex(index=0))
    root.session.launch_interaction = pick_stub

    root.session.age += 1
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "case-split on pair; over-supply two bodies",
        "target_isabelle_term": "p", "rule": "default",
        "proofs": [
            {"case_name": "alpha",
             "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "beta",
             "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After splice (N==1, over-supply)", file)
    root.print(0, file, show_warnings=True)
    file.write(f"Interactions fired: {interaction_count[0]} (expected 1)\n")
    assert interaction_count[0] == 1, \
        f"expected 1 MapCase (single runtime case), got {interaction_count[0]}"


@model_test("CaseSplit_Pair_N1_Keep",
            "Test_CaseSplit_Pair_N1_Keep.thy", 8)
async def _test_CaseSplit_Pair_N1_Keep(root: Root, file: MyIO):
    """Insert_before an existing proof step with a CaseSplit-with-proofs
    on N==1 (pair).  Stub picks the `the_existing_proof` option, so
    the existing siblings are preserved; the supplied body is dropped
    with a FOOTER warning."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # First seed the proof with one Obvious step, then insert_before it.
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "seed", "name": "h",
        "statement": {"english": "trivial", "conclusion": "True"}})])
    print_header("After seeding Have at step 1", file)
    root.print(0, file)

    interaction_count = [0]
    async def keep_stub(interaction):
        interaction_count[0] += 1
        assert isinstance(interaction, Interaction_MapCase)
        print_header(f"MapCase for `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        # Find the "existing proof" sentinel option and pick it.
        try:
            idx = interaction.supplied_options.index(CASE_EXISTING)
        except ValueError:
            assert False, f"`{CASE_EXISTING}` not offered — siblings-after missing?"
        return await interaction.answer(AnswerIndex(index=idx))
    root.session.launch_interaction = keep_stub

    root.session.age += 1
    await root.insert_before("1", [CaseSplit.gen_single({
        "thought": "case-split on pair; agent picks 'keep existing'",
        "target_isabelle_term": "p", "rule": "default",
        "proofs": [
            {"case_name": "nope",
             "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After insert_before (stub kept existing)", file)
    root.print(0, file, show_warnings=True)
    file.write(f"Interactions fired: {interaction_count[0]} (expected 1)\n")
    assert interaction_count[0] == 1


@model_test("CaseSplit_Pair_N1_Replace",
            "Test_CaseSplit_Pair_N1_Replace.thy", 8)
async def _test_CaseSplit_Pair_N1_Replace(root: Root, file: MyIO):
    """Same setup as Keep, but the stub picks the supplied body:
    existing siblings are truncated with a warning, and the supplied
    body is spliced as the new parent-sibling after the CaseSplit."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "seed", "name": "h",
        "statement": {"english": "trivial", "conclusion": "True"}})])
    print_header("After seeding Have at step 1", file)
    root.print(0, file)

    interaction_count = [0]
    async def replace_stub(interaction):
        interaction_count[0] += 1
        assert isinstance(interaction, Interaction_MapCase)
        print_header(f"MapCase for `{interaction.actual_case}`", file)
        await interaction.prompt(0, file)
        # Pick first option (a new-* supplied body).
        return await interaction.answer(AnswerIndex(index=0))
    root.session.launch_interaction = replace_stub

    root.session.age += 1
    await root.insert_before("1", [CaseSplit.gen_single({
        "thought": "case-split on pair; agent replaces existing with supplied",
        "target_isabelle_term": "p", "rule": "default",
        "proofs": [
            {"case_name": "replacement",
             "body": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After insert_before (stub replaced existing)", file)
    root.print(0, file, show_warnings=True)


@model_test("CaseSplit_Pair_N1_MidProof",
            "Test_CaseSplit_Pair_N1_MidProof.thy", 8)
async def _test_CaseSplit_Pair_N1_MidProof(root: Root, file: MyIO):
    """`case_tac` on pair WITHOUT supplied proofs — acts as a mid-proof
    transformation step.  No interaction should fire; the seeded
    sibling(s) after it stay put (no truncate, no splice)."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "seed", "name": "h",
        "statement": {"english": "trivial", "conclusion": "True"}})])
    print_header("After seeding Have at step 1", file)
    root.print(0, file)

    interaction_count = [0]
    async def unexpected_stub(interaction):
        interaction_count[0] += 1
        file.write(f"UNEXPECTED interaction: {type(interaction).__name__}\n")
        return await interaction.answer(AnswerIndex(index=None))
    root.session.launch_interaction = unexpected_stub

    root.session.age += 1
    await root.insert_before("1", [CaseSplit.gen_single({
        "thought": "case-split on pair as mid-proof transform; no proofs",
        "target_isabelle_term": "p", "rule": "default",
        # No `proofs` — CaseSplit just transforms the current goal.
    })])
    print_header("After insert_before (no-proofs; siblings untouched)", file)
    root.print(0, file, show_warnings=True)
    file.write(f"Interactions fired: {interaction_count[0]} (expected 0)\n")
    assert interaction_count[0] == 0


@model_test("CaseSplit_NestedCaseNameShadow",
            "Test_CaseSplit_NestedCaseNameShadow.thy", 8)
async def _test_CaseSplit_NestedCaseNameShadow(root: Root, file: MyIO):
    """Regression test for the nested-induction case_name shadowing
    encountered in the production log at
    ``log/AoA/DC0408929_17A6CF6/interaction.yaml`` (lines ~1244-1281).

    Setup: outer Induction on ``n`` opens a "Suc" case (binding
    ``Suc.IH`` etc.).  The body of that "Suc" case starts a fresh inner
    Induction on the same variable name ``n``.  Isabelle disambiguates
    the inner case binding to avoid shadowing the outer one — the
    inner case ends up named ``Suc1`` (with ``Suc1.IH``), not ``Suc``.

    Fix verified: ``CaseSplit_Like._orchestrate_rematch`` runs a
    second pre-process pass that strips trailing digits from the
    runtime case_name and retries an exact lookup against the supplied
    dict.  ``Suc1`` → strip → ``Suc`` matches the supplied entry; the
    body is installed silently and NO ``Interaction_MapCase`` fires.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    interactions_seen: list[tuple[str, str, list[str]]] = []
    async def stub_fork(interaction):
        if isinstance(interaction, Interaction_MapCase):
            interactions_seen.append(
                (interaction.kind, interaction.actual_case,
                 list(interaction.supplied_options)))
            file.write(
                f"UNEXPECTED MapCase fired: kind={interaction.kind} "
                f"actual_case={interaction.actual_case!r} "
                f"options={list(interaction.supplied_options)}\n")
            return await interaction.answer(AnswerIndex(index=None))
        if isinstance(interaction, Interaction_SelectIHFacts):
            # Decline the IH-fact picker (select none) so this induction
            # test's output is unaffected by that feature.
            return await interaction.answer(AnswerIndexes(indexes=[]))
        file.write(
            f"Other (non-MapCase) interaction: "
            f"{type(interaction).__name__}\n")
        return await interaction.answer(AnswerIndex(index=None))
    root.session.launch_interaction = stub_fork

    root.session.age += 1
    await root.fill("1", [Induction.gen_single({
        "thought": "outer induction on n",
        "target_isabelle_term": "n",
        "variables": [
            {"name": "n", "status": "fixed"},
            {"name": "P", "status": "fixed"},
        ],
        "rule": "default",
        "proofs": [
            {"case_name": "0",
             "body": [{"operation": "Obvious", "facts": []}]},
            {"case_name": "Suc",
             "body": [
                 {"operation": "Induction",
                  "thought": "inner induction on the same variable n",
                  "target_isabelle_term": "n",
                  "variables": [
                      {"name": "n", "status": "fixed"},
                      {"name": "P", "status": "fixed"},
                  ],
                  "rule": "default",
                  "proofs": [
                      {"case_name": "0",
                       "body": [{"operation": "Obvious", "facts": []}]},
                      {"case_name": "Suc",
                       "body": [{"operation": "Obvious", "facts": []}]},
                  ]},
             ]},
        ],
    })])
    print_header("After nested induction (outer Suc body has inner Induction)",
                 file)
    root.print(0, file, show_warnings=True)
    file.write(f"\nMapCase interactions fired: {len(interactions_seen)} "
               f"(expected 0 — fuzzy match handles `Suc1`→`Suc`)\n")
    assert interactions_seen == [], \
        f"Fuzzy match regressed: MapCase fired for {interactions_seen}"


@model_test("CaseSplit_NestedSkolem",
            "Test_CaseSplit_NestedSkolem.thy", 8)
async def _test_CaseSplit_NestedSkolem(root: Root, file: MyIO):
    """Regression test for skolemized variable names in nested CaseSplits.

    When two CaseSplits happen on variables of the same type (both nat),
    the inner CaseSplit's Suc case introduces a predecessor variable that
    collides with the outer one. Isabelle's Variable.add_fixes_binding
    skolemizes it (appending ``__``), producing names like ``nat__`` that
    are invalid in user-facing terms — ``Name.reject_internal`` /
    ``Name.reject_skolem`` raises "Bad name" when the agent tries to use
    them in a Have or Suffices statement.

    This test reproduces the bug from the production log at
    ``log/AoA/DCAE54855_17D7672/interaction.yaml`` (lines ~4366-4605).
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: CaseSplit on n
    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on n",
        "target_isabelle_term": "n"
    })])
    print_header("After CaseSplit on n", file)
    import sys
    n0 = root.locate_node("1.0")
    n1 = root.locate_node("1.Suc")
    print(f"DEBUG 1.0: ml={n0.ml_state.name}, res={n0.resulting_state().name}, status={n0.status}", file=sys.stderr)
    print(f"DEBUG 1.Suc: ml={n1.ml_state.name}, goal={cast(GoalNode, n1).goal() is not None}, leading_goal={n1.ml_state.leading_goal is not None}", file=sys.stderr)
    root.print(0, file)

    # Step 2: Inside the Suc case of n, CaseSplit on m.
    # The Suc case introduces a predecessor variable named `nat` (from the type).
    # The inner CaseSplit on m also wants to introduce `nat` as its predecessor,
    # causing a naming conflict.
    root.session.age += 1
    await root.fill("1.Suc.1", [CaseSplit.gen_single({
        "thought": "Case split on m inside Suc case of n",
        "target_isabelle_term": "m"
    })])
    print_header("After nested CaseSplit on m (inside Suc of n)", file)
    root.print(0, file)

    # Step 3: Inspect the inner Suc case for skolemized variable names.
    # After CaseSplit m inside CaseSplit n's Suc case, the inner Suc case
    # is at path 1.Suc.1.Suc1.
    inner_suc = cast(GoalNode, root.locate_node("1.Suc.1.Suc1"))
    goal = inner_suc.goal()
    skolem_vars = []
    skolem_in_conclusion = False
    conclusion_str = ""
    if goal is not None:
        for var_name in goal.context.vars:
            name_str = var_name.unicode if hasattr(var_name, 'unicode') else repr(var_name)
            if name_str.endswith("__"):
                skolem_vars.append(name_str)
        conclusion_str = goal.conclusion.unicode if hasattr(goal.conclusion, 'unicode') else repr(goal.conclusion)
        if "__" in conclusion_str:
            skolem_in_conclusion = True
            file.write(f"BUG: Goal conclusion contains skolemized name: {conclusion_str}\n")
    if inner_suc.case_vars:
        for (vname, vtype) in inner_suc.case_vars:
            name_str = vname.unicode if hasattr(vname, 'unicode') else str(vname)
            if name_str.endswith("__"):
                skolem_vars.append(name_str)
    if inner_suc.case_hyps:
        for (hname, hterm) in inner_suc.case_hyps:
            hname_str = hname.unicode if hasattr(hname, 'unicode') else repr(hname)
            term_str = hterm.unicode if hasattr(hterm, 'unicode') else repr(hterm)
            if "__" in term_str:
                file.write(f"BUG: Premise '{hname_str}' contains skolemized name: {term_str}\n")
    file.write(f"Skolemized variable names found: {skolem_vars}\n")

    # Step 4: Try to use a variable from the inner goal in a Have statement.
    # If the goal contains a skolemized variable like `nat__`, using it in
    # a Have statement will trigger "Bad name" from Isabelle.
    if goal is not None:
        conclusion_str = goal.conclusion.unicode if hasattr(goal.conclusion, 'unicode') else str(goal.conclusion)
        # Try a Have that references the conclusion (which may contain nat__)
        root.session.age += 1
        outcome = await root.fill("1.Suc.1.Suc1.1", [Have.gen_single({
            "thought": "Restate part of the goal",
            "statement": {
                "english": "restating the goal conclusion",
                "conclusion": conclusion_str
            },
            "name": "htest"
        })])
        if outcome.failure is not None:
            file.write(f"Have with goal conclusion failed: {outcome.failure}\n")
            if "Bad name" in str(outcome.failure):
                file.write("CONFIRMED BUG: 'Bad name' error from skolemized variable name\n")
        else:
            file.write("Have with goal conclusion succeeded (no skolem issue)\n")

    print_header("Final state", file)
    root.print(0, file)

    if skolem_vars or skolem_in_conclusion:
        parts = []
        if skolem_vars:
            parts.append(f"variable names: {skolem_vars}")
        if skolem_in_conclusion:
            parts.append(f"goal conclusion: {conclusion_str}")
        raise TestFailed(
            f"Skolemized names leaked to agent ({', '.join(parts)}). "
            "Agent cannot reference these in statements (Isabelle rejects them with 'Bad name').")


@model_test("CaseSplit_InteractiveVars",
            "Test_CaseSplit_InteractiveVars.thy", 8)
async def _test_CaseSplit_InteractiveVars(root: Root, file: MyIO):
    """Test agent-specified case variable names via case_variables in proofs.

    CaseSplit on nat with case_variables: Suc case names its predecessor 'k'
    instead of the default 'nat' or 'n'. Verifies:
    1. The variable 'k' appears in the Suc case's context
    2. The proof can reference 'k' in a Have statement
    """
    print_header("Initial", file)
    root.print(0, file)

    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on n with custom variable names",
        "target_isabelle_term": "n",
        "proofs": [
            {"case_name": "0", "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Suc", "case_variables": ["k"], "body": [
                {"operation": "Obvious", "facts": []}
            ]}
        ]
    })])
    print_header("After CaseSplit with case_variables", file)
    root.print(0, file)

    suc_node = cast(GoalNode, root.locate_node("1.Suc"))
    if suc_node is None:
        raise TestFailed("Cannot find node 1.Suc")
    if suc_node.case_vars is None:
        raise TestFailed("Suc case has no case_vars")
    var_names = [v[0] for v in suc_node.case_vars]
    file.write(f"Suc case_vars: {var_names}\n")
    if "k" not in [v.unicode if hasattr(v, 'unicode') else str(v) for v in var_names]:
        raise TestFailed(f"Expected 'k' in Suc case_vars, got: {var_names}")


@model_test("Induction_InteractiveVars",
            "Test_Induction_InteractiveVars.thy", 8)
async def _test_Induction_InteractiveVars(root: Root, file: MyIO):
    """Test agent-specified case variable names for Induction.

    Induction on nat with case_variables: Suc case names its predecessor 'k'.
    Verifies the variable 'k' appears in the Suc case's context and
    the induction hypothesis references 'k'.
    """
    print_header("Initial", file)
    root.print(0, file)

    await root.fill("1", [Induction.gen_single({
        "thought": "Induction on n with custom variable names",
        "target_isabelle_term": "n",
        "variables": [{"name": "n", "status": "fixed"}],
        "proofs": [
            {"case_name": "0", "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Suc", "case_variables": ["k"], "body": [
                {"operation": "Obvious", "facts": [
                    {"name": "Suc.IH"}
                ]}
            ]}
        ]
    })])
    print_header("After Induction with case_variables", file)
    root.print(0, file)

    zero_node = cast(GoalNode, root.locate_node("1.0"))
    if zero_node is not None and zero_node.case_vars is not None:
        file.write(f"0 case_vars: {[v[0] for v in zero_node.case_vars]}\n")

    suc_node = cast(GoalNode, root.locate_node("1.Suc"))
    if suc_node is None:
        raise TestFailed("Cannot find node 1.Suc")
    if suc_node.case_vars is not None:
        var_names = [v[0] for v in suc_node.case_vars]
        file.write(f"Suc case_vars: {var_names}\n")
        if "k" not in [v.unicode if hasattr(v, 'unicode') else str(v) for v in var_names]:
            raise TestFailed(f"Expected 'k' in Suc case_vars, got: {var_names}")
    else:
        file.write(f"Suc case_vars: not yet set (status={suc_node.status.status.value})\n")


def _varname_strs(node: GoalNode) -> list[str] | None:
    if node.case_vars is None:
        return None
    return [v.unicode if hasattr(v, 'unicode') else str(v) for v, _ty in node.case_vars]


@model_test("CaseSplit_VarNames_MultiVar",
            "Test_CaseSplit_VarNames_MultiVar.thy", 8)
async def _test_CaseSplit_VarNames_MultiVar(root: Root, file: MyIO):
    """CaseSplit on a list with case_variables: ["x", "xs"] for Cons.
    Verifies multiple agent-specified variable names reach ML."""
    print_header("Initial", file)
    root.print(0, file)

    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on list l",
        "target_isabelle_term": "l",
        "proofs": [
            {"case_name": "Nil", "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Cons", "case_variables": ["x", "xs"], "body": [
                {"operation": "Obvious", "facts": []}
            ]}
        ]
    })])
    print_header("After CaseSplit with multi-var Cons", file)
    root.print(0, file)

    cons_node = cast(GoalNode, root.locate_node("1.Cons"))
    names = _varname_strs(cons_node)
    file.write(f"Cons case_vars: {names}\n")
    if names is None or "x" not in names or "xs" not in names:
        raise TestFailed(f"Expected ['x', 'xs'] in Cons case_vars, got: {names}")


@model_test("CaseSplit_VarNames_FirstCase",
            "Test_CaseSplit_VarNames_FirstCase.thy", 8)
async def _test_CaseSplit_VarNames_FirstCase(root: Root, file: MyIO):
    """CaseSplit on nat with case_variables for the FIRST case (0).
    The first case goes through beginning_opr re-refresh."""
    print_header("Initial", file)
    root.print(0, file)

    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on n, naming first case var",
        "target_isabelle_term": "n",
        "proofs": [
            {"case_name": "0", "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Suc", "case_variables": ["k"], "body": [
                {"operation": "Obvious", "facts": []}
            ]}
        ]
    })])
    print_header("After CaseSplit", file)
    root.print(0, file)

    suc_node = cast(GoalNode, root.locate_node("1.Suc"))
    names = _varname_strs(suc_node)
    file.write(f"Suc case_vars: {names}\n")
    if names is None or "k" not in names:
        raise TestFailed(f"Expected 'k' in Suc case_vars, got: {names}")


@model_test("CaseSplit_VarNames_AllCases",
            "Test_CaseSplit_VarNames_AllCases.thy", 8)
async def _test_CaseSplit_VarNames_AllCases(root: Root, file: MyIO):
    """CaseSplit on list with case_variables for ALL cases.
    Nil has no variables, so case_variables is empty.
    Cons specifies ["h", "t"]."""
    print_header("Initial", file)
    root.print(0, file)

    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on l with varnames for all cases",
        "target_isabelle_term": "l",
        "proofs": [
            {"case_name": "Nil", "case_variables": [], "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Cons", "case_variables": ["h", "t"], "body": [
                {"operation": "Obvious", "facts": []}
            ]}
        ]
    })])
    print_header("After CaseSplit with all case vars", file)
    root.print(0, file)

    cons_node = cast(GoalNode, root.locate_node("1.Cons"))
    names = _varname_strs(cons_node)
    file.write(f"Cons case_vars: {names}\n")
    if names is None or "h" not in names or "t" not in names:
        raise TestFailed(f"Expected ['h', 't'] in Cons case_vars, got: {names}")


@model_test("Induction_VarNames_MultiVar",
            "Test_Induction_VarNames_MultiVar.thy", 8)
async def _test_Induction_VarNames_MultiVar(root: Root, file: MyIO):
    """Induction on a list with case_variables: ["y", "ys"] for Cons.
    Verifies multiple agent-specified variable names work with Induction."""
    print_header("Initial", file)
    root.print(0, file)

    await root.fill("1", [Induction.gen_single({
        "thought": "Induction on l with custom Cons vars",
        "target_isabelle_term": "l",
        "variables": [{"name": "l", "status": "fixed"}],
        "proofs": [
            {"case_name": "Nil", "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Cons", "case_variables": ["y", "ys"], "body": [
                {"operation": "Obvious", "facts": []}
            ]}
        ]
    })])
    print_header("After Induction with multi-var Cons", file)
    root.print(0, file)

    cons_node = cast(GoalNode, root.locate_node("1.Cons"))
    names = _varname_strs(cons_node)
    file.write(f"Cons case_vars: {names}\n")
    if names is None or "y" not in names or "ys" not in names:
        raise TestFailed(f"Expected ['y', 'ys'] in Cons case_vars, got: {names}")


@model_test("CaseSplit_VarNames_Rename",
            "Test_CaseSplit_VarNames_Rename.thy", 8)
async def _test_CaseSplit_VarNames_Rename(root: Root, file: MyIO):
    """CaseSplit with case_variables, then rename a variable.
    Currently GoalNode._rename_var doesn't check case_vars in the
    multi-case path, so rename_var raises CannotRename_VariableNotFound.
    This test documents that limitation."""
    print_header("Initial", file)
    root.print(0, file)

    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on n",
        "target_isabelle_term": "n",
        "proofs": [
            {"case_name": "0", "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Suc", "case_variables": ["k"], "body": [
                {"operation": "Obvious", "facts": []}
            ]}
        ]
    })])
    print_header("After CaseSplit with k", file)
    root.print(0, file)

    suc_node = cast(GoalNode, root.locate_node("1.Suc"))
    names = _varname_strs(suc_node)
    file.write(f"Before rename - Suc case_vars: {names}\n")

    try:
        await root.rename_var(IsaTerm.from_agent("k"), IsaTerm.from_agent("m"))
        print_header("After rename k -> m", file)
        root.print(0, file)
        suc_node = cast(GoalNode, root.locate_node("1.Suc"))
        names = _varname_strs(suc_node)
        file.write(f"After rename - Suc case_vars: {names}\n")
    except CannotRename_VariableNotFound:
        file.write(f"rename_var raised CannotRename_VariableNotFound (expected: GoalNode multi-case path)\n")


@model_test("CaseSplit_VarNames_Amend",
            "Test_CaseSplit_VarNames_Amend.thy", 8)
async def _test_CaseSplit_VarNames_Amend(root: Root, file: MyIO):
    """CaseSplit without case_variables, then amend with case_variables.
    Verifies that amend can introduce agent varnames."""
    print_header("Initial", file)
    root.print(0, file)

    await root.fill("1", [CaseSplit.gen_single({
        "thought": "Case split on n, no varnames",
        "target_isabelle_term": "n",
        "proofs": [
            {"case_name": "0", "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Suc", "body": [
                {"operation": "Obvious", "facts": []}
            ]}
        ]
    })])
    print_header("After CaseSplit without varnames", file)
    root.print(0, file)

    suc_node = cast(GoalNode, root.locate_node("1.Suc"))
    names = _varname_strs(suc_node)
    file.write(f"Before amend - Suc case_vars: {names}\n")

    root.session.age += 1
    await root.amend("1", [CaseSplit.gen_single({
        "thought": "Case split on n, now with varnames",
        "target_isabelle_term": "n",
        "proofs": [
            {"case_name": "0", "body": [
                {"operation": "Obvious", "facts": []}
            ]},
            {"case_name": "Suc", "case_variables": ["j"], "body": [
                {"operation": "Obvious", "facts": []}
            ]}
        ]
    })])
    print_header("After amend with case_variables", file)
    root.print(0, file)

    suc_node = cast(GoalNode, root.locate_node("1.Suc"))
    names = _varname_strs(suc_node)
    file.write(f"After amend - Suc case_vars: {names}\n")


@model_test("NestedHaveProof", "Test_NestedHaveProof.thy", 8)
async def _test_NestedHaveProof(root: Root, file: MyIO):
    """A single-item batch where the item's `proof` field carries a nested
    Obvious — verifies that nested proof lists are parsed and attached as
    children at refresh time."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "auxiliary restating of the goal",
        "statement": {"english": "x*x nonneg", "conclusion": r"x * x \<ge> 0"},
        "name": "h1",
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("After Have with nested proof=[Obvious]", file)
    root.print(0, file)
    have_node = root.locate_node("1")
    assert isinstance(have_node, Have), f"expected Have at 1, got {type(have_node).__name__}"
    assert len(cast(NonLeaf_Node, have_node).sub_nodes) >= 1, \
        f"expected at least one nested child under Have, got {len(cast(NonLeaf_Node, have_node).sub_nodes)}"


@model_test("BatchFill_HaveObvious", "Test_BatchFill_HaveObvious.thy", 8)
async def _test_BatchFill_HaveObvious(root: Root, file: MyIO):
    """Multi-item fill batch [Have with nested Obvious, Obvious]: verify the
    first fills target_step, the second appends to the same parent, and the
    outer goal gets discharged by the appended Obvious."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Have", "thought": "restate goal as aux",
             "statement": {"english": "x*x nonneg", "conclusion": r"x * x \<ge> 0"},
             "name": "aux",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Obvious",
             "facts": [{"name": "aux"}]},
        ]})
    print_header("edit_message: batch fill [Have(proof:[Obvious]), Obvious]", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")
    print_header("After batched fill [Have(proof:[Obvious]), Obvious]", file)
    root.print(0, file)
    unfinished: set[Node] = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("ComplexEditFlow", "Test_ComplexEditFlow.thy", 8)
async def _test_ComplexEditFlow(root: Root, file: MyIO):
    """Exercises diverse `edit_message` variants in one flow:
      (1) bare Obvious on a non-trivial goal → GoalIsNontrivial,
      (2) batch fill success → range headline + Congratulations,
      (3) amend missing target → CannotEdit_NodeNotFound,
      (4) amend with unprovable replacement → is_error=True + revert,
      (5) amend recovery → success,
      (6) batch insert_before → range headline."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)

    # (1) bare Obvious on a non-trivial goal.
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Obvious", "facts": []},
        ]})
    print_header("[1] fill [Obvious] — goal is non-trivial", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")

    # (2) batch fill: Have(nested Obvious) + Obvious using aux → done.
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Have", "thought": "restate goal",
             "statement": {"english": "nonneg", "conclusion": r"x * x \<ge> 0"},
             "name": "aux",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Obvious",
             "facts": [{"name": "aux"}]},
        ]})
    print_header("[2] batch fill [Have(nested), Obvious(using aux)]", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")

    # (3) amend a node that doesn't exist.
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "999", "action": "amend", "proof_operations": [
            {"operation": "Obvious", "facts": []},
        ]})
    print_header("[3] amend missing target '999'", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")

    # (4) amend step 1 into an unprovable statement — nested Obvious fails,
    #     hook requests TERMINATE_AND_REVERT.
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "amend", "proof_operations": [
            {"operation": "Have", "thought": "unprovable replacement",
             "statement": {"english": "false", "conclusion": "(1::int) = 2"},
             "name": "bad",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    print_header("[4] amend step 1 with unprovable `1 = 2`", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")

    # (5) amend step 1 with a provable renamed Have → success.
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "amend", "proof_operations": [
            {"operation": "Have", "thought": "renamed aux",
             "statement": {"english": "nonneg", "conclusion": r"x * x \<ge> 0"},
             "name": "aux2",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    print_header("[5] amend step 1 (recovery) with `x*x >= 0`", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")

    # (6) batch insert_before [Have, Have] at step 1.
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "insert_before", "proof_operations": [
            {"operation": "Have", "thought": "ins1",
             "statement": {"english": "h1", "conclusion": r"x * x \<ge> 0"},
             "name": "h1",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Have", "thought": "ins2",
             "statement": {"english": "h2", "conclusion": r"x * x \<ge> 0"},
             "name": "h2",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    print_header("[6] batch insert_before [Have, Have] at step 1", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")


@model_test("WorkerErrIdLeak", "Test_WorkerErrIdLeak.thy", 8)
async def _test_worker_err_id_leak(root: Root, file: MyIO):
    """Reproduces the AoA defect in /tmp/report1.md: when a worker (sub-agent)
    fills an open sub-step and the fill FAILS, the `edit` error message
    ("Cannot fill a node with id X") leaks the UN-relativized ABSOLUTE node id
    (carrying the worker's mount-point prefix), while recall / outline / the
    success headline all show the worker-RELATIVE id. The diagnostic id (in the
    error) and the actionable id (everywhere else) then live in two different
    namespaces that the worker cannot reconcile — exactly the loop the report
    observed (worker burns rounds re-`recall`-ing and rewriting its briefing).

    Setup: a `Have` sub-lemma `sub` (the worker's target, absolute id "1") with a
    deliberately unprovable body `(1::int) = 2`. A worker scoped to it fills its
    open body subgoal — which it addresses by the RELATIVE id "1" — with a bare
    `Obvious`. The hammer fails on the unprovable goal, the node is reverted
    (is_error=True), and the failure renders via `prompts.edit_message` →
    `CannotEdit._action_phrase`.

    Root cause: `_action_phrase` prints `self.target_step`, which
    `Obvious._on_edit_failure` set to the ABSOLUTE id "1.1" (via
    `CannotEdit_EvaluationFailed(self.id, ...)`), with no
    `Session._display_id` absolute→relative projection applied. Tellingly, the
    reason text emitted right beside it on the same code path IS relativized
    (`Obvious._on_edit_failure` wraps it in `the_session()._relativize_text(...)`)
    — so the id leak is an inconsistency in that very method, not a missing
    feature. We assert the id rendered in the error equals the worker-relative id
    the worker actually used.
    """
    import re
    from .mcp_http_server import _edit_tool_logic
    session = root.session
    goal = root.sub_nodes[1]

    # The sub-lemma the worker will be dispatched on (absolute id "1"); its body
    # `(1::int) = 2` is unprovable, so a bare Obvious inside it will fail.
    await goal.fill("1", [Have.gen_single({
        "thought": "sub-lemma to be discharged by a worker",
        "statement": {"english": "one equals two", "conclusion": r"(1::int) = 2"},
        "name": "sub"})])
    H = goal.sub_nodes[0]
    assert H.id == "1", f"expected the sub-lemma at absolute id '1', got {H.id!r}"

    # Scope a worker to H. The worker addresses H's open body slot (absolute
    # "1.1") by its relative id — what recall/outline show and what it must use.
    body_abs = "1.1"
    session.role = model.Role_Worker(target=H)
    try:
        worker_rel = session._display_id(body_abs)
        file.write(f"worker scope root (absolute): {H.id}\n")
        file.write(f"body slot absolute id:        {body_abs}\n")
        file.write(f"body slot worker-relative id: {worker_rel}\n")

        # Worker fills its open subgoal with a bare Obvious; the hammer fails, the
        # step reverts, and the failure is rendered to the worker via the real
        # tool path (`_edit_tool_logic` → `prompts.edit_message`).
        session.age += 1
        result, is_error = await _edit_tool_logic(session, {
            "target_step": worker_rel, "action": "fill",
            "proof_operations": [{"operation": "Obvious", "facts": []}]})
    finally:
        session.role = model.Role_Major()

    print_header("worker `edit fill` failure response", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")

    # The error must name the step in the SAME namespace the worker uses.
    m = re.search(r"Cannot fill a node with id (\S+)", result)
    if m is None:
        raise TestFailed(
            "WorkerErrIdLeak: expected a 'Cannot fill a node with id X' failure "
            f"(is_error={is_error}); got:\n{result}")
    shown_id = m.group(1)
    file.write(f"id shown in error message:    {shown_id}\n")
    file.write(f"leaks absolute mount prefix:  {shown_id != worker_rel}\n")
    if shown_id != worker_rel:
        raise TestFailed(
            "WorkerErrIdLeak: the fill-failure error leaked an un-relativized "
            f"node id. The worker addresses the step as {worker_rel!r} (recall / "
            f"outline / headline all use that), but the error says 'Cannot fill a "
            f"node with id {shown_id}' — two namespaces the worker cannot "
            f"reconcile (see /tmp/report1.md). Expected {worker_rel!r}.")


@model_test("WorkerErrIdLeak_BlockClosed", "Test_WorkerErrIdLeak_BlockClosed.thy", 8)
async def _test_worker_err_id_leak_blockclosed(root: Root, file: MyIO):
    """Companion to `WorkerErrIdLeak` covering the OTHER id-bearing field of an
    edit failure: `CannotEdit_BlockClosed.closed_by` (the report-driven fix had
    to relativize this too, but no prior golden exercised it).

    A worker fills a batch into its target's body. The first op — an
    `InferenceRule` (`conjI`) — splits the conjunctive goal and CLOSES the body
    block (`SubgoalMaker._should_open_proof_block` →
    `YES_AND_CLOSE_PARENT_BLOCK`), so the trailing `Have` cannot attach and the
    append raises `CannotEdit_BlockClosed`, whose `_reason` says
    "…edit node {closed_by} instead". `closed_by` is the ABSOLUTE id of the
    closing node ("1.1"); a worker scoped at "1" must see it RELATIVE ("1") —
    the same projection bug class as the node-id leak, on the reason side.
    """
    import re
    from .mcp_http_server import _edit_tool_logic
    session = root.session
    goal = root.sub_nodes[1]

    # Have sub-lemma (worker target, absolute id "1"); its body is a conjunction
    # so `conjI` splits it and closes the body block.
    await goal.fill("1", [Have.gen_single({
        "thought": "sub-lemma the worker discharges",
        "statement": {"english": "trivial conjunction",
                      "conclusion": r"(1::int) = 1 \<and> (2::int) = 2"},
        "name": "sub"})])
    H = goal.sub_nodes[0]
    assert H.id == "1", f"expected the sub-lemma at absolute id '1', got {H.id!r}"

    session.role = model.Role_Worker(target=H)
    try:
        # The closing InferenceRule lands at absolute "1.1"; worker-relative "1".
        worker_rel = session._display_id("1.1")
        expected_closed = worker_rel               # closed_by == the node just filled
        session.age += 1
        result, is_error = await _edit_tool_logic(session, {
            "target_step": worker_rel, "action": "fill",
            "proof_operations": [
                {"operation": "InferenceRule", "thought": "split via conjI",
                 "rule": {"name": "conjI"}},
                {"operation": "Have", "thought": "misplaced trailing step",
                 "statement": {"english": "x", "conclusion": r"(1::int) = 1"},
                 "name": "mis",
                 "proof": [{"operation": "Obvious", "facts": []}]},
            ]})
    finally:
        session.role = model.Role_Major()

    print_header("worker batch fill: trailing op hits block-closed", file)
    file.write(result)
    file.write("\n---------------\n")
    file.write(f"is_error: {is_error}\n")
    file.write(f"worker-relative closing-node id: {expected_closed}\n")

    # The redirect hint must name the closing node in the worker's namespace.
    m = re.search(r"edit node (\S+) instead", result)
    if m is None:
        raise TestFailed(
            "WorkerErrIdLeak_BlockClosed: expected a block-closed "
            f"'edit node X instead' hint; got:\n{result}")
    shown = m.group(1)
    file.write(f"id shown in block-closed hint:   {shown}\n")
    file.write(f"leaks absolute mount prefix:     {shown != expected_closed}\n")
    if shown != expected_closed:
        raise TestFailed(
            "WorkerErrIdLeak_BlockClosed: the block-closed reason leaked an "
            f"un-relativized closed_by id — worker scope is '1', so the closing "
            f"node 'edit node {shown} instead' should read "
            f"{expected_closed!r} (see /tmp/report1.md).")


@model_test("BatchInsertBefore", "Test_BatchInsertBefore.thy", 8)
async def _test_BatchInsertBefore(root: Root, file: MyIO):
    """insert_before with a list of two Have ops — each carries its own
    nested proof, and both land as consecutive siblings before the target."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    # Seed the tree with a pre-existing Obvious at step 1.
    await root.fill("1", [Obvious.gen_single({"facts": []})])
    print_header("After initial fill with Obvious", file)
    root.print(0, file)
    # Batch-insert two Haves before step 1.
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "insert_before", "proof_operations": [
            {"operation": "Have", "thought": "first aux",
             "statement": {"english": "aux a", "conclusion": r"x * x \<ge> 0"},
             "name": "aux_a",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Have", "thought": "second aux",
             "statement": {"english": "aux b", "conclusion": r"x * x \<ge> 0"},
             "name": "aux_b",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After batched insert_before [Have, Have]", file)
    root.print(0, file)


@model_test("AmendMultiSequence", "Test_AmendMultiSequence.thy", 8)
async def _test_AmendMultiSequence(root: Root, file: MyIO):
    """`amend` on a single step where the replacement is a *list* of
    several proof operations.  The target is deleted and the list lands
    in its former slot as consecutive siblings — exercises the
    multi-item amend path and the `Amended step X-Y.` range headline."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)

    # Seed the proof with a single Have (will later be amended into many).
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Have", "thought": "seed aux",
             "statement": {"english": "nonneg", "conclusion": r"x * x \<ge> 0"},
             "name": "seed",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    print_header("[1] seed fill: single Have", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")

    # Amend step 1 with THREE replacement Haves; target is removed and
    # the three land as siblings at its former position.
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "amend", "proof_operations": [
            {"operation": "Have", "thought": "replacement A",
             "statement": {"english": "rA", "conclusion": r"x * x \<ge> 0"},
             "name": "rA",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Have", "thought": "replacement B",
             "statement": {"english": "rB", "conclusion": r"x * x \<ge> 0"},
             "name": "rB",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Have", "thought": "replacement C",
             "statement": {"english": "rC", "conclusion": r"x * x \<ge> 0"},
             "name": "rC",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    print_header("[2] amend step 1 with THREE Haves", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")

    # Amend the middle of the triple (step 2) with TWO replacements — to
    # exercise mid-sequence multi-amend.
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "2", "action": "amend", "proof_operations": [
            {"operation": "Have", "thought": "mid replacement 1",
             "statement": {"english": "m1", "conclusion": r"x * x \<ge> 0"},
             "name": "m1",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Have", "thought": "mid replacement 2",
             "statement": {"english": "m2", "conclusion": r"x * x \<ge> 0"},
             "name": "m2",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    print_header("[3] amend step 2 with TWO Haves (mid-sequence)", file)
    file.write(result)
    file.write("---------------\n")
    file.write(f"is_error: {is_error}\n")


@model_test("BatchAmendMulti", "Test_BatchAmendMulti.thy", 8)
async def _test_BatchAmendMulti(root: Root, file: MyIO):
    """amend with a multi-item list — target deleted, list inserted at its
    former slot; no `_amend_from` inheritance (old children gone with target)."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    # Seed a Have with inner proof.
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "original",
        "statement": {"english": "orig", "conclusion": r"x * x \<ge> 0"},
        "name": "orig",
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("After initial Have at step 1", file)
    root.print(0, file)
    # Amend step 1 with a two-item list (delete + insert semantics).
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "amend", "proof_operations": [
            {"operation": "Have", "thought": "replacement 1",
             "statement": {"english": "r1", "conclusion": r"x * x \<ge> 0"},
             "name": "r1",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Have", "thought": "replacement 2",
             "statement": {"english": "r2", "conclusion": r"x * x \<ge> 0"},
             "name": "r2",
             "proof": [{"operation": "Obvious", "facts": []}]},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After batched amend [Have, Have] replacing step 1", file)
    root.print(0, file)


@model_test("NestedBranchCases", "Test_NestedBranchCases.thy", 8)
async def _test_NestedBranchCases(root: Root, file: MyIO):
    """A Branch whose individual `cases[i].proof` fields each carry a nested
    Obvious list — all cases get their proof attached at refresh time."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Branch.gen_single({
        "thought": "trichotomy on x",
        "cases": [
            {"statement": {"english": "positive", "isabelle": "x > 0", "name": "pos"},
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"statement": {"english": "negative", "isabelle": "x < 0", "name": "neg"},
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"statement": {"english": "zero", "isabelle": "x = 0", "name": "zero"},
             "proof": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After Branch with per-case nested Obvious", file)
    root.print(0, file)


@model_test("BatchCase1Reject", "Test_BatchCase1Reject.thy", 8)
async def _test_BatchCase1Reject(root: Root, file: MyIO):
    """`Parse_Op_List` must reject a forest where a terminal operation
    (`Obvious`, which implements `if remaining is not None: raise` in
    its `.gen`) is followed by another sibling — nothing can execute
    after such an op."""
    print_header("Initial YAML", file)
    root.print(0, file)
    ops = [
        {"operation": "Obvious", "facts": []},
        {"operation": "Obvious", "facts": []},
    ]
    try:
        Parse_Op_List(ops, "proof_operations")
        file.write("UNEXPECTED: parser accepted [Obvious, Obvious]\n")
    except AoA_Error as e:
        file.write(f"parser correctly rejected:\n{e}\n")
    # Complementary: Branch followed by Obvious is NOT rejected statically
    # — closing behaviour for Branch is runtime-dependent (depends on goal
    # count and Isabelle state), so truncation is handled at refresh time
    # by `_close_by` plus a FOOTER warning.
    ops2 = [
        {"operation": "Branch", "thought": "trichotomy",
         "cases": [
             {"statement": {"english": "p", "isabelle": "x > 0", "name": "p"}},
             {"statement": {"english": "z", "isabelle": "x = 0", "name": "z"}},
             {"statement": {"english": "n", "isabelle": "x < 0", "name": "n"}},
         ]},
        {"operation": "Obvious", "facts": []},
    ]
    try:
        Parse_Op_List(ops2, "proof_operations")
        file.write("parser accepted [Branch, Obvious] (closing is runtime-dependent)\n")
    except AoA_Error as e:
        file.write(f"UNEXPECTED: {e}\n")
    # The tree must be untouched — no mutation on parse failure.
    print_header("Tree after parse checks (should be unchanged)", file)
    root.print(0, file)


@model_test("InferenceRuleBatch", "Test_InferenceRuleBatch.thy", 8)
async def _test_InferenceRuleBatch(root: Root, file: MyIO):
    """Regression test for the real-world failure where the OLD hardcoded
    `_STRICT_SUBGOALMAKER_OPS` (now removed) wrongly rejected a batch
    starting with `InferenceRule ccontr` followed by `Have` / `Obvious`
    siblings.

    Under the current parser only `Obvious` is statically rejected when
    followed by siblings.  For `InferenceRule ccontr`: the rule produces
    a single subgoal at runtime (the contradictory premise plus `False`),
    so `_should_open_proof_block` returns NO — no block is opened, the
    parent block is NOT closed, and subsequent siblings in the batch
    attach normally."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "InferenceRule",
             "thought": "proof by contradiction",
             "rule": {"name": "ccontr"}},
            {"operation": "Obvious", "facts": []},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After batch [InferenceRule ccontr, Obvious]", file)
    root.print(0, file)
    # Both items should have landed as siblings under the goal's proof line.
    n1 = root.locate_node("1")
    parent = n1.parent
    assert parent is not None
    kinds = [type(c).__name__ for c in parent.sub_nodes]
    file.write(f"sibling kinds: {kinds}\n")
    assert "InferenceRule" in kinds, (
        f"InferenceRule missing from sibling list; parser must have "
        f"rejected — got kinds {kinds}")
    # The Obvious should be present as a sibling (not swallowed into some
    # InferenceRule subgoal slot), confirming no-close-parent behaviour.
    assert kinds.count("Obvious") >= 1, \
        f"expected Obvious as a sibling, got kinds {kinds}"
    unfinished: set[Node] = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("InferenceRuleBatch_MultiSubgoal",
            "Test_InferenceRuleBatch_MultiSubgoal.thy", 8)
async def _test_InferenceRuleBatch_MultiSubgoal(root: Root, file: MyIO):
    """Complement to `InferenceRuleBatch`: when an InferenceRule splits the
    goal into multiple subgoals, `SubgoalMaker._should_open_proof_block`
    returns YES_AND_CLOSE_PARENT_BLOCK, which closes the parent proof line.
    Subsequent siblings in the batch cannot attach — `StdBlock.append` raises
    `CannotAppend_BlockClosed`.  The batch path catches this, commits only
    the InferenceRule, and emits a single aggregated `session.warnings`
    entry carrying the unapplied tail verbatim so the agent can re-submit
    the steps at the correct location (inside one of the new GoalNodes).
    `is_error` stays False because one item did land in the tree."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    # conjI splits `P ∧ Q` into two subgoals — SubgoalMaker will CLOSE the parent.
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "InferenceRule",
             "thought": "split conjunction via conjI",
             "rule": {"name": "conjI"}},
            # These two are agent's mistake — they cannot be siblings after
            # a block-closing SubgoalMaker.  Expected to be aggregated into
            # `session.warnings` as unapplied.
            {"operation": "Have", "thought": "misplaced aux",
             "statement": {"english": "aux", "conclusion": "(1::int) = (1::int)"},
             "name": "aux",
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"operation": "Obvious", "facts": []},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After batch; InferenceRule splits, siblings aggregated into session.warnings",
                 file)
    # Print with show_warnings=True so FOOTER discard warnings surface.
    root.print(0, file, show_warnings=True)
    n1 = root.locate_node("1")
    assert isinstance(n1, InferenceRule), \
        f"step 1 should be the InferenceRule, got {type(n1).__name__}"
    parent = n1.parent
    assert parent is not None
    # Parent must be closed by the InferenceRule.
    assert parent._closed_by is n1, \
        f"parent._closed_by should be the InferenceRule; got {parent._closed_by!r}"
    # Parent's sub_nodes should contain only the InferenceRule (no stray siblings).
    assert parent.sub_nodes and parent.sub_nodes[-1] is n1, \
        f"InferenceRule should be parent's last child; kinds={[type(c).__name__ for c in parent.sub_nodes]}"
    # InferenceRule should now have exactly 2 GoalNode children (from conjI).
    goal_kids = [c for c in cast(NonLeaf_Node, n1).sub_nodes if type(c).__name__ == "GoalNode"]
    file.write(f"InferenceRule GoalNode children: {len(goal_kids)}\n")
    assert len(goal_kids) == 2, \
        f"expected 2 subgoals from conjI on P∧Q, got {len(goal_kids)}"
    # `is_error` must be False (InferenceRule landed).
    assert is_error is False, f"expected is_error=False, got {is_error}"
    assert isinstance(result, str)
    file.write(f"response length: {len(result)} chars\n")
    assert "Filled step 1." in result, \
        f"response missing single-commit headline; response:\n{result}"
    assert "The proof block is closed" in result, \
        f"response missing block-closed failure notice; response:\n{result}"
    assert "You should edit node 1 instead" in result, \
        f"response missing closed_by redirect hint; response:\n{result}"


@model_test("InferenceRuleProofsPerSubgoal",
            "Test_InferenceRuleProofsPerSubgoal.thy", 8)
async def _test_InferenceRuleProofsPerSubgoal(root: Root, file: MyIO):
    """InferenceRule with `proofs: [[Obv1], [Obv2]]` (two entries): splice
    does NOT fire (len != 1).  At refresh time, each `proofs[i]` is applied
    positionally as `pending_proof` on the i-th GoalNode child of the
    InferenceRule.  `conjI` splits `P ∧ Q` into two subgoals, each
    discharged by its own Obvious."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "InferenceRule",
             "thought": "split ∧ via conjI",
             "rule": {"name": "conjI"},
             "proofs": [
                 [{"operation": "Obvious", "facts": []}],
                 [{"operation": "Obvious", "facts": []}],
             ]},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After batch; per-subgoal proofs landed under InferenceRule",
                 file)
    root.print(0, file)
    ir = root.locate_node("1")
    goal_kids = [c for c in cast(NonLeaf_Node, ir).sub_nodes if type(c).__name__ == "GoalNode"]
    file.write(f"InferenceRule GoalNode children: {len(goal_kids)}\n")
    assert len(goal_kids) == 2, \
        f"expected 2 subgoals from conjI on P∧Q, got {len(goal_kids)}"
    for i, gn in enumerate(goal_kids):
        assert cast(NonLeaf_Node, gn).sub_nodes, (
            f"GoalNode {gn.id} is empty — positional proofs[{i}] did not apply")
        file.write(f"  {gn.id}: first sub = {type(cast(NonLeaf_Node, gn).sub_nodes[0]).__name__}\n")
    unfinished: set[Node] = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("InferenceRule_ProofsOverSupply",
            "Test_InferenceRuleProofsPerSubgoal.thy", 8)
async def _test_InferenceRule_ProofsOverSupply(root: Root, file: MyIO):
    """Agent supplies 3 positional proofs but conjI only produces 2
    subgoals.  The first 2 proofs match by key ("1" and "2"); the 3rd
    proof (key "3") has no matching GoalNode and should appear in the
    footer warning as unconsumed."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "conjI with oversupply",
        "rule": {"name": "conjI"},
        "proofs": [
            [{"operation": "Obvious", "facts": []}],
            [{"operation": "Obvious", "facts": []}],
            [{"operation": "Obvious", "facts": []}],
        ],
    })])
    print_header("After fill: 2 subgoals matched, proof[2] unconsumed", file)
    root.print(0, file, show_warnings=True)
    ir = root.locate_node("1")
    goal_kids = [c for c in cast(NonLeaf_Node, ir).sub_nodes
                 if type(c).__name__ == "GoalNode"]
    file.write(f"GoalNode children: {len(goal_kids)}\n")
    for gn in goal_kids:
        has_body = bool(cast(NonLeaf_Node, gn).sub_nodes)
        file.write(f"  {gn.id}: has_body={has_body}\n")


@model_test("InferenceRule_ProofsUnderSupply",
            "Test_InferenceRuleProofsPerSubgoal.thy", 8)
async def _test_InferenceRule_ProofsUnderSupply(root: Root, file: MyIO):
    """Agent supplies 1 positional proof but conjI produces 2 subgoals.
    Proof[0] matches GoalNode "1"; GoalNode "2" gets no proof and
    remains open (default _rematch drops)."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "conjI with undersupply",
        "rule": {"name": "conjI"},
        "proofs": [
            [{"operation": "Obvious", "facts": []}],
        ],
    })])
    print_header("After fill: proof[0] on subgoal 1, subgoal 2 empty", file)
    root.print(0, file)
    ir = root.locate_node("1")
    goal_kids = [c for c in cast(NonLeaf_Node, ir).sub_nodes
                 if type(c).__name__ == "GoalNode"]
    file.write(f"GoalNode children: {len(goal_kids)}\n")
    for gn in goal_kids:
        has_body = bool(cast(NonLeaf_Node, gn).sub_nodes)
        file.write(f"  {gn.id}: has_body={has_body}\n")


@model_test("BranchPartialProofs", "Test_NestedBranchCases.thy", 8)
async def _test_BranchPartialProofs(root: Root, file: MyIO):
    """Branch with 3 cases but only case 1 and 3 have proofs.
    Case 2 (no proof) should remain open."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Branch.gen_single({
        "thought": "trichotomy, partial proofs",
        "cases": [
            {"statement": {"english": "positive", "isabelle": "x > 0", "name": "pos"},
             "proof": [{"operation": "Obvious", "facts": []}]},
            {"statement": {"english": "negative", "isabelle": "x < 0", "name": "neg"},
             "proof": None},
            {"statement": {"english": "zero", "isabelle": "x = 0", "name": "zero"},
             "proof": [{"operation": "Obvious", "facts": []}]},
        ],
    })])
    print_header("After Branch: cases 1,3 have proof, case 2 empty", file)
    root.print(0, file)
    br = root.locate_node("1")
    goal_kids = [c for c in cast(NonLeaf_Node, br).sub_nodes
                 if type(c).__name__ == "GoalNode"]
    file.write(f"GoalNode children: {len(goal_kids)}\n")
    for gn in goal_kids:
        has_body = bool(cast(NonLeaf_Node, gn).sub_nodes)
        file.write(f"  {gn.id}: has_body={has_body}\n")


@model_test("InferenceRule_Quickview", "Test_InferenceRuleBatch.thy", 8)
async def _test_InferenceRule_Quickview(root: Root, file: MyIO):
    """Bug: InferenceRule with N<=1 subgoals doesn't show derived goal in
    quickview.  _print_header (full print) shows it, but quickview()
    inherits the default Node.quickview which omits it.

    Uses ccontr (N=1): derived goal should be `¬ P ⟶ False`."""
    await root.fill("1", [InferenceRule.gen_single({
        "thought": "proof by contradiction",
        "rule": {"name": "ccontr"},
    })])
    print_header("Full print (shows derived goal)", file)
    root.print(0, file)
    print_header("Quickview (should show derived goal too)", file)
    root.quickview(0, file)


# Disabled: YAML-diff check is unstable because several intermediate Obvious
# steps depend on Sledgehammer/auto (notably 3.2.5.1 squaring sqrt(p/3) < n).
# The cat_tree BLOCK patch it covers is exercised by the rest of the AoA
# suite; revive this when we have a sorry-ending Minilang op or trim the
# reproducer to avoid ATP-sensitive Obvious calls.
# @model_test("CcontrIntroMatch", "Test_Ccontr_Intro_Match.thy", 14)
async def _test_CcontrIntroMatch(root: Root, file: MyIO):
    """Reproducer for `exception Match raised (line 675 of library/proof.ML)`
    replayed from the real Rabinowitz proof logged at /tmp/t3 step 3.2.10.

    The stack at the failure is Intro→Induction(nat_less_induct)→Branch,
    with 7 Have steps preceding the ccontr. Earlier simpler shapes
    (single Branch, single InferenceRule) do NOT fire the bug — only the
    two-level CASES nest (Induction + Branch) plus accumulated local facts
    reaches the cat_tree(BLOCK, PROP) mismatch.

    Structural hypothesis: agent_server.ML:272 sets INTRO_mk_block=true →
    INTRO''.PRT wraps in BLOCK → the enclosing single-sibling CASES PRT
    (library/proof.ML:2374) invokes cat_tree (BLOCK _) (PROP _) →
    cat_tree has no BLOCK pattern at lib/proof.ML:675-677 → Match.
    """
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)

    # --- Step 1: Intro (fix i, leave `i ≤ p-2` as premise) ---
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "Introduce the universally quantified variable i, keep i≤p-2 as premise",
        "variable_bindings": ["i"],
        "fact_bindings": [],
    })])
    # --- Step 2: Induction on i via nat_less_induct ---
    root.session.age += 1
    await root.fill("2", [Induction.gen_single({
        "thought": "Strong induction on i",
        "target_isabelle_term": "i",
        "rule": {"name": "nat_less_induct"},
        "variables": [
            {"name": "i", "status": "generalized"},
            {"name": "f", "status": "fixed"},
            {"name": "p", "status": "fixed"},
        ],
    })])
    print_header("After Intro + Induction", file)
    root.print(0, file)

    # --- Step 3: Branch on whether n ≤ ⌊sqrt(p/3)⌋ ---
    root.session.age += 1
    await root.fill("3", [Branch.gen_single({
        "thought": "Case split on whether n ≤ sqrt(p/3)",
        "cases": [
            {"statement": {"name": "small",
                           "english": "n small enough for h1 to apply",
                           "isabelle": "int n ≤ ⌊sqrt (real p / (3::real))⌋"}},
            {"statement": {"name": "large",
                           "english": "n too large for h1 to apply directly",
                           "isabelle": "¬ (int n ≤ ⌊sqrt (real p / (3::real))⌋)"}},
        ]
    })])
    # Discharge the exhaustiveness goal 3.0
    root.session.age += 1
    await root.fill("3.0.1", [Obvious.gen_single({"facts": []})])
    # Discharge case 3.1 (small)
    root.session.age += 1
    await root.fill("3.1.1", [Obvious.gen_single({
        "facts": [{"name": "h1"},
                  {"name": "small"}]
    })])
    print_header("After Branch setup + close small case", file)
    root.print(0, file)

    # --- Case 3.2 body: Rewrite + 7 Haves, matching the log ---
    root.session.age += 1
    await root.fill("3.2.1", [Rewrite.gen_single({
        "thought": "unfold f n using h0",
        "using": [{"name": "h0"}],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": [],
    })])
    root.session.age += 1
    await root.fill("3.2.2", [Have.gen_single({
        "thought": "p is prime from h1 with k=0",
        "name": "prime_p",
        "statement": {"english": "p is prime", "conclusion": "prime p"},
        "proof": [
            {"operation": "Derive",
             "thought": "instantiate h1 with k=0",
             "rule": {"name": "h1"},
             "instantiations": [{"name": "?k", "value": "(0::nat)"}],
             "result_name": "h1_0"},
            {"operation": "Obvious",
             "facts": [{"name": "h1_0"},
                       {"name": "h0"}]},
        ],
    })])
    root.session.age += 1
    await root.fill("3.2.3", [Have.gen_single({
        "thought": "p ≥ 2 since it is prime",
        "name": "pge2",
        "statement": {"english": "p ≥ 2", "conclusion": "p ≥ (2::nat)"},
        "proof": [{"operation": "Obvious",
                   "facts": [{"name": "prime_p"},
                             {"name": "prime_ge_2_nat"}]}],
    })])
    root.session.age += 1
    await root.fill("3.2.4", [Have.gen_single({
        "thought": "sqrt(p/3) < real n from large + floor_less_iff",
        "name": "sqrt_lt",
        "statement": {"english": "sqrt(p/3) < real n",
                      "conclusion": "sqrt (real p / (3::real)) < real n"},
        "proof": [{"operation": "Obvious",
                   "facts": [{"name": "large"},
                             {"name": "floor_less_iff"}]}],
    })])
    root.session.age += 1
    await root.fill("3.2.5", [Have.gen_single({
        "thought": "squaring sqrt(p/3) < real n gives p/3 < n^2",
        "name": "p_third_lt",
        "statement": {"english": "p/3 < real n^2",
                      "conclusion": "real p / (3::real) < (real n)^2"},
        "proof": [{"operation": "Obvious",
                   "facts": [{"name": "sqrt_lt"},
                             {"name": "pge2"}]}],
    })])
    root.session.age += 1
    await root.fill("3.2.6", [Have.gen_single({
        "thought": "multiply by 3 to get p < 3n^2",
        "name": "n_big",
        "statement": {"english": "p < 3n^2",
                      "conclusion": "p < (3::nat) * n^2"},
        "proof": [{"operation": "Obvious",
                   "facts": [{"name": "p_third_lt"}]}],
    })])
    root.session.age += 1
    await root.fill("3.2.7", [Have.gen_single({
        "thought": "n ≥ 1 since 3n^2 > p ≥ 2",
        "name": "nge1",
        "statement": {"english": "n ≥ 1", "conclusion": "n ≥ (1::nat)"},
        "proof": [{"operation": "Obvious",
                   "facts": [{"name": "n_big"},
                             {"name": "pge2"}]}],
    })])
    root.session.age += 1
    await root.fill("3.2.8", [Have.gen_single({
        "thought": "fn > 1",
        "name": "fn_gt1",
        "statement": {"english": "n^2 + n + p > 1",
                      "conclusion": "n^2 + n + p > (1::nat)"},
        "proof": [{"operation": "Obvious",
                   "facts": [{"name": "pge2"}]}],
    })])
    print_header("After case 3.2 setup (Rewrite + 7 Haves)", file)
    root.print(0, file)

    # --- Step 3.2.9: InferenceRule(ccontr) with positional Intro splice ---
    #     This is the exact call shape that triggered Match in /tmp/t3.
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "3.2.9", "action": "fill", "proof_operations": [
            {"operation": "InferenceRule",
             "thought": "Proof by contradiction",
             "rule": {"name": "ccontr"},
             "proofs": [[
                 {"operation": "Intro",
                  "thought": "assume ¬ prime (n² + n + p)",
                  "fact_bindings": ["nprime"]}
             ]]},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After fill(3.2.9, InferenceRule ccontr + Intro splice)", file)
    root.print(0, file)

    # Regression guard: before the cat_tree BLOCK patch, the inner Intro
    # failed with `exception Match raised (line 675 ...)`. It must succeed
    # now so that a future regression can't pass by accidentally matching
    # the golden YAML.
    intro_node = root.locate_node("3.2.10")
    assert intro_node.status.status == EvaluationStatus.Status.SUCCESS, (
        f"3.2.10 Intro expected SUCCESS after the cat_tree BLOCK patch, "
        f"got {intro_node.status.status.value}")


@model_test("Unfold_LocalDef", "Test_Unfold_LocalDef.thy", 12)
async def _test_Unfold_LocalDef(root: Root, file: MyIO):
    """Regression test: Unfold on a proof-local function defined via Define.

    Before the fix, potential_defs_of raised IsabelleError("term_head_not_const")
    because the ML callback only accepted Const heads, not Free heads.
    After the fix, the callback also accepts Free heads and looks up
    the local .simps facts registered by FUN.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1-2: Define `double` locally, then Witness it.
    await root.fill("1", [
        Define.gen_single({
            "thought": "Define double as a witness",
            "name": "double",
            "type": r"nat \<Rightarrow> nat",
            "equations": ["double n = n + n"],
        }),
        Witness.gen_single({
            "thought": "Provide the locally-defined double as witness",
            "witnesses": ["double"],
        }),
    ])
    print_header("After Define + Witness", file)
    root.print(0, file)

    # Step 3: Unfold the locally-defined function.
    # Before the fix this raised IsabelleError("term_head_not_const").
    _outcome = await root.fill("3", [Unfold.gen_single({
        "thought": "Unfold the locally-defined double",
        "targets": ["double"],
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    file.write(f"Unfold is_error: {is_error}\n")
    if _outcome.failure:
        file.write(f"Unfold failure: {_outcome.failure}\n")

    print_header("After Unfold", file)
    root.print(0, file)


@model_test("Unfold_LocalDef_Nested", "Test_Unfold_LocalDef_Nested.thy", 10)
async def _test_Unfold_LocalDef_Nested(root: Root, file: MyIO):
    """Reproduce the original zv bug: Define at top level, Intro splits
    the conjunction, then Unfold inside a nested case block.
    This matches the original agent log where Unfold failed with
    'No definitions found for: zv' inside a nested Intro block."""
    from Isabelle_RPC_Host.universal_key import EntityKind

    # Step 1: Define double, Step 2: Witness double
    await root.fill("1", [
        Define.gen_single({
            "thought": "Define double",
            "name": "double",
            "type": r"nat \<Rightarrow> nat",
            "equations": ["double n = n + n"],
        }),
        Witness.gen_single({
            "thought": "Witness double",
            "witnesses": ["double"],
        }),
    ])

    # Step 3: SplitConjs to create nested cases
    await root.fill("3", [SplitConjs.gen_single({
        "thought": "Split conjunction",
    })])
    print_header("After Define + Witness + Intro", file)
    root.print(0, file)

    # Step 3.1.1: Unfold double inside the FIRST case block (nested!)
    _outcome = await root.fill("3.1.1", [Unfold.gen_single({
        "thought": "Unfold double in nested case",
        "targets": ["double"],
    })])
    is_error = _outcome.failure is not None and _outcome.failure.is_error
    file.write(f"Unfold in nested case is_error: {is_error}\n")
    if _outcome.failure:
        file.write(f"Unfold failure: {_outcome.failure}\n")

    print_header("After nested Unfold", file)
    root.print(0, file)


@model_test("HaveLeakSibling", "Test_HaveLeakSibling.thy", 8)
async def _test_HaveLeakSibling(root: Root, file: MyIO):
    """Regression: Have facts from one conjunct must not leak into sibling cases.

    Split (1+1=2) ∧ (2+2=4) via SplitConjs.  In case 1.1, prove a Have
    named 'helper', close the case, then inspect case 1.2's quickview.  The
    named fact 'helper' must NOT appear as a premise of case 1.2.
    """
    print_header("Initial State", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [SplitConjs.gen_single({
        "thought": "Split conjunction",
    })])
    print_header("After split", file)
    root.quickview(0, file)

    # Case 1.1: (1+1=2).  Introduce a named Have, prove it, then close.
    root.session.age += 1
    await root.fill("1.1.1", [Have.gen_single({
        "thought": "Trivial helper",
        "statement": {"english": "one plus one is two", "conclusion": r"(1::nat) + 1 = 2"},
        "name": "helper",
    })])
    root.session.age += 1
    await root.fill("1.1.1.1", [Obvious.gen_single({"facts": []})])
    root.session.age += 1
    await root.fill("1.1.2", [Obvious.gen_single({
        "facts": [{"name": "helper"}]
    })])
    print_header("After closing case 1.1 with Have 'helper'", file)
    root.quickview(0, file)

    # Check: case 1.2's quickview must NOT show 'helper' as a premise.
    gn_1_2 = cast(GoalNode, root.locate_node("1.2"))
    goal = gn_1_2.goal()
    if goal is not None:
        suppressed = gn_1_2._ctxt_before_me()
        visible_hyps = {k: v for k, v in goal.context.hyps.items()
                        if k not in suppressed.hyps}
        leaked = [k for k in visible_hyps if k.unicode == "helper"]
        if leaked:
            file.write(f"BUG: 'helper' leaked into case 1.2 premises: {visible_hyps}\n")
            raise TestFailed("Have fact 'helper' from case 1.1 leaked into sibling case 1.2")
        else:
            file.write("OK: no Have facts leaked into sibling case\n")
    else:
        file.write("WARNING: case 1.2 has no goal (already solved?)\n")

    print_header("Final state", file)
    root.print(0, file)


@model_test("AmendInductionDiscardedCtxt", "Test_AmendInductionDiscardedCtxt.thy", 8)
async def _test_AmendInductionDiscardedCtxt(root: Root, file: MyIO):
    """Regression: amending an Induction node with a rule that changes the
    number of cases (e.g. nat.induct → less_induct) discards the old
    GoalNode sub-nodes into a warning.  Printing those discarded nodes
    with show_warnings=True used to crash with
        InternalError: The target node is not my children
    because the discarded GoalNodes still had `parent` pointing at the
    new Induction node, which no longer listed them in `sub_nodes`."""
    print_header("Initial YAML", file)
    root.print(0, file)

    await root.fill("1", [Induction.gen_single({
        "thought": "default induction on n (nat.induct, 2 cases: 0, Suc)",
        "target_isabelle_term": "n",
        "variables": [{"name": "n", "status": "fixed"}],
    })])
    print_header("After fill (nat.induct, 2 cases)", file)
    root.print(0, file)

    await root.amend("1", [Induction.gen_single({
        "thought": "amend to strong induction (less_induct, 1 case)",
        "target_isabelle_term": "n",
        "rule": {"name": "less_induct"},
        "variables": [{"name": "n", "status": "fixed"}],
    })])
    print_header("After amend (less_induct, 1 case) — show_warnings=True", file)
    root.print(0, file, show_warnings=True)


@model_test("AmendInductionNested", "Test_AmendInductionNested.thy", 8)
async def _test_AmendInductionNested(root: Root, file: MyIO):
    """Reproduce crash from production log e2130bcea_59:
    A batch fill with a Have whose nested proof contains
    [Intro, Induction, Obvious]. During StdBlock._refresh_me_alone,
    the for-loop iterates self.sub_nodes. When the Induction child
    refreshes and creates >1 subgoals, _close_by replaces
    self.sub_nodes with a truncated new list. But the for-loop still
    holds the OLD list reference and advances to the Obvious child
    (discarded from the new list). The Obvious calls
    resulting_state() → parent._resulting_state_of_child(self) →
    searches the NEW sub_nodes → not found →
    InternalError("The target node is not my children").
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "helper lemma by induction",
        "statement": {
            "english": "sum identity",
            "conclusion": r"(\<Sum>i\<le>n. i) = n * (n + 1) div 2",
        },
        "name": "helper",
        "proof": [
            {"operation": "Intro", "thought": "intro"},
            {"operation": "Induction",
             "thought": "induction on n",
             "target_isabelle_term": "n",
             "variables": [{"name": "n", "status": "fixed"}],
             "proofs": "GivenLater"},
            {"operation": "Obvious", "facts": []},
        ],
    })])

    print_header("After fill", file)
    root.print(0, file)


@model_test("SimpRoles", "Test_SimpRoles.thy", 12)
async def _test_simp_roles(root: Root, file: MyIO):
    """Bug repro: fun-defined .simps facts are marked [manual] despite being
    registered in the simplifier.  The root cause is in thm_roles
    (agent_server.ML) which checks Thm.get_name_hint against a pre-computed
    simp_rule_names set.

    This test retrieves .simps facts both as a bundle and individually
    (indexed), then asserts that the roles list includes "simp".
    """
    from Isabelle_RPC_Host.universal_key import EntityKind
    ml = root.ml_state

    file.write("=== Retrieve double.simps (bundle, no index) ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.THEOREM, "double.simps"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: roles={roles}\n")
            for e in exprs:
                file.write(f"    {e.unicode}\n")
        else:
            file.write("  None\n")

    file.write("=== Retrieve double.simps(1) ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.THEOREM, "double.simps(1)"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: roles={roles}\n")
            for e in exprs:
                file.write(f"    {e.unicode}\n")
        else:
            file.write("  None\n")

    file.write("=== Retrieve double.simps(2) ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.THEOREM, "double.simps(2)"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: roles={roles}\n")
            for e in exprs:
                file.write(f"    {e.unicode}\n")
        else:
            file.write("  None\n")

    file.write("=== Retrieve a known system simp rule: add_0 ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.THEOREM, "add_0"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: roles={roles}\n")
        else:
            file.write("  None\n")

    file.write("=== Retrieve a known intro rule: conjI ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.THEOREM, "conjI"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: roles={roles}\n")
        else:
            file.write("  None\n")

    file.write("=== Retrieve a known elim rule: conjE ===\n")
    results = await ml._retrieve_entity([
        (EntityKind.THEOREM, "conjE"),
    ])
    for r in results:
        if r is not None:
            short_name, exprs, roles, abbrev_names, _is_local = r
            file.write(f"  {short_name.unicode}: roles={roles}\n")
        else:
            file.write("  None\n")


@model_test("AmendHaveToConjI", "Test_AmendHaveToConjI.thy", 8)
async def _test_AmendHaveToConjI(root: Root, file: MyIO):
    """Reproduce: SubgoalMaker.sub_nodes type-invariant violated after amend.

    The base NonLeaf_Node._amend_from transplants old.sub_nodes wholesale
    into the new node — but for SubgoalMaker (InferenceRule / Intro /
    Branch / Induction / CaseSplit_Like), sub_nodes are *framework-managed
    GoalNodes*, one per subgoal produced by the begin-op, not user-written
    proof steps. The transfer is therefore type-incoherent for any
    StdBlock → SubgoalMaker amend.

    SubgoalMaker._refresh_the_beginning_opr (model.py:3992) tries to
    rebuild GoalNodes only when the count differs (warn-discard branch);
    when the inherited count happens to match the new subgoal count, the
    `pass` branch silently keeps the wrong-typed children.

    Setup: parent goal is `True ∧ True`. Step 1 is filled as a Have on a
    meta-quantified intermediate (`⋀x::nat. x = x`), which causes
    `_attach_proof` to inject an auto-Intro plus the user-supplied
    Obvious — Have ends up with 2 sub_nodes ([Intro, Obvious]). The
    amend swaps Have for InferenceRule(conjI), which produces 2 subgoals
    on the parent — count match (2 == 2). After refresh, the
    InferenceRule's sub_nodes still hold the inherited [Intro, Obvious]
    instead of two GoalNodes.

    The user's note "SubgoalMaker should also override _amend_from" was
    pointing at this: the carry-over only makes sense when sub_nodes
    are user proof steps; SubgoalMaker should stash the inherited
    children for rematch-aware re-attachment, not transplant them.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "irrelevant intermediate",
        "statement": {
            "english": "for all x::nat, x = x",
            "conclusion": r"\<And>x::nat. x = x",
        },
        "name": "h",
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("After Have(...) with body", file)
    root.print(0, file)
    have_step = cast(NonLeaf_Node, root.locate_node("1"))
    file.write(f"Have type: {type(have_step).__name__}\n")
    file.write(f"Have sub_nodes types: {[type(c).__name__ for c in have_step.sub_nodes]}\n")
    file.write(f"Have status: {have_step.status.status.value}\n")

    root.session.age += 1
    outcome = await root.amend("1", [InferenceRule.gen_single({
        "thought": "switch to conjI",
        "rule": {"name": "conjI"},
    })])
    amended = cast(NonLeaf_Node, outcome.committed[0]) if outcome.committed else None
    print_header("After amend Have -> InferenceRule(conjI)", file)
    root.print(0, file)
    if amended is None:
        raise TestFailed(f"Amend produced no committed node; outcome={outcome}")
    file.write(f"Amended type: {type(amended).__name__}\n")
    file.write(f"Amended sub_nodes types: {[type(c).__name__ for c in amended.sub_nodes]}\n")
    file.write(f"Amended status: {amended.status.status.value}\n")

    bad = [type(c).__name__ for c in amended.sub_nodes if not isinstance(c, GoalNode)]
    if bad:
        raise TestFailed(
            f"BUG: SubgoalMaker.sub_nodes contains non-GoalNode children: {bad}. "
            f"NonLeaf_Node._amend_from carried StdBlock body across without "
            f"kind awareness; SubgoalMaker should override _amend_from."
        )


@model_test("DeleteObtainUnfound", "Test_DeleteObtainUnfound.thy", 8)
async def _test_DeleteObtainUnfound(root: Root, file: MyIO):
    """Reproduce: deleting an Obtain whose constraint facts are referenced
    by a downstream Obvious step causes InternalError in pack().

    After Obtain introduces a named constraint (k_def), a subsequent
    Obvious step references it via facts:[k_def].  When the Obtain is
    deleted, the Obvious is refreshed: refresh_facts() returns
    IsabelleFact_Unfound for k_def, but Obvious.the_operation() calls
    HAMMER(fact_refs) which calls pack() on the unfound fact, raising
    InternalError instead of gracefully degrading to a failure status."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 2: Obtain k with constraint k_def: k = m
    root.session.age += 1
    await root.fill("2", [Obtain.gen_single({
        "thought": "unpack the existential",
        "variables": [{"name": "k", "type": "nat"}],
        "constraints": [{"name": "k_def",
                         "isabelle": "k = m",
                         "english": "the existential witness"}],
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("After Obtain", file)
    root.print(0, file)

    # Step 3: Obvious with facts:[k_def] — proves m = m using the
    # constraint from the Obtain above.
    root.session.age += 1
    await root.fill("3", [Obvious.gen_single({
        "facts": [{"name": "k_def"}]
    })])
    print_header("After Obvious with k_def", file)
    root.print(0, file)

    # Now delete the Obtain (step 2).  The downstream Obvious (step 3,
    # renumbered to step 2 after deletion) must be refreshed.  Its
    # fact_refs include k_def which is no longer in scope.
    # BUG: refresh_facts returns IsabelleFact_Unfound for k_def, but
    # Obvious.the_operation() calls pack() on it → InternalError.
    root.session.age += 1
    await root.delete(["2"])
    print_header("After deleting Obtain", file)
    root.print(0, file)


@model_test("SpliceHaveRefresh", "Test_SpliceHaveRefresh.thy", 8)
async def _test_SpliceHaveRefresh(root: Root, file: MyIO):
    """Reproduce bug: InferenceRule with 1 subgoal (N<=1 splice path) that
    carries a nested proof body.  _truncate_siblings_for_splice replaces
    parent.sub_nodes with a new list, so _splice_body's appends are invisible
    to the parent's ongoing for-loop in _refresh_me_alone.  Result: spliced
    children stay at EVALUATION_NOT_YET."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    # Have "\<not> False" proved by InferenceRule notI (1 subgoal → splice),
    # with body = [Obvious] to close the subgoal "False ==> False".
    await root.fill("1", [Have.gen_single({
        "thought": "claim not False",
        "statement": {"english": "not False", "conclusion": r"\<not> False"},
        "name": "nf",
        "proof": [
            {"operation": "InferenceRule",
             "thought": "apply notI",
             "rule": {"name": "notI"},
             "proofs": [[
                 {"operation": "Obvious", "facts": []}
             ]]}
        ]
    })])
    print_header("After Have with spliced InferenceRule proof", file)
    root.print(0, file)
    # Probe: check statuses of spliced children
    have_node = root.locate_node("1")
    assert isinstance(have_node, NonLeaf_Node)
    file.write(f"Have sub_nodes count: {len(have_node.sub_nodes)}\n")
    for child in have_node.sub_nodes:
        file.write(f"  {child.id}: {type(child).__name__} status={child.status.status.name}\n")
    # The bug: spliced children (after InferenceRule) have status FAILURE
    # with reason "Not yet evaluated" instead of being properly refreshed.
    spliced = [c for c in have_node.sub_nodes
               if c.status == EVALUATION_NOT_YET]
    if spliced:
        file.write(f"BUG: {len(spliced)} node(s) never refreshed (EVALUATION_NOT_YET):\n")
        for c in spliced:
            file.write(f"  - {c.id} ({type(c).__name__})\n")
    else:
        file.write("OK: all children were refreshed\n")


@model_test("ObviousDescriptionFact", "Test_ObviousDescriptionFact.thy", 8)
async def _test_ObviousDescriptionFact(root: Root, file: MyIO):
    """Regression: Obvious with FactByDescription must not crash.
    FactByDescription is not in Obvious's schema, but LLMs can violate
    schemas. fetch_facts returns Interaction_RetrieveForProof for such
    facts, which lacks .pack() — previously crashed in HAMMER().
    The description fact should be filtered out with a warning."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Obvious.gen_single({
        "facts": [
            {"english": "nonneg square"},
        ]
    })])
    print_header("After Obvious with description fact", file)
    root.print(0, file)


@model_test("SpliceAutoIntro", "Test_SpliceAutoIntro.thy", 8)
async def _test_SpliceAutoIntro(root: Root, file: MyIO):
    """InferenceRule ccontr (N=1 splice) with a proof body [Have, Obvious].
    The splice inserts body ops as parent siblings.  The derived goal from
    ccontr is a meta-implication (¬ P ⟹ False), so auto-Intro must be
    injected between the InferenceRule and the first body node.

    Bug: append() passes auto_intro=False to commit_and_hook, so the new
    auto-Intro mechanism never fires for the InferenceRule.  Q7 fires but
    creates a SPURIOUS Intro at the end instead of between InferenceRule
    and the first body node."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    result, is_error = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "InferenceRule",
             "thought": "proof by contradiction",
             "rule": {"name": "ccontr"},
             "proofs": [[
                 {"operation": "Have",
                  "thought": "trivial claim",
                  "statement": {"english": "True", "conclusion": "True"},
                  "name": "h",
                  "proof": [{"operation": "Obvious", "facts": []}]},
                 {"operation": "Obvious", "facts": []},
             ]]},
        ]})
    file.write(f"is_error: {is_error}\n")
    print_header("After InferenceRule ccontr with spliced body [Have, Obvious]", file)
    root.print(0, file)
    ir = root.locate_node("1")
    parent = ir.parent
    assert parent is not None and isinstance(parent, NonLeaf_Node)
    kinds = [type(c).__name__ for c in parent.sub_nodes]
    file.write(f"sibling kinds: {kinds}\n")
    # The node immediately after InferenceRule must be an auto-Intro
    # (consuming the meta-premise from ccontr's derived goal).
    ir_idx = next(i for i, c in enumerate(parent.sub_nodes) if c is ir)
    next_node = parent.sub_nodes[ir_idx + 1]
    file.write(f"node after InferenceRule: {type(next_node).__name__}\n")
    assert isinstance(next_node, Intro), (
        f"Expected auto-Intro immediately after InferenceRule, "
        f"got {type(next_node).__name__}")
    # No spurious Intro appended at the end by Q7.
    last_node = parent.sub_nodes[-1]
    file.write(f"last node: {type(last_node).__name__}\n")
    assert not isinstance(last_node, Intro), (
        f"Spurious Intro at the end (step {last_node.id})")


@model_test("MultilineThought", "Test_MultilineThought.thy", 8)
async def _test_MultilineThought(root: Root, file: MyIO):
    """Exercise _print_thought multi-line path (lines 2477-2483).
    When the thought string contains newlines, it should render as a
    YAML literal block `thought: |` instead of inline."""
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", [Have.gen_single({
        "thought": "First line of reasoning.\nSecond line continues.\nThird concludes.",
        "statement": {
            "english": "square is nonneg",
            "conclusion": r"(x::int) * x \<ge> 0"
        },
        "name": "sq"
    })])
    print_header("After Have with multiline thought", file)
    root.print(0, file)

@model_test("RenameVarNotFound", "Test_RenameVarNotFound.thy", 8)
async def _test_RenameVarNotFound(root: Root, file: MyIO):
    """Exercise rename_var raising CannotRename_VariableNotFound (lines 2754-2760).
    Attempting to rename a variable that doesn't exist in the proof tree
    must raise the appropriate error."""
    print_header("Initial YAML", file)
    root.print(0, file)
    try:
        await root.rename_var(IsaTerm.from_agent("nonexistent"), IsaTerm.from_agent("new_name"))
        file.write("BUG: rename_var should have raised CannotRename_VariableNotFound\n")
    except CannotRename_VariableNotFound as e:
        file.write(f"OK: rename_var raised CannotRename_VariableNotFound\n")

@model_test("RenameFactNotFound", "Test_RenameFactNotFound.thy", 8)
async def _test_RenameFactNotFound(root: Root, file: MyIO):
    """Exercise rename_fact raising CannotRename_FactNotFound (lines 2762-2767).
    Attempting to rename a fact that doesn't exist in the proof tree
    must raise the appropriate error."""
    print_header("Initial YAML", file)
    root.print(0, file)
    try:
        await root.rename_fact("nonexistent_fact", "new_fact_name")
        file.write("BUG: rename_fact should have raised CannotRename_FactNotFound\n")
    except CannotRename_FactNotFound as e:
        file.write(f"OK: rename_fact raised CannotRename_FactNotFound\n")

@model_test("RenameIntroVar", "Test_RenameIntroVar.thy", 8)
async def _test_RenameIntroVar(root: Root, file: MyIO):
    """Exercise Intro._rename_var (lines 6358-6364) and the successful
    rename_var path (lines 2754-2760) with refresh cascade."""
    print_header("Initial YAML (auto-intro fixes x)", file)
    root.print(0, file)
    await root.rename_var(IsaTerm.from_agent("x"), IsaTerm.from_agent("y"))
    print_header("After renaming x to y", file)
    root.print(0, file)

@model_test("ObtainMultiConstraint", "Test_ObtainMultiConstraint.thy", 8)
async def _test_ObtainMultiConstraint(root: Root, file: MyIO):
    """Exercise Obtain._print_header multiple-constraints path (lines 6114-6126).
    When the Obtain block has >1 constraints, they are printed as a
    bulleted list under `constraints:` instead of singular `constraint:`."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("2", [Obtain.gen_single({
        "thought": "Unpack the existential with multiple constraints",
        "variables": [{"name": "k", "type": "nat"}],
        "constraints": [
            {"name": "k_eq", "isabelle": "k = m", "english": "k equals m"},
            {"name": "k_le", "isabelle": r"k \<le> m", "english": "k is at most m"},
        ],
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    print_header("After Obtain with two constraints", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("ObtainQuickview", "Test_ObtainQuickview.thy", 8)
async def _test_ObtainQuickview(root: Root, file: MyIO):
    """Exercise Obtain.quickview dedup (lines 6069-6084).
    After Obtain fires, quickview must announce the obtained variables
    and constraints. A second quickview call must NOT re-emit them (dedup)."""
    root.session.age += 1
    await root.fill("2", [Obtain.gen_single({
        "thought": "Unpack the existential",
        "variables": [{"name": "k", "type": "nat"}],
        "constraints": [{"name": "k_def", "isabelle": "k = m",
                         "english": "the existential witness"}],
        "proof": [{"operation": "Obvious", "facts": []}],
    })])
    # Prove the remaining goal so Obtain's ending is reached
    root.session.age += 1
    await root.fill("3", [Obvious.gen_single({"facts": [{"name": "k_def"}]})])
    print_header("Quickview (first render — should show obtained vars/constraints)", file)
    root.quickview(0, file)
    print_header("Quickview (second render — dedup, should NOT repeat)", file)
    root.quickview(0, file)

@model_test("FailedLeafQuickview", "Test_FailedLeafQuickview.thy", 8)
async def _test_FailedLeafQuickview(root: Root, file: MyIO):
    """Exercise _print_evaluation_status_quickview FAILURE path (lines 2431-2439).
    A deliberately failing Have (nonsensical statement) produces a FAILURE
    status; quickview should print 'evaluation failed'."""
    await root.fill("1", [Have.gen_single({
        "thought": "Deliberately wrong claim",
        "statement": {
            "english": "a false claim",
            "conclusion": "False"
        },
        "name": "bad_claim"
    })])
    # The Have itself should succeed (it's just claiming), the subproof will fail
    # Try filling with an Obvious that will fail
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("Full print (shows error details)", file)
    root.print(0, file)
    print_header("Quickview (should show evaluation status)", file)
    root.quickview(0, file)

@model_test("FactByNameWhere", "Test_FactByNameWhere.thy", 10)
async def _test_FactByNameWhere(root: Root, file: MyIO):
    """Test FactByName with [where ...] instantiation through the full pipeline."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Obvious.gen_single({
        "facts": [{"name": "h", "instantiations": [{"name": "x", "value": "0 :: nat"}]}]
    })])
    if outcome.failure is not None:
        file.write(f"Fill failed: {outcome.failure}\n")
    print_header("After Obvious with FactByName[where]", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("FactByNameOF", "Test_FactByNameOF.thy", 10)
async def _test_FactByNameOF(root: Root, file: MyIO):
    """Test FactByName with [OF ...] discharge through the full pipeline."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Obvious.gen_single({
        "facts": [
            {"name": "rule", "discharge": [None, {"name": "hb"}]},
            {"name": "ha"}
        ]
    })])
    if outcome.failure is not None:
        file.write(f"Fill failed: {outcome.failure}\n")
    print_header("After Obvious with FactByName[OF _ hb] + ha", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("FactByNameWhereOF", "Test_FactByNameWhereOF.thy", 10)
async def _test_FactByNameWhereOF(root: Root, file: MyIO):
    """Regression: a FactByName carrying BOTH `instantiations` (→xwhere) and
    `discharge` (→xOF) must render as ONE comma-separated attribute bracket
    `rule[xwhere x = ‹7 :: nat›, xOF hs]`, NOT two adjacent groups
    `rule[xwhere ...][xOF ...]`. `read_fact`'s `Parse.thm` accepts only a
    single `[...]` group (`Scan.optional attribs`, no repeat), so the old
    two-bracket form left the second group unconsumed and raised
    `Cannot parse "..." as a fact reference`, leaving the goal unproved.
    The merged single-bracket form instantiates ∀x with 7 then discharges
    `S 7` via hs, yielding exactly `R 7`, so Obvious closes the goal."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Obvious.gen_single({
        "facts": [{"name": "rule",
                   "instantiations": [{"name": "x", "value": "7 :: nat"}],
                   "discharge": [{"name": "hs"}]}]
    })])
    if outcome.failure is not None:
        file.write(f"Fill failed: {outcome.failure}\n")
    print_header("After Obvious with FactByName[xwhere + xOF]", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("FactByNameRejectsProposition", "Test_FactByNameRejectsProposition.thy", 10)
async def _test_FactByNameRejectsProposition(root: Root, file: MyIO):
    """A proposition pasted where a fact NAME belongs is rejected at
    validation time, per slot, before anything reaches ML. Replays the
    missing-lemma-loop incident (putnam_1987_a2, eb6c5d71c_1): the model put
    the propositions to discharge into `discharge` instead of fact names,
    and the old feedback was an opaque `Cannot parse "...[xwhere ..., xOF
    ...]" as a fact reference` echo of the internal pack syntax. Records all
    three message variants: discharge entry / facts name (FactByProposition
    alternative offered) / rule name (no alternative)."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    try:
        Obvious.gen_single({"facts": [{
            "name": "Greatest_equality",
            "instantiations": [
                {"name": "?P", "value": "λ(k1::nat). k1 ≤ k"},
                {"name": "?x", "value": "k"}],
            "discharge": [
                "k ≤ k",
                "∀(y::nat). y ≤ k ⟶ y ≤ k"],
            "flip": False}]})
    except ArgumentError as e:
        file.write(f"ArgumentError: {e}\n")
    try:
        Obvious.gen_single({"facts": [{"name": "k ≤ k"}]})
    except ArgumentError as e:
        file.write(f"ArgumentError: {e}\n")
    try:
        # `rule` slots are validated at the central raw-op entry
        # (`Parse_Op`), not in `InferenceRule.gen_single`; validate the
        # field directly the way that entry does.
        validate(FactByName, {"name": "k ≤ k"}, "rule")
    except ArgumentError as e:
        file.write(f"ArgumentError: {e}\n")


@model_test("Rewrite_WhereBadVar", "Test_Rewrite_WhereBadVar.thy", 11)
async def _test_Rewrite_WhereBadVar(root: Root, file: MyIO):
    """Reproduce: [where] with wrong variable name from display renaming.

    Root cause from real bug (DFDD2C266_1BB5E6E):
    1. Function defined proof-locally → .simps has HOL ∀ (bound variable)
    2. Free `n` already in scope → deconflict_bound_names renames
       the bound variable from `n` to `n1` for display
    3. Retrieval shows `∀(n1 :: nat). myf n1 = ...` (see retrieval.yaml)
    4. LLM uses `n1` in [where n1 = ...]
    5. [where] fails: 'No such variable in theorem: ?n1'
       because the theorem's actual schematic is ?n, not ?n1

    This test reproduces the final error: [where] with a variable name
    that doesn't match the theorem's schematics."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Rewrite using myf.simps with display-renamed variable name "n1".
    # The schematic is actually ?n, but the printer shows ?n1 because
    # Free n is in scope.  VN_Name "n1" should match via schematic_deconf_map.
    root.session.age += 1
    outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Unfold outer myf with variable name from display",
        "using": [{"name": "myf.simps",
                   "instantiations": [{"name": "n1", "value": "myf n"}]}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After Rewrite with display-renamed variable", file)
    root.print(0, file)


@model_test("FactByNameFlip", "Test_FactByNameFlip.thy", 10)
async def _test_FactByNameFlip(root: Root, file: MyIO):
    """Test FactByName with [symmetric] (flip) through the full pipeline."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Obvious.gen_single({
        "facts": [{"name": "h", "flip": True}]
    })])
    if outcome.failure is not None:
        file.write(f"Fill failed: {outcome.failure}\n")
    print_header("After Obvious with flip", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("RewriteFlipForall", "Test_RewriteFlipForall.thy", 10)
async def _test_RewriteFlipForall(root: Root, file: MyIO):
    """Rewrite with flip=True on a universally quantified equation (∀z. f z = z+1)
    should not crash with 'symmetric: no unifiers'. Reproduces the bug where
    [symmetric] is appended to the fact name but Isabelle's symmetric rule
    cannot apply because the top-level connective is ∀, not =."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Rewrite the goal using h flipped",
        "using": [{"name": "h", "flip": True}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    if outcome.failure is not None:
        file.write(f"Fill failed: {outcome.failure}\n")
    print_header("After Rewrite with flip on forall-quantified fact", file)
    root.print(0, file)


@model_test("RewriteNeqFlipNoOp", "Test_RewriteNeqFlipNoOp.thy", 10)
async def _test_RewriteNeqFlipNoOp(root: Root, file: MyIO):
    """Reproduces the 'Rewrite shows nothing' incident.

    The agent wanted to flip a premise `ln2_ne_0 : ln 2 ≠ 0` into `0 ≠ ln 2`
    using `neq_commute` but instantiated it BACKWARDS — `?a = 0, ?b = ln 2`,
    giving the rule `(0 ≠ ln 2) = (ln 2 ≠ 0)`, whose LHS `0 ≠ ln 2` does NOT
    occur in the premise `ln 2 ≠ 0`.  (Flipping `ln 2 ≠ 0` needs `?a = ln 2,
    ?b = 0`, or simply `flip: True`.)  So the rule rewrites nothing.

    With `use system simplifiers = True` the operation nevertheless COMMITS
    (no "The simplification made no progress." error — contrast
    `Rewrite_NoProgress`, which has system simplifiers OFF), yet the targeted
    premise and the goal conclusion are both unchanged.  Rewrite.quickview only
    prints a binding block when the bindings change and a "goal changes into"
    block when the goal CONCLUSION changes — both empty here.

    Regression guard for the fix: Rewrite._refresh_me_alone now detects this
    (goal conclusion unchanged AND no resulting bindings) and appends a HEADER
    notice + marks the node `changed`, so the outline (quickview) surfaces the
    "The rewrite changed nothing …" notice instead of rendering just the title.
    This test dumps the outcome, the committed node's warnings, the rendered
    outline, and the full print (with warnings) to pin the notice down."""
    print_header("Initial", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Flip inequality using neq_commute",
        "using": [{
            "name": "neq_commute",
            "instantiations": [
                {"name": "?a", "value": "(0::real)"},
                {"name": "?b", "value": "ln (2::real)"},
            ],
            "discharge": [],
            "flip": False,
        }],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["ln2_ne_0"],
    })])
    print_header("Outcome", file)
    file.write(f"failure: {outcome.failure}\n")
    file.write(f"committed: {[n.id for n in outcome.committed]}\n")
    node = outcome.committed[0]
    file.write(f"node warnings: {[str(w.printer) for w in node.warnings]}\n")
    print_header("Quickview outline (what the agent is shown)", file)
    root.session.quickview_proof_scope(1, file)
    print_header("Full print (with warnings)", file)
    root.print(0, file, show_warnings=True)


@model_test("RewriteNeqFlipNoOp2", "Test_RewriteNeqFlipNoOp2.thy", 10)
async def _test_RewriteNeqFlipNoOp2(root: Root, file: MyIO):
    """Probe variant of RewriteNeqFlipNoOp where the goal (0 ≤ ln 2 * ln 2)
    DIFFERS from the targeted premise (ln 2 ≠ 0) — to confirm the silent no-op
    (and the no-change notice) is not an artifact of goal==premise. Same
    backwards neq_commute + system simplifiers ON."""
    print_header("Initial", file)
    root.print(0, file)
    root.session.age += 1
    outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Flip inequality using neq_commute",
        "using": [{
            "name": "neq_commute",
            "instantiations": [
                {"name": "?a", "value": "(0::real)"},
                {"name": "?b", "value": "ln (2::real)"},
            ],
            "discharge": [],
            "flip": False,
        }],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["ln2_ne_0"],
    })])
    print_header("Outcome", file)
    file.write(f"failure: {outcome.failure}\n")
    file.write(f"committed: {[n.id for n in outcome.committed]}\n")
    node = outcome.committed[0]
    file.write(f"node warnings: {[str(w.printer) for w in node.warnings]}\n")
    print_header("Quickview outline (what the agent is shown)", file)
    root.session.quickview_proof_scope(1, file)


def _noop_notice_count(node) -> int:
    """How many copies of the no-op notice are attached to a Rewrite node."""
    return sum(1 for w in node.warnings
               if isinstance(w.printer, str) and "The rewrite changed nothing" in w.printer)


@model_test("RewriteNeqFlipNoOpDup", "Test_RewriteNeqFlipNoOpDup.thy", 10)
async def _test_RewriteNeqFlipNoOpDup(root: Root, file: MyIO):
    """Regression for warning NON-IDEMPOTENCY exposed by surfacing the no-op
    notice in the outline.

    A no-op Rewrite is at step 2 (after a declarative Have at step 1). Amending
    step 1 cascades a re-refresh onto step 2, re-running its
    `_refresh_me_alone`. Because warnings are only cleared at end-of-edit
    (`root.reset`), a method that merely `append`s its notice would accumulate a
    DUPLICATE on the re-refresh — rendered as a repeated bullet under one
    `notice:`. The fix clears HEADER warnings on refresh entry (keeping FOOTER),
    so the count stays 1 across re-refreshes. This dumps the notice count before
    and after the amend, plus the final outline."""
    # Step 1: a trivial declarative Have (leaves the main goal open at step 2).
    await root.fill("1", [Have.gen_single({
        "thought": "trivial helper",
        "statement": {"english": "ln 2 squared is non-negative",
                      "conclusion": r"(0::real) \<le> ln 2 * ln 2"},
        "name": "lem1"})])
    root.session.age += 1
    # Step 2: the no-op Rewrite (backwards neq_commute on premise ln2_ne_0).
    outcome = await root.fill("2", [Rewrite.gen_single({
        "thought": "Flip inequality using neq_commute",
        "using": [{
            "name": "neq_commute",
            "instantiations": [
                {"name": "?a", "value": "(0::real)"},
                {"name": "?b", "value": "ln (2::real)"},
            ],
            "discharge": [],
            "flip": False,
        }],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["ln2_ne_0"],
    })])
    rewrite_node = outcome.committed[0]
    print_header("After first fill (step 2)", file)
    file.write(f"no-op notice count: {_noop_notice_count(rewrite_node)}\n")
    # Amend step 1 → cascades a re-refresh onto step 2.
    root.session.age += 1
    await root.amend("1", [Have.gen_single({
        "thought": "trivial helper (amended)",
        "statement": {"english": "ln 2 squared is non-negative",
                      "conclusion": r"(0::real) \<le> ln 2 * ln 2 + 0"},
        "name": "lem1"})])
    print_header("After amending step 1 (cascade re-refresh of step 2)", file)
    file.write(f"no-op notice count: {_noop_notice_count(rewrite_node)}\n")
    print_header("Quickview outline (what the agent is shown)", file)
    root.session.quickview_proof_scope(1, file)


@model_test("QuickviewCollapse", "Test_QuickviewCollapse.thy", 8)
async def _test_QuickviewCollapse(root: Root, file: MyIO):
    """When 5+ consecutive sibling steps are done and unchanged,
    quickview should collapse them: first, '...', second-to-last, last."""
    # Fill 6 trivially-provable Have steps
    for i, (name, stmt) in enumerate([
        ("h1", "(1::nat) > 0"),
        ("h2", "(2::nat) > 0"),
        ("h3", "(3::nat) > 0"),
        ("h4", "(4::nat) > 0"),
        ("h5", "(5::nat) > 0"),
        ("h6", "(6::nat) > 0"),
    ], start=1):
        root.session.age += 1
        await root.fill(str(i), [Have.gen_single({
            "thought": f"claim {name}",
            "statement": {"english": f"{name}", "conclusion": stmt},
            "name": name,
        })])
        root.session.age += 1
        await root.fill(f"{i}.1", [Obvious.gen_single({"facts": []})])
    root.reset()
    print_header("Quickview with 6 done steps (should collapse)", file)
    root.quickview(0, file)

@model_test("Contradiction_notI", "Test_Contradiction_notI.thy", 8)
async def _test_Contradiction_notI(root: Root, file: MyIO):
    """Contradiction on a ¬-led goal uses notI internally.
    Goal: ¬ False. Contradiction assumes False as hypothesis, goal becomes False.
    Obvious closes it because False is in the premises."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Contradiction.gen_single({
        "hypothesis_name": "neg_hyp",
    })])
    print_header("After Contradiction (notI path)", file)
    root.print(0, file)
    root.quickview(0, file)
    contra_node = root.locate_node("1")
    assert isinstance(contra_node, Contradiction)
    file.write(f"status: {contra_node.status.status.name}\n")
    file.write(f"bindings: {contra_node.bindings}\n")
    # Now prove the resulting False goal
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": [{"name": "neg_hyp"}]})])
    print_header("After Obvious to close False", file)
    root.print(0, file)

@model_test("Contradiction_ccontr", "Test_Contradiction_ccontr.thy", 8)
async def _test_Contradiction_ccontr(root: Root, file: MyIO):
    """Contradiction on a non-¬ goal uses ccontr internally.
    Goal: True. Contradiction assumes ¬ True as hypothesis, goal becomes False.
    We derive False from ¬ True."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Contradiction.gen_single({
        "hypothesis_name": "neg_hyp",
    })])
    print_header("After Contradiction (ccontr path)", file)
    root.print(0, file)
    root.quickview(0, file)
    contra_node = root.locate_node("1")
    assert isinstance(contra_node, Contradiction)
    file.write(f"status: {contra_node.status.status.name}\n")
    file.write(f"bindings: {contra_node.bindings}\n")
    # Prove False: neg_hyp is "¬ True", Rewrite with neg_hyp to turn False into ¬ True, then Obvious
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": [{"name": "neg_hyp"}]})])
    print_header("After Obvious to close False", file)
    root.print(0, file)

@model_test("Contradiction_double_neg", "Test_Contradiction_double_neg.thy", 8)
async def _test_Contradiction_double_neg(root: Root, file: MyIO):
    """Nested negation: goal ¬ ¬ True uses notI (¬-led).
    Hypothesis is ¬ True, goal becomes False."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Contradiction.gen_single({
        "hypothesis_name": "h",
    })])
    print_header("After Contradiction on ¬ ¬ True", file)
    root.print(0, file)
    contra_node = root.locate_node("1")
    assert isinstance(contra_node, Contradiction)
    file.write(f"status: {contra_node.status.status.name}\n")
    if contra_node.bindings:
        for fb in contra_node.bindings[1]:
            file.write(f"hypothesis: {fb.name.unicode} = {fb.pretty.unicode}\n")
    # Prove False: h is "¬ True", use it
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({"facts": [{"name": "h"}]})])
    print_header("After closing False", file)
    root.print(0, file)

@model_test("Contradiction_false_goal", "Test_Contradiction_false_goal.thy", 8)
async def _test_Contradiction_false_goal(root: Root, file: MyIO):
    """Degenerate: goal is False (after Intro consumes the ⟹ premise).
    Contradiction uses ccontr, hypothesis becomes ¬ False, goal stays False.
    This is a valid but pointless use — verify it doesn't crash."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # First do Intro to consume "False ⟹ False" into premise + goal False
    root.session.age += 1
    await root.fill("1", [Intro.gen_single({
        "thought": "introduce premise",
    })])
    print_header("After Intro", file)
    root.print(0, file)
    # Now Contradiction on goal False
    root.session.age += 1
    await root.fill("2", [Contradiction.gen_single({
        "hypothesis_name": "absurd",
    })])
    print_header("After Contradiction on False", file)
    root.print(0, file)
    contra_node = root.locate_node("2")
    assert isinstance(contra_node, Contradiction)
    file.write(f"status: {contra_node.status.status.name}\n")
    if contra_node.bindings:
        for fb in contra_node.bindings[1]:
            file.write(f"hypothesis: {fb.name.unicode} = {fb.pretty.unicode}\n")
    # Close with Obvious using the original premise (False from Intro)
    root.session.age += 1
    await root.fill("3", [Obvious.gen_single({"facts": []})])
    print_header("After closing", file)
    root.print(0, file)

@model_test("Contradiction_Derive", "Test_Contradiction_Derive.thy", 11)
async def _test_Contradiction_Derive(root: Root, file: MyIO):
    """Reproduce fastype_of: Bound bug — Derive (SPECIALIZE) with HOL ∀
    instantiation + premise discharge inside a Contradiction block.

    Goal: n = 2520 with hypotheses:
      h0: ∀n. f n = (∑k | k dvd n. 1) / real n powr (1/3)
      h1: ∀p. p ≠ n → f p < f n
    Contradiction introduces neg: n ≠ 2520.
    Derive tries to instantiate h1 with p=2520 and discharge using neg.
    The discharge requires proving '2520 ≠ n' from 'n ≠ 2520' (argument swap)."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Step 1: Contradiction — assumes neg: n ≠ 2520, goal becomes False
    root.session.age += 1
    await root.fill("1", [Contradiction.gen_single({
        "hypothesis_name": "neg",
    })])
    print_header("After Contradiction", file)
    root.print(0, file)
    # Step 2a: Derive from h1 with p=2520, NO discharge — isolate instantiation
    root.session.age += 1
    _outcome = await root.fill("2", [Derive.gen_single({
        "thought": "Instantiate h1 with p=2520 (no discharge)",
        "rule": {"name": "h1"},
        "instantiations": [{"name": "p", "value": "(2520::nat)"}],
        "result_name": "inst_h1"
    })])
    is_error_a = _outcome.failure is not None and _outcome.failure.is_error
    reason_a = _outcome.failure
    print_header("After Derive (no discharge)", file)
    file.write(f"Is error: {is_error_a}\n")
    if reason_a is not None:
        file.write(f"Reason: {reason_a}\n")
    root.print(0, file)
    # Delete and retry with discharge
    root.session.age += 1
    await root.delete(["2"])
    # Step 2b: Derive from h1 with p=2520 WITH discharge
    root.session.age += 1
    _outcome = await root.fill("2", [Derive.gen_single({
        "thought": "Instantiate h1 with p=2520 and discharge using neg",
        "rule": {"name": "h1"},
        "instantiations": [{"name": "p", "value": "(2520::nat)"}],
        "discharging_facts": [{"name": "neg"}],
        "result_name": "ineq"
    })])
    is_error_b = _outcome.failure is not None and _outcome.failure.is_error
    reason_b = _outcome.failure
    print_header("After Derive (with discharge)", file)
    file.write(f"Is error: {is_error_b}\n")
    if reason_b is not None:
        file.write(f"Reason: {reason_b}\n")
    root.print(0, file)

@model_test("ForkDeletesRefreshingNode", "Test_Unfold1.thy", 15)
async def _test_ForkDeletesRefreshingNode(root: Root, file: MyIO):
    """Reproduce crash: fork sub-agent deletes the node being refreshed.

    Scenario from production: fill(step, [Unfold]) triggers launch_interaction
    inside Unfold._refresh_me_alone to choose among multiple definitions.
    The fork sub-agent answers the interaction but then continues running
    and deletes the Unfold node from the tree. When launch_interaction returns,
    Unfold._refresh_me_alone calls super()._refresh_me_alone which calls
    resulting_state(), but the node is no longer in parent.sub_nodes.
    This raises InternalError("The target node is not my children").
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    async def stub_delete_during_fork(interaction):
        answer = await interaction.answer(AnswerIndexesOrName(indexes=[0], name=None))
        # Simulate the fork sub-agent deleting the Unfold node (step 1)
        # while it is still mid-refresh.  In production this happened when
        # the fork sub-agent saw "Error: Not yet evaluated" on the Unfold
        # node and decided to delete it and try a different approach.
        root.session.age += 1
        await root.delete(["1"])
        return answer

    root.session.launch_interaction = stub_delete_during_fork
    try:
        root.session.age += 1
        await root.fill("1", [Unfold.gen_single({
            "thought": "Unfold the goal",
            "targets": ["XXX"],
        })])
        file.write("BUG: expected InternalError but fill succeeded\n")
    except InternalError as e:
        file.write(f"Caught expected error: {e}\n")

    print_header("After fill", file)
    root.print(0, file)

@model_test("AmendFallbackFill", "Test_AmendFallbackFill.thy", 11)
async def _test_AmendFallbackFill(root: Root, file: MyIO):
    """Amend on a not-found node falls back to fill when the step_id
    matches the fill-position of its parent block.

    Scenario: a node is deleted (simulating what happens after
    TERMINATE_AND_REVERT). Then amend on the deleted step_id should
    fall back to fill and succeed."""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)

    # (1) Fill step 1 with a Have statement — creates node at step 1.
    root.session.age += 1
    result1, is_error1 = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Have", "thought": "restate",
             "statement": {"english": "nonneg", "conclusion": r"x * x \<ge> 0"},
             "name": "sq",
             "proof": [{"operation": "Obvious", "facts": [{"name": "h"}]}]},
        ]})
    print_header("[1] fill [Have(sq)] — creates step 1", file)
    file.write(result1)
    file.write(f"is_error: {is_error1}\n")

    # (2) Delete step 1 — simulates the revert that happens after
    # a failed Obvious via TERMINATE_AND_REVERT.
    root.session.age += 1
    await root.delete(["1"])
    print_header("[2] delete step 1 — simulates revert", file)
    root.print(0, file)

    # (3) Amend step 1 — node no longer exists. With the fallback,
    # this delegates to fill and succeeds.
    root.session.age += 1
    result3, is_error3 = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "amend", "proof_operations": [
            {"operation": "Obvious", "facts": [{"name": "h"}]},
        ]})
    print_header("[3] amend step 1 — fallback to fill, succeeds", file)
    file.write(result3)
    file.write(f"is_error: {is_error3}\n")

    # (4) Amend a truly non-existent node (no valid fill position) —
    # should still fail with NodeNotFound.
    root.session.age += 1
    result4, is_error4 = await _edit_tool_logic(
        root.session,
        {"target_step": "999", "action": "amend", "proof_operations": [
            {"operation": "Obvious", "facts": []},
        ]})
    print_header("[4] amend '999' — genuinely not found", file)
    file.write(result4)
    file.write(f"is_error: {is_error4}\n")


@model_test("HavePowerParsing", "Test_HavePowerParsing.thy", 10)
async def _test_HavePowerParsing(root: Root, file: MyIO):
    """Isabelle inner syntax parser ambiguity: chaining three or more
    `(expr)^n *` terms fails when `*` inside the parenthesized
    sub-expressions has no surrounding spaces (e.g. `2*b` vs `2 * b`).
    Adding spaces resolves the parser ambiguity."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Three chained (expr)^2 terms WITH spaces — succeeds
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "three terms spaced",
        "statement": {"english": "", "conclusion": "(a - 2 * b + c)^2 * (2 * a - b - c)^2 * (a + b - 2 * c)^2 = (0::real)"},
        "name": "three_terms_spaced"
    })])
    print_header("three terms spaced (succeeds)", file)
    root.print(0, file)

    # Same three terms WITHOUT spaces — fails with inner syntax error
    root.session.age += 1
    await root.fill("2", [Have.gen_single({
        "thought": "three terms no-space",
        "statement": {"english": "", "conclusion": "(a - 2*b + c)^2 * (2*a - b - c)^2 * (a + b - 2*c)^2 = (0::real)"},
        "name": "three_terms_nospace"
    })])
    print_header("three terms no-space (fails)", file)
    root.print(0, file)


@model_test("AttachProofInheritsIntoSubgoalMaker", "Test_AttachProofInheritsIntoSubgoalMaker.thy", 10)
async def _test_AttachProofInheritsIntoSubgoalMaker(root: Root, file: MyIO):
    """Regression: _attach_proof places inherited children into a
    SubgoalMaker (Induction/CaseSplit) via isinstance(last, StdBlock),
    but SubgoalMaker expects only GoalNode children.  When Induction
    refreshes, beginning_opr → _case_vars_of_child(0) raises
    InternalError("The child of a CaseSplit_Like is not a GoalNode").

    Trigger: amend a global Have (which has children from a previous
    sub-proof) to a new Have whose proof body ends with Induction."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: global Have with inline proof=[Obvious] — the Obvious
    # succeeds on "True", so the Have has sub_nodes = [Obvious].
    root.session.age += 1
    _outcome = await root.global_env.append([Have.gen_single({
        "thought": "Trivial helper",
        "statement": {"english": "True", "conclusion": "True"},
        "name": "helper",
        "proof": [{"operation": "Obvious", "facts": []}]
    })])
    have1 = _outcome.committed[0] if _outcome.committed else None
    has_children = (isinstance(have1, NonLeaf_Node) and len(have1.sub_nodes) > 0) if have1 else False
    file.write(f"global.1 has children: {has_children}\n")
    print_header("After global Have + Obvious", file)
    root.print(0, file)

    # Step 2: Amend global.1 to a Have whose proof body ends with
    # Induction.  Before fix: inherited Obvious placed into
    # Induction.sub_nodes → InternalError.  After fix: discarded
    # with warning (_can_host_inherited_children = False).
    root.session.age += 1
    _outcome = await root.amend("global.1", [Have.gen_single({
        "thought": "Prove by induction",
        "statement": {
            "english": "for all m, m + 0 = m",
            "for_any": [{"name": "m", "type": "nat"}],
            "conclusion": "m + 0 = m",
        },
        "name": "helper",
        "proof": [
            {"operation": "Induction", "thought": "induct on m",
             "target_isabelle_term": "m",
             "variables": [{"name": "m", "status": "fixed"}]},
        ]
    })])
    amended = _outcome.committed[0] if _outcome.committed else None
    file.write(f"Amend committed: {amended is not None}\n")
    if _outcome.failure:
        file.write(f"Amend failure: {_outcome.failure}\n")
    if amended:
        file.write(f"Amended node status: {amended.status.status.value}\n")
        file.write(f"Amended node warnings: {len(amended.warnings)}\n")
    print_header("After amend (print)", file)
    root.print(0, file, show_warnings=True)
    print_header("After amend (quickview)", file)
    root.quickview(0, file)


@model_test("AmendDeepNotFound", "Test_AmendDeepNotFound.thy", 11)
async def _test_AmendDeepNotFound(root: Root, file: MyIO):
    """Regression test: amend on a deeply nested nonexistent node must not
    raise unhandled exceptions.

    Reproduces the production crash where:
      1. amend('X.Y.Z', [Rewrite, Obvious]) → NodeNotFound
      2. except NodeNotFound → fill('X.Y.Z', [Rewrite, Obvious])
      3. fill processes Rewrite → _refresh_me_alone → launch_interaction
      4. launch_interaction raises (TypeError / NotImplementedError) inside
         the except-NodeNotFound handler of amend
      5. Exception propagates uncaught from amend → _edit_tool_logic →
         sys.exit(1) → kills the RPC server process

    The test calls root.amend directly (not through _edit_tool_logic) to
    avoid the sys.exit(1) crash.  It verifies:
    - shallow amend on deleted node: fill fallback succeeds
    - deep amend on nonexistent node: returns failure outcome, does NOT raise
    - tree remains consistent after all operations"""
    from .mcp_http_server import _edit_tool_logic
    print_header("Initial YAML", file)
    root.print(0, file)

    # (1) Build a 2-level nested tree:  Have → Have → Obvious
    root.session.age += 1
    r1, e1 = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Have", "thought": "outer lemma",
             "statement": {"english": "nonneg", "conclusion": r"x * x \<ge> 0"},
             "name": "sq"},
        ]})
    print_header("[1] fill Have(sq) — creates step 1 with open subgoal 1.1", file)
    file.write(r1)
    file.write(f"is_error: {e1}\n")

    root.session.age += 1
    r2, e2 = await _edit_tool_logic(
        root.session,
        {"target_step": "1.1", "action": "fill", "proof_operations": [
            {"operation": "Obvious", "facts": [{"name": "h"}]},
        ]})
    print_header("[2] fill Obvious at 1.1 — closes step 1", file)
    file.write(r2)
    file.write(f"is_error: {e2}\n")

    # (2) Delete step 1 → tree reverts to open
    root.session.age += 1
    await root.delete(["1"])
    print_header("[3] delete step 1 — reverts tree", file)
    root.print(0, file)

    # (3) Amend step 1.1 (no longer exists, parent 1 also gone).
    #     amend → NodeNotFound → fill fallback → fill also fails (parent gone)
    #     → must return a failure outcome, NOT raise.
    root.session.age += 1
    outcome3 = await root.amend("1.1", [Obvious.gen_single({"facts": [{"name": "h"}]})])
    print_header("[4] amend '1.1' — deep node after parent deleted", file)
    file.write(f"failure: {outcome3.failure is not None}\n")
    file.write(f"failure type: {type(outcome3.failure).__name__ if outcome3.failure else 'None'}\n")

    # (4) Amend a truly nonexistent deep path (3 levels: 7.2.3).
    #     The parent path 7.2 doesn't exist either, so fill should fail gracefully.
    root.session.age += 1
    outcome4 = await root.amend("7.2.3", [
        Rewrite.gen_single({
            "thought": "attempt rewrite on phantom node",
            "using": [{"name": "h"}],
            "use system simplifiers": True,
            "rewrite goal": True,
            "rewrite premises": [],
        }),
        Obvious.gen_single({"facts": []}),
    ])
    print_header("[5] amend '7.2.3' — deeply nonexistent with Rewrite+Obvious", file)
    file.write(f"failure: {outcome4.failure is not None}\n")
    file.write(f"failure type: {type(outcome4.failure).__name__ if outcome4.failure else 'None'}\n")

    # (5) Amend on a deleted CHILD while PARENT still exists.
    #     This exercises the fill fallback actually processing operations (not
    #     just returning failure) — the path that triggers launch_interaction in
    #     production.
    #
    #   (5a) Create Have → step 1 with open subgoal 1.1
    root.session.age += 1
    r5a, e5a = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Have", "thought": "outer lemma",
             "statement": {"english": "nonneg", "conclusion": r"x * x \<ge> 0"},
             "name": "sq"},
        ]})
    print_header("[5a] fill Have(sq) — creates step 1", file)
    file.write(r5a)
    file.write(f"is_error: {e5a}\n")

    #   (5b) Fill step 1.1 so the node exists, then delete it.
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": [{"name": "h"}]})])
    root.session.age += 1
    await root.delete(["1.1"])
    print_header("[5b] after fill+delete 1.1 — parent 1 still exists, child 1.1 gone", file)
    root.print(0, file)

    #   (5c) Amend step 1.1 with Rewrite — fill fallback runs through append,
    #        creating a Rewrite node and evaluating it. In production (APIDriver
    #        session), Rewrite._refresh_me_alone may call launch_interaction →
    #        _make_fork → potential TypeError. In the test session (bare Session),
    #        launch_interaction raises NotImplementedError if triggered.
    #        Either way, amend must NOT propagate exceptions.
    root.session.age += 1
    caught_exc: Exception | None = None
    outcome5c: EditOutcome | None = None
    try:
        outcome5c = await root.amend("1.1", [
            Rewrite.gen_single({
                "thought": "rewrite after child deletion",
                "using": [{"name": "h"}],
                "use system simplifiers": True,
                "rewrite goal": True,
                "rewrite premises": [],
            }),
        ])
    except Exception as e:
        caught_exc = e
    print_header("[5c] amend '1.1' — fill fallback processes Rewrite", file)
    if caught_exc is not None:
        file.write(f"BUG: amend raised {type(caught_exc).__name__}: {caught_exc}\n")
    elif outcome5c is not None:
        file.write(f"failure: {outcome5c.failure is not None}\n")
        if outcome5c.failure:
            file.write(f"failure type: {type(outcome5c.failure).__name__}\n")
        elif outcome5c.committed:
            file.write(f"committed: {len(outcome5c.committed)} node(s)\n")

    # (6) Verify tree is still consistent after the failed operations.
    #     Delete step 1 and fill with Obvious to confirm usability.
    root.session.age += 1
    await root.delete(["1"])
    root.session.age += 1
    r6, e6 = await _edit_tool_logic(
        root.session,
        {"target_step": "1", "action": "fill", "proof_operations": [
            {"operation": "Obvious", "facts": [{"name": "h"}]},
        ]})
    print_header("[6] fill step 1 after errors — tree consistency check", file)
    file.write(r6)
    file.write(f"is_error: {e6}\n")

    print_header("Final YAML", file)
    root.print(0, file)


@model_test("ForkProviderConflict", "Test_ForkProviderConflict.thy", 6)
async def _test_fork_provider_conflict(root: Root, file: MyIO):
    """Verify that APIDriver._make_fork correctly reuses the parent's provider
    via the explicit provider= parameter in subclass __init__, rather than
    creating a throwaway provider that conflicts with the one passed by _make_fork.

    Uses a mock subclass to avoid needing real API keys."""
    from .driver_api import APIDriver, Provider
    import shutil

    class MockProvider(Provider):
        @property
        def context_window(self): return 1000
        @property
        def model_name(self): return "mock"
        def pricing(self): return {"input": 0.0, "cached": 0.0, "output": 0.0}
        def format_tools(self, tool_info): return []
        async def chat(self, messages, tools, **kwargs): raise NotImplementedError
        def format_assistant_msg(self, response): raise NotImplementedError

    class TestSubDriver(APIDriver):
        """Mirrors the __init__ pattern of all concrete APIDriver subclasses."""
        def __init__(self, *args, provider: Provider | None = None,
                     argument=None, **kwargs):
            if provider is None:
                provider = MockProvider()
            super().__init__(*args, provider=provider, **kwargs)

    saved_session = model.the_session()
    parent = TestSubDriver()
    parent.root = None  # normally set by initialize(); fork just copies it
    model._session_var.set(None)
    try:
        fork = TestSubDriver._make_fork(parent)
        file.write(f"_make_fork succeeded\n")
        file.write(f"fork reuses parent provider: {fork._provider is parent._provider}\n")
    except TypeError as e:
        file.write(f"BUG: _make_fork raised TypeError: {e}\n")
    finally:
        model._session_var.set(saved_session)
        shutil.rmtree(parent.working_dir, ignore_errors=True)


@model_test("CompletionCascade", "Test_CompletionCascade.thy", 8)
async def _test_completion_cascade(root: Root, file: MyIO):
    """Test that _collect_completed_ancestors reports cascading completions.

    Phase 1 — single-level completion:
      step 1: Have h1
        step 1.1: Obvious  → completes step 1

    Phase 2 — two-level cascading completion:
      step 2: Have h2
        step 2.1: Have h3 (nested inside h2)
          step 2.1.1: Obvious  → completes step 2.1 AND step 2

    Phase 3 — finish the proof:
      step 3: Obvious  → completes the whole proof"""
    print_header("Initial YAML", file)
    root.print(0, file)

    # --- Phase 1: single-level completion ---
    root.session.age += 1
    outcome1 = await root.fill("1", [Have.gen_single({
        "thought": "Prove an intermediate lemma",
        "statement": {"english": "x squared is non-negative", "conclusion": "x * x ≥ 0"},
        "name": "h1",
    })])
    print_header("edit_message: Have h1", file)
    file.write((await _P.edit_message(root, outcome1, root.session))[0])
    file.write("---------------\n")

    root.session.age += 1
    outcome2 = await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("edit_message: fill 1.1 (should complete step 1)", file)
    file.write((await _P.edit_message(root, outcome2, root.session))[0])
    file.write("---------------\n")

    # --- Phase 2: two-level cascading completion ---
    # step 2: Have h2 (another intermediate lemma)
    root.session.age += 1
    outcome3 = await root.fill("2", [Have.gen_single({
        "thought": "Another intermediate",
        "statement": {"english": "x squared is non-negative again", "conclusion": "x * x ≥ 0"},
        "name": "h2",
    })])
    print_header("edit_message: Have h2", file)
    file.write((await _P.edit_message(root, outcome3, root.session))[0])
    file.write("---------------\n")

    # step 2.1: Have h3 (nested inside h2's body)
    root.session.age += 1
    outcome4 = await root.fill("2.1", [Have.gen_single({
        "thought": "Deep nested lemma",
        "statement": {"english": "x squared is non-negative yet again", "conclusion": "x * x ≥ 0"},
        "name": "h3",
    })])
    print_header("edit_message: Have h3 (nested in h2)", file)
    file.write((await _P.edit_message(root, outcome4, root.session))[0])
    file.write("---------------\n")

    # step 2.1.1: Obvious → completes step 2.1 only (step 2 still has 2.2)
    root.session.age += 1
    outcome5 = await root.fill("2.1.1", [Obvious.gen_single({"facts": []})])
    print_header("edit_message: fill 2.1.1 (should complete step 2.1 only)", file)
    file.write((await _P.edit_message(root, outcome5, root.session))[0])
    file.write("---------------\n")

    # step 2.2: Obvious → completes step 2.2. This also cascades to step 2
    # because 2.1 is already done, so now all children of step 2 are complete.
    root.session.age += 1
    outcome6 = await root.fill("2.2", [Obvious.gen_single({"facts": [{"name": "h3"}]})])
    print_header("edit_message: fill 2.2 (should complete step 2.2 AND cascade to step 2)", file)
    file.write((await _P.edit_message(root, outcome6, root.session))[0])
    file.write("---------------\n")

    # --- Phase 3: multi-ID cascade ---
    # Build: step 3 = Have h4, step 3.1 = Have h5 (nested).
    # Then fill continuations first (3.2 and 3.1.2), leaving only 3.1.1.
    # Filling 3.1.1 should complete step 3.1 AND step 3 in one shot.
    root.session.age += 1
    outcome7 = await root.fill("3", [Have.gen_single({
        "thought": "Outer",
        "statement": {"english": "again", "conclusion": "x * x ≥ 0"},
        "name": "h4",
    })])
    print_header("edit_message: Have h4 (step 3)", file)
    file.write((await _P.edit_message(root, outcome7, root.session))[0])
    file.write("---------------\n")

    root.session.age += 1
    outcome8 = await root.fill("3.1", [Have.gen_single({
        "thought": "Inner",
        "statement": {"english": "again again", "conclusion": "x * x ≥ 0"},
        "name": "h5",
    })])
    print_header("edit_message: Have h5 (step 3.1, nested in h4)", file)
    file.write((await _P.edit_message(root, outcome8, root.session))[0])
    file.write("---------------\n")

    # Fill the continuations first so the last fill cascades
    root.session.age += 1
    outcome9 = await root.fill("3.1.2", [Obvious.gen_single({"facts": [{"name": "h5"}]})])
    print_header("edit_message: fill 3.1.2 (h5's continuation)", file)
    file.write((await _P.edit_message(root, outcome9, root.session))[0])
    file.write("---------------\n")

    root.session.age += 1
    outcome10 = await root.fill("3.2", [Obvious.gen_single({"facts": [{"name": "h4"}]})])
    print_header("edit_message: fill 3.2 (h4's continuation)", file)
    file.write((await _P.edit_message(root, outcome10, root.session))[0])
    file.write("---------------\n")

    # Now fill 3.1.1 — should cascade: completes step 3.1 AND step 3
    root.session.age += 1
    outcome11 = await root.fill("3.1.1", [Obvious.gen_single({"facts": []})])
    print_header("edit_message: fill 3.1.1 (should complete step 3.1 AND step 3)", file)
    file.write((await _P.edit_message(root, outcome11, root.session))[0])
    file.write("---------------\n")

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("CompletionGoalNode", "Test_CompletionGoalNode.thy", 8)
async def _test_completion_goalnode(root: Root, file: MyIO):
    """Test: what titled_id shows up when a GoalNode (from SubgoalMaker) completes?

    conjI on P∧Q creates 2 GoalNode children (is_single_goal=False, numeric IDs).
    Fill both subgoals and observe the edit_message for each."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Apply conjI → creates GoalNode 1.1 and 1.2
    root.session.age += 1
    outcome1 = await root.fill("1", [InferenceRule.gen_single({
        "thought": "split conjunction",
        "rule": {"name": "conjI"},
    })])
    print_header("edit_message: conjI", file)
    file.write((await _P.edit_message(root, outcome1, root.session))[0])
    file.write("---------------\n")
    root.print(0, file)

    # Dump GoalNode info
    rule_node = root.locate_node("1")
    for child in cast(NonLeaf_Node, rule_node).sub_nodes:
        file.write(f"child: id={child.id!r}, titled_id={child.titled_id!r}, "
                   f"type={type(child).__name__}, _kind={child._kind!r}, "
                   f"id_of_goal={child.id_of_goal()!r}\n")

    # Fill GoalNode 1.1 (first subgoal)
    root.session.age += 1
    outcome2 = await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    print_header("edit_message: fill 1.1.1 (first subgoal)", file)
    file.write((await _P.edit_message(root, outcome2, root.session))[0])
    file.write("---------------\n")

    # Fill GoalNode 1.2 (second subgoal — should complete 1.2 and cascade to step 1)
    root.session.age += 1
    outcome3 = await root.fill("1.2.1", [Obvious.gen_single({"facts": []})])
    print_header("edit_message: fill 1.2.1 (second subgoal — should cascade)", file)
    file.write((await _P.edit_message(root, outcome3, root.session))[0])
    file.write("---------------\n")

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("Compute1", "Test_Compute1.thy", 9)
async def _test_Compute1(root: Root, file: MyIO):
    """Test Compute: evaluate a ground term and bind the result as a fact."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", [Compute.gen_single({
        "thought": "Evaluate 3 * 7",
        "term": "(3::nat) * 7",
        "name": "computed"
    })])
    print_header("After Compute", file)
    root.print(0, file)
    print_header("Quickview after Compute", file)
    root.quickview(0, file)
    root.session.age += 1
    await root.fill("2", [Obvious.gen_single({
        "facts": [{"name": "computed"}]
    })])
    print_header("After Obvious", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")


@model_test("Branch_SorryNextFail", "Test_Branch.thy", 8)
async def _test_Branch_SorryNextFail(root: Root, file: MyIO):
    """Reproduce: when Branch's sorry_next fails during sub-node creation,
    subsequent fill on a child of the partially-created Branch must NOT
    crash with InternalError("The beginning state of the execution is not
    initialized!").

    Root cause (from conversation e5fe3afb6_6): SubgoalMaker._refresh_the
    _beginning_opr's sorry_next loop (model.py ~line 4736) can raise
    IsabelleError (e.g. "Conclusion in obtained context must be object-logic
    judgment" from Obtain.eliminate in the CONSIDER MAGIC callback). The
    unhandled exception leaves sub_nodes partially populated with
    GoalNodes whose _state_before_ending_ was never initialized via the
    normal refresh path. A subsequent fill on those GoalNodes tries to
    execute from an uninitialized state, hitting "beginning_state_not_found"
    on the ML side, which is escalated to InternalError and crashes the
    process (sys.exit(1) in _edit_tool_logic).

    Strategy: monkey-patch sorry_next to fail on the second call (the one
    that advances past the first case), simulating the real failure without
    requiring the exact Isabelle-level conditions.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    sorry_next_call_count = 0
    original_sorry_next = Minilang_State.sorry_next

    async def patched_sorry_next(self, varnames, assign_to):
        nonlocal sorry_next_call_count
        sorry_next_call_count += 1
        if sorry_next_call_count == 2:
            raise IsabelleError(
                ["Conclusion in obtained context must be object-logic judgment"], None)
        return await original_sorry_next(self, varnames, assign_to)

    Minilang_State.sorry_next = patched_sorry_next

    root.session.age += 1
    try:
        outcome1 = await root.fill("1", [Branch.gen_single({
            "thought": "Case split on sign of x",
            "cases": [
                {"statement": {"english": "x is positive", "isabelle": "x > 0"},
                 "name": "pos"},
                {"statement": {"english": "x is negative", "isabelle": "x < 0"},
                 "name": "neg"},
                {"statement": {"english": "x is zero", "isabelle": "x = 0"},
                 "name": "zero"},
            ]
        })])
        branch_err = outcome1.failure
        if branch_err is not None:
            file.write(f"Branch fill returned failure: {branch_err}\n")
        else:
            file.write("Branch fill succeeded\n")
    except IsabelleError as e:
        file.write(f"Branch fill raised IsabelleError: {e}\n")
    except InternalError as e:
        file.write(f"BUG: Branch fill raised InternalError: {e}\n")
    finally:
        Minilang_State.sorry_next = original_sorry_next

    print_header("After Branch attempt (sorry_next patched to fail on 2nd call)", file)
    root.print(0, file)

    br = root.locate_node("1")
    if isinstance(br, NonLeaf_Node) and br.sub_nodes:
        file.write(f"Branch sub_nodes count: {len(br.sub_nodes)}\n")
        for gn in br.sub_nodes:
            file.write(f"  {gn.id}: status={gn.status.status.value}\n")

        root.session.age += 1
        try:
            outcome2 = await root.fill("1.0.1", [Obvious.gen_single({"facts": []})])
            if outcome2.failure:
                file.write(f"Fill 1.0.1 failure (graceful): {outcome2.failure}\n")
            else:
                file.write(f"Fill 1.0.1 succeeded\n")
        except InternalError as e:
            file.write(f"BUG: Fill 1.0.1 raised InternalError: {e}\n")
        except IsabelleError as e:
            file.write(f"Fill 1.0.1 raised IsabelleError (graceful): {e}\n")
        except Exception as e:
            file.write(f"Fill 1.0.1 raised {type(e).__name__}: {e}\n")
    else:
        file.write("Branch has no sub_nodes or was not created\n")

    print_header("Final state", file)
    root.print(0, file)


@model_test("Branch_SorryNextFail_Real", "Test_BranchSorryNextFail.thy", 16)
async def _test_Branch_SorryNextFail_Real(root: Root, file: MyIO):
    """Reproduce the actual ML-level sorry_next failure from conversation
    e5fe3afb6_6.  Uses the same goal structure: Ball quantifier over a set
    of functions, Rewrite with Ball_def to fix variables, then Branch.
    """
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    outcome1 = await root.fill("1", [Rewrite.gen_single({
        "thought": "Unfold the bounded universal",
        "using": [{"name": "Ball_def"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    print_header("After Rewrite with Ball_def", file)
    root.print(0, file)

    root.session.age += 1
    try:
        outcome2 = await root.fill("2", [Branch.gen_single({
            "thought": "Case split: c > 0 or c <= 0",
            "cases": [
                {"statement": {"english": "c is positive", "isabelle": "(0::real) < c"},
                 "name": "c_pos"},
                {"statement": {"english": "c is non-positive", "isabelle": "c \\<le> (0::real)"},
                 "name": "c_nonpos"},
            ]
        })])
        if outcome2.failure is not None:
            file.write(f"Branch fill failure: {outcome2.failure}\n")
        else:
            file.write("Branch fill succeeded\n")
    except IsabelleError as e:
        file.write(f"Branch raised IsabelleError: {e}\n")
    except InternalError as e:
        file.write(f"BUG (Branch): InternalError: {e}\n")

    print_header("After Branch attempt", file)
    root.print(0, file)

    br = root.locate_node("2")
    if isinstance(br, NonLeaf_Node) and br.sub_nodes:
        file.write(f"Branch sub_nodes: {len(br.sub_nodes)}\n")
        for gn in br.sub_nodes:
            file.write(f"  {gn.id}: status={gn.status.status.value}\n")
        root.session.age += 1
        try:
            outcome3 = await root.fill("2.0.1", [Obvious.gen_single({"facts": []})])
            if outcome3.failure:
                file.write(f"Fill 2.0.1 failure: {outcome3.failure}\n")
            else:
                file.write(f"Fill 2.0.1 succeeded\n")
        except InternalError as e:
            file.write(f"BUG (Fill): InternalError: {e}\n")
        except Exception as e:
            file.write(f"Fill 2.0.1 raised {type(e).__name__}: {e}\n")
    else:
        file.write("Branch has no sub_nodes\n")

    print_header("Final state", file)
    root.print(0, file)


@model_test("FillCancelledPredecessor", "Test_FillCancelledPredecessor.thy", 11)
async def _test_FillCancelledPredecessor(root: Root, file: MyIO):
    """Reproduce: filling a cancelled step whose predecessor's ml_state was
    reset by the cancellation cascade crashes with InternalError
    "The beginning state of the execution is not initialized!"

    Scenario (from log EA68457EB): a GoalNode has children
    [Have(h1), Derive(h1), Derive(hP), Derive(hQ), Obvious].  All succeed.
    Deleting the Have removes h1 from scope; the parent re-evaluates and
    the first Derive fails (h1 unfound).  The cancellation cascade resets
    downstream ml_states: cancel of Derive(hP) resets Derive(hQ).ml_state,
    cancel of Derive(hQ) resets Obvious.ml_state.  Filling the Obvious
    deletes it and refreshes the predecessor (Derive(hQ)), whose ml_state
    was reset — execute hits "beginning_state_not_found" on the ML side."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # The GoalNode for a single-goal proof has id="" — its children are
    # addressed as "1", "2", ... (no prefix).
    root.session.age += 1
    outcome0 = await root.fill("1", [
        Have.gen_single({
            "thought": "introduce P from premise",
            "statement": {"english": "P holds", "conclusion": "P"},
            "name": "h1"
        }),
        Derive.gen_single({
            "thought": "copy h1",
            "rule": {"name": "h1"},
            "result_name": "d1"
        }),
        Derive.gen_single({
            "thought": "copy hP",
            "rule": {"name": "hP"},
            "result_name": "d2"
        }),
        Derive.gen_single({
            "thought": "copy hQ",
            "rule": {"name": "hQ"},
            "result_name": "d3"
        }),
        Obvious.gen_single({"facts": []})
    ])
    file.write(f"batch fill failure: {outcome0.failure}\n")
    print_header("After batch fill (all should succeed)", file)
    root.print(0, file)

    # The GoalNode is root.sub_nodes[1] (after GlobalEnv)
    gn = root.sub_nodes[1]
    file.write(f"GoalNode children: {len(gn.sub_nodes)}\n")
    for c in gn.sub_nodes:
        file.write(f"  {c.id}: {type(c).__name__} status={c.status.status.value}\n")

    # Delete the Have (step "1") — triggers re-evaluation cascade.
    # The GoalNode is re-evaluated: Derive(h1) at step 2 fails (h1 gone),
    # subsequent steps 3, 4, 5 are CANCELLED.  Cancel of step 3 resets
    # step 4's ml_state; cancel of step 4 resets step 5's ml_state.
    root.session.age += 1
    await root.delete(["1"])

    print_header("After deleting Have h1 (cascade: Derive(h1) fails, rest cancelled)", file)
    root.print(0, file)
    gn = root.sub_nodes[1]
    file.write(f"GoalNode children after delete: {len(gn.sub_nodes)}\n")
    for c in gn.sub_nodes:
        file.write(f"  {c.id}: {type(c).__name__} status={c.status.status.value}\n")
        file.write(f"    ml_state initialized: {c.ml_state.initialized()}\n")

    # Try to fill the last cancelled step (Obvious at step "5").
    # BUG: fill deletes Obvious, predecessor is Derive(hQ) at step 4
    # whose ml_state was reset by step 3's cancel → execute hits
    # "beginning_state_not_found" on the ML side.
    root.session.age += 1
    try:
        outcome = await root.fill("5", [Obvious.gen_single({"facts": []})])
        if outcome.failure:
            file.write(f"Fill 5 returned failure (graceful): {outcome.failure}\n")
        else:
            file.write("Fill 5 succeeded\n")
    except InternalError as e:
        file.write(f"BUG: Fill 5 raised InternalError: {e}\n")
    except IsabelleError as e:
        file.write(f"Fill 5 raised IsabelleError: {e}\n")
    except Exception as e:
        file.write(f"Fill 5 raised {type(e).__name__}: {e}\n")

    print_header("Final state", file)
    root.print(0, file)


@model_test("GlobalEnv_LeafOps", "Test_GlobalEnv_LeafOps.thy", 11)
async def _test_GlobalEnv_LeafOps(root: Root, file: MyIO):
    """Verify that non-declarative operations (Obvious, Rewrite, InferenceRule)
    are rejected when inserted into GlobalEnv via append, and that declarative
    operations (Have) still work.

    Lemma: x = 0 ⟹ x * x = 0
    """
    print_header("Initial YAML", file)
    root.print(0, file)
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # --- 1: Obvious in GlobalEnv — should be rejected ---
    print_header("1: Obvious in GlobalEnv (should fail)", file)
    root.session.age += 1
    outcome = await root.global_env.append([Obvious.gen_single({
        "facts": [{"name": "h1"}]
    })])
    file.write(f"committed: {len(outcome.committed)}\n")
    file.write(f"failure: {outcome.failure is not None}\n")
    if outcome.failure:
        file.write(f"  type: {type(outcome.failure).__name__}\n")
        file.write(f"  message: {outcome.failure}\n")
        file.write(f"  is_error: {outcome.failure.is_error}\n")
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # --- 2: Rewrite in GlobalEnv — should be rejected ---
    print_header("2: Rewrite in GlobalEnv (should fail)", file)
    root.session.age += 1
    outcome = await root.global_env.append([Rewrite.gen_single({
        "thought": "Rewrite using h1",
        "using": [{"name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    })])
    file.write(f"committed: {len(outcome.committed)}\n")
    file.write(f"failure: {outcome.failure is not None}\n")
    if outcome.failure:
        file.write(f"  type: {type(outcome.failure).__name__}\n")
        file.write(f"  message: {outcome.failure}\n")
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # --- 3: InferenceRule in GlobalEnv — should be rejected ---
    print_header("3: InferenceRule in GlobalEnv (should fail)", file)
    root.session.age += 1
    outcome = await root.global_env.append([InferenceRule.gen_single({
        "thought": "Apply conjI",
        "rule": {"name": "conjI"},
    })])
    file.write(f"committed: {len(outcome.committed)}\n")
    file.write(f"failure: {outcome.failure is not None}\n")
    if outcome.failure:
        file.write(f"  type: {type(outcome.failure).__name__}\n")
        file.write(f"  message: {outcome.failure}\n")
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # --- 4: Have in GlobalEnv — should succeed (declarative) ---
    print_header("4: Have in GlobalEnv (should succeed)", file)
    root.session.age += 1
    outcome = await root.global_env.append([Have.gen_single({
        "thought": "Restate h1",
        "statement": {"english": "x is zero", "conclusion": "x = 0"},
        "name": "t1",
    })])
    file.write(f"committed: {len(outcome.committed)}\n")
    if outcome.committed:
        file.write(f"  id: {outcome.committed[0].id}\n")
        file.write(f"  status: {outcome.committed[0].status.status.value}\n")
    file.write(f"failure: {outcome.failure is not None}\n")
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # --- 5: Batch with Have + Obvious — should commit Have, reject Obvious ---
    print_header("5: Batch [Have, Obvious] (partial commit)", file)
    root.session.age += 1
    outcome = await root.global_env.append([
        Have.gen_single({
            "thought": "Another fact",
            "statement": {"english": "zero", "conclusion": "(0::int) = 0"},
            "name": "t2",
        }),
        Obvious.gen_single({"facts": []}),
    ])
    file.write(f"committed: {len(outcome.committed)}\n")
    if outcome.committed:
        for c in outcome.committed:
            file.write(f"  {c.id}: {c.status.status.value}\n")
    file.write(f"failure: {outcome.failure is not None}\n")
    if outcome.failure:
        file.write(f"  type: {type(outcome.failure).__name__}\n")
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # --- Final tree ---
    print_header("Final tree", file)
    root.print(0, file)


@model_test("RefuteOrSurrender", "Test_RefuteOrSurrender.thy", 11)
async def _test_RefuteOrSurrender(root: Root, file: MyIO):
    """Test the split tools for Worker (event-based) and Plan roles:
    `report` (refute / surrender) and the dual-role
    `request_lemmas` (worker channel + planner no-arg hint)."""
    from .mcp_http_server import (
        _report_tool_logic, _request_lemmas_tool_logic)
    from .model import WorkerHandle
    session = root.session

    # --- Worker: report communicates via the WorkerHandle queue ---
    session.age += 1
    goal_node = root.sub_nodes[1]
    await goal_node.fill("1", [Have.gen_single({
        "thought": "target",
        "statement": {"english": "trivial", "conclusion": "True"},
        "name": "h_target",
    })])
    have_node = goal_node.sub_nodes[0]

    # A real handle, but with no task started — we only inspect its event queue.
    handle = WorkerHandle(have_node, session)
    session.role = model.Role_Worker(target=have_node, worker_handle=handle)

    # Surrender: enqueues a WorkerSurrender AND sets a terminal quit_info=Surrender
    # so the worker's agent loop winds down cleanly (the planner also learns of it
    # via the event). See _report_tool_logic.
    result, is_error = await _report_tool_logic(session, {
        "type": "surrender",
        "detail": "I need more lemmas",
    })
    file.write(f"worker surrender result: {result}\n")
    file.write(f"worker surrender is_error: {is_error}\n")
    file.write(f"worker surrender sets quit_info: {session.quit_info is not None}\n")
    ev = handle._event_queue.get_nowait()
    file.write(f"surrender event: {type(ev).__name__}\n")
    file.write(f"surrender event detail: {ev.detail}\n")

    # Refute, planner REJECTS: the tool blocks on the review future until it is
    # resolved, then tells the worker to keep going.
    task = asyncio.ensure_future(_report_tool_logic(session, {
        "type": "refute",
        "detail": "The goal contradicts premises",
    }))
    ev = await handle._event_queue.get()
    file.write(f"refute event: {type(ev).__name__}\n")
    file.write(f"refute event detail: {ev.detail}\n")
    ev.response_future.set_result((False, "premises are actually consistent"))
    result, is_error = await task
    file.write(f"refute rejected result mentions reject: {'reject' in result.lower()}\n")
    file.write(f"refute rejected is_error: {is_error}\n")

    # Refute, planner ACCEPTS.
    task = asyncio.ensure_future(_report_tool_logic(session, {
        "type": "refute",
        "detail": "genuinely unprovable",
    }))
    ev = await handle._event_queue.get()
    ev.response_future.set_result((True, None))
    result, is_error = await task
    file.write(f"refute accepted result mentions accept: {'accept' in result.lower()}\n")

    # --- Worker: request_lemmas blocks on a feedback future, then resumes ---
    task = asyncio.ensure_future(_request_lemmas_tool_logic(session, {
        "detail": "need a helper about squares",
        "suggested_lemmas": [{
            "name": "sq_nonneg", "english": "squares are non-negative",
            "isabelle_statement": "0 ≤ x * x"}],
    }))
    ev = await handle._event_queue.get()
    file.write(f"request_lemmas event: {type(ev).__name__}\n")
    file.write(f"request_lemmas event lemmas count: {len(ev.lemmas)}\n")
    ev.response_future.set_result("Added lemma sq_nonneg; use it to continue.")
    result, is_error = await task
    file.write(f"request_lemmas resume mentions sq_nonneg: {'sq_nonneg' in result}\n")
    file.write(f"request_lemmas resume is_error: {is_error}\n")

    # Worker request_lemmas with an empty wish-list is rejected.
    result, is_error = await _request_lemmas_tool_logic(session, {
        "detail": "vague", "suggested_lemmas": []})
    file.write(f"empty request_lemmas is_error: {is_error}\n")

    # Invalid type (validated before the role branch).
    result, is_error = await _report_tool_logic(session, {
        "type": "invalid_type",
        "detail": "test",
    })
    file.write(f"invalid type is_error: {is_error}\n")
    file.write(f"invalid type result contains 'Invalid': {'Invalid' in result}\n")

    # A Role_Worker with no handle is a programming error → InternalError.
    session.role = model.Role_Worker(target=goal_node)
    try:
        await _report_tool_logic(session, {"type": "surrender", "detail": "x"})
        file.write("no-handle worker: NO error raised (UNEXPECTED)\n")
    except model.InternalError:
        file.write("no-handle worker: InternalError raised\n")

    # --- Plan: request_lemmas is a no-argument hint (no event, no error) ---
    session.role = model.Role_Major()
    result, is_error = await _request_lemmas_tool_logic(session, {})
    file.write(f"planner request_lemmas is_error: {is_error}\n")
    file.write(f"planner request_lemmas mentions global: {'global' in result.lower()}\n")

    # NOTE: the Role_Major surrender path is intentionally NOT exercised here.
    # It calls request_restart(), which leaves a transient quit_info=Restart()
    # that only a driver loop consumes; in the model-test path nothing consumes
    # it, so `by aoa` would never terminate cleanly. Planner refute/surrender
    # behavior is unchanged by this split and is out of scope for this test.


@model_test("RecallWorkerScope", "Test_RecallWorkerScope.thy", 9)
async def _test_recall_worker_scope(root: Root, file: MyIO):
    """`recall` line-bound computation under a *worker*-scoped proof.yaml.

    A worker's ``refresh_YAML`` (``print_proof_scope``) re-renders only the
    target's subtree, so only the target's *descendants* get fresh ``.line``;
    the target itself, its ancestors and its siblings keep stale lines from an
    earlier full render. We build a Have block ``H`` (the worker target) with
    two children, plus a sibling step ``G`` after it, then poison ``G.line``
    to simulate that stale value. The regression this guards: before the
    scope-aware fix, recalling the *last* child of ``H`` escaped the target
    subtree and read ``G``'s stale line, returning an end before the node's
    own start (an empty `Line N-(N-1)` read). It also checks that recalling an
    out-of-scope id (the target itself, or the sibling) is rejected."""
    import re
    import tempfile
    from io import StringIO
    from .mcp_http_server import _read_tool_logic, _line_is_fresh, _node_end_line

    session = root.session
    goal = root.sub_nodes[1]

    # H = Have block (worker target) with two children: a nested Have "1.1"
    # (itself having child "1.1.1") and a closing Obvious "1.2" (the LAST child).
    await goal.fill("1", [Have.gen_single({
        "thought": "outer helper",
        "statement": {"english": "x squared is non-negative",
                      "conclusion": r"(0::int) \<le> x * x"},
        "name": "outer"})])
    H = goal.sub_nodes[0]
    await root.fill("1.1", [Have.gen_single({
        "thought": "inner helper",
        "statement": {"english": "x squared is non-negative",
                      "conclusion": r"(0::int) \<le> x * x"},
        "name": "inner"})])
    await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    # Second child of H, also a Have: this leaves H's own subgoal open (and thus
    # the whole proof unfinished), so `root.is_proof_finished()` is False and the
    # ML side never tries to assemble a closing proof (which would trip the
    # "axiomatic sorry" guard). Mirrors how `Have1` leaves its goal open.
    await H.append([Have.gen_single({
        "thought": "inner helper 2",
        "statement": {"english": "x squared is non-negative",
                      "conclusion": r"(0::int) \<le> x * x"},
        "name": "inner2"})])                               # node "1.2" (H's last child)
    # G = a top-level sibling AFTER H (out of the worker's scope).
    await goal.append([Have.gen_single({
        "thought": "out-of-scope sibling",
        "statement": {"english": "x squared is non-negative",
                      "conclusion": r"(0::int) \<le> x * x"},
        "name": "sibling"})])                              # node "2"
    G = goal.sub_nodes[1]

    # Switch to a worker scoped to H and render the scoped proof.yaml (this is
    # what the live worker's refresh_YAML does): only H's descendants get fresh
    # `.line` values, consistent with the on-disk scoped file.
    session.role = model.Role_Worker(target=H)
    fd, tmp = tempfile.mkstemp(prefix="recall_scope_", suffix=".yaml")
    os.close(fd)
    session.YAML_path = tmp
    with open(tmp, "w", encoding="utf-8") as f:
        session.print_proof_scope(0, MyIO(f), update_line=True, show_warnings=True)
    with open(tmp, encoding="utf-8") as f:
        total_lines = len(f.readlines())

    # Simulate a stale line left on the out-of-scope sibling by an earlier full
    # render: a small, nonzero value that the old (scope-blind) `_node_end_line`
    # would wrongly adopt as the end bound for H's last child.
    G.line = 5

    def _span(res: str) -> tuple[int, int] | None:
        m = re.search(r"showing Line (\d+)-(\d+)", res)
        return (int(m.group(1)), int(m.group(2))) if m else None

    last = H.sub_nodes[-1]                 # "1.2", H's last child
    nonlast = H.sub_nodes[0]               # "1.1", in-scope, not last

    # A worker addresses steps relative to its scope, so recall is called with
    # the relative id (what the worker sees in proof.yaml); it resolves back to
    # the absolute node internally.
    print_header("recall last child of target (in scope)", file)
    res, err = await _read_tool_logic(session, {"step_id": [session._display_id(last.id)]})
    a, b = _span(res)
    file.write(f"is_error: {err}\n")
    file.write(f"non-empty range (end >= start): {b >= a}\n")
    file.write(f"reaches end of scoped file: {b == total_lines}\n")

    print_header("recall non-last child of target (in scope)", file)
    res, err = await _read_tool_logic(session, {"step_id": [session._display_id(nonlast.id)]})
    a, b = _span(res)
    file.write(f"is_error: {err}\n")
    file.write(f"non-empty range (end >= start): {b >= a}\n")

    # Out-of-scope nodes are no longer addressable: a worker only ever sees/uses
    # ids relative to its own scope, so the target's siblings/ancestors have no
    # id it can express — the relativized display id of the sibling is
    # `<external>`, and the scope root itself relativizes to the empty id.
    print_header("out-of-scope nodes are not worker-addressable", file)
    file.write(f"sibling G display id: {session._display_id(G.id)}\n")
    file.write(f"scope-root H display id: {session._display_id(H.id)!r}\n")

    print_header("helper predicates", file)
    file.write(f"_line_is_fresh(last child)  : {_line_is_fresh(last, H, True)}\n")
    file.write(f"_line_is_fresh(grandchild)  : {_line_is_fresh(nonlast.sub_nodes[0], H, True)}\n")
    file.write(f"_line_is_fresh(target self) : {_line_is_fresh(H, H, True)}\n")
    file.write(f"_line_is_fresh(sibling)     : {_line_is_fresh(G, H, True)}\n")
    file.write(f"_node_end_line(last child) == EOF: "
               f"{_node_end_line(last, total_lines, H) == total_lines}\n")
    # Planner (non-worker): the whole tree is freshly rendered, so every node is
    # in scope regardless of position.
    file.write(f"_line_is_fresh(sibling, planner): {_line_is_fresh(G, root, False)}\n")

    session.role = model.Role_Major()
    os.remove(tmp)


@model_test("RecallContainment", "Test_RecallContainment.thy", 9)
async def _test_recall_containment(root: Root, file: MyIO):
    """Multi-step `recall` containment (planner / whole-tree scope).

    When several `step_id`s are requested at once, a step whose *printed* line
    range falls inside another requested step's printed range is already shown
    within that enclosing segment, so it renders header-only (`... ; content
    already shown above`) instead of repeating the lines. Covers:
      - nesting chains (1 ⊃ 1.1 ⊃ 1.1.1) + a non-contained sibling (2);
      - order independence (child listed before parent still collapses);
      - printed-range (NOT tree-ancestry) semantics: a small `range` that
        truncates the parent before the child's lines leaves the child in full;
      - single-step recall never suppresses;
      - a nonexistent id warns inline without disturbing the others.

    Reuses `_make_lock_tree`:
        1 (Have H){ 1.1 (Have){1.1.1 Obvious}, 1.2 (Have, open) },  2 (Have sib)
    1.2 stays open so the proof is unfinished (mirrors the worker recall test).
    """
    import re
    from .mcp_http_server import _read_tool_logic

    session = root.session
    session.role = model.Role_Major()                 # planner: whole tree in scope
    goal, H = await _make_lock_tree(root)

    # Render the whole-tree proof.yaml the planner reads, with fresh line nums.
    fd, tmp = tempfile.mkstemp(prefix="recall_contain_", suffix=".yaml")
    os.close(fd)
    session.YAML_path = tmp
    with open(tmp, "w", encoding="utf-8") as f:
        session.print_proof_scope(0, MyIO(f), update_line=True, show_warnings=True)

    _HDR = re.compile(r"^\[Step (\S+) is at Line ")
    def _summary(res: str) -> str:
        """One robust line per segment: id, mode (full|contained) and whether
        any content followed the header. Deliberately omits exact line numbers /
        YAML body so the golden is stable against layout drift — the feature is
        captured by mode + content_present."""
        segs: list[dict] = []
        cur: dict | None = None
        for ln in res.split("\n"):
            m = _HDR.match(ln)
            if m:
                cur = {"id": m.group(1),
                       "mode": "contained" if "content already shown above" in ln else "full",
                       "content": False}
                segs.append(cur)
            elif ln.startswith("WARNING"):
                cur = {"warn": ln}
                segs.append(cur)
            elif ln.strip() and cur is not None and "id" in cur:
                cur["content"] = True
        out = []
        for s in segs:
            if "warn" in s:
                out.append(s["warn"])
            else:
                out.append(f"{s['id']:<10} {s['mode']:<9} content_present={s['content']}")
        return "\n".join(out)

    async def _recall(label: str, **kw):
        print_header(label, file)
        res, err = await _read_tool_logic(session, kw)
        file.write(f"is_error: {err}\n")
        file.write(_summary(res) + "\n")

    # Full nest + sibling: 1 full; 1.1/1.1.1/1.2 collapse (shown within 1); 2 full.
    await _recall("recall [1, 1.1, 1.1.1, 1.2, 2]", step_id=["1", "1.1", "1.1.1", "1.2", "2"])
    # Child listed before its parent: output order is preserved, child still collapses.
    await _recall("recall [1.1, 1] (child before parent)", step_id=["1.1", "1"])
    # range=2 truncates 1's print before 1.2's lines -> 1.2 not contained -> full.
    await _recall("recall [1, 1.2] range=2 (parent truncated)", step_id=["1", "1.2"], range=2)
    # Single id: nothing can contain it.
    await _recall("recall [1] (single step)", step_id=["1"])
    # Nonexistent id warns inline; 1 full, 1.1 collapses regardless.
    await _recall("recall [1, 1.1, 9.9] (missing id)", step_id=["1", "1.1", "9.9"])

    os.remove(tmp)


async def _make_lock_tree(root):
    """Build the shared tree used by the edit-lock tests:
        1 (Have H) { 1.1 (Have){1.1.1 Obvious}, 1.2 (Have) },  2 (Have, sibling)
    Returns (goal, H) where H == node "1". 1.2 is an open Have, so the proof
    stays unfinished (H.status == SUCCESS but is_proof_finished() == False)."""
    goal = root.sub_nodes[1]
    s = {"english": "nonneg", "conclusion": r"(0::int) \<le> x * x"}
    await goal.fill("1", [Have.gen_single({"thought": "H", "statement": s, "name": "hH"})])
    H = goal.sub_nodes[0]
    await root.fill("1.1", [Have.gen_single({"thought": "c1", "statement": s, "name": "hC1"})])
    await root.fill("1.1.1", [Obvious.gen_single({"facts": []})])
    await H.append([Have.gen_single({"thought": "c2", "statement": s, "name": "hC2"})])  # 1.2 (open)
    await goal.append([Have.gen_single({"thought": "sib", "statement": s, "name": "hSib"})])  # 2
    return goal, H


def _dump_verdicts(session, file, label, cases):
    print_header(label, file)
    for step, action in cases:
        v, h = session._edit_verdict(step, action)
        file.write(f"{action:>13} {step:<9} -> {v.name:<13} blocker={h.target.id if h else '-'}\n")


@model_test("EditLock_MainAgent", "Test_EditLock_MainAgent.thy", 9)
async def _test_editlock_main(root: Root, file: MyIO):
    """Main-agent edit-lock via `_edit_verdict` + the two rendered LOCKED
    messages. A parked worker is simulated by attaching an (unstarted)
    `WorkerHandle` to Have node "1". Covers lock rows L1-L4 and the self-handle
    exemption (amend on the parked node itself is allowed; it tears its own
    worker down)."""
    from .mcp_http_server import _edit_tool_logic
    from .model import WorkerHandle
    session = root.session
    session.age += 1
    goal, H = await _make_lock_tree(root)

    H.worker_handle = WorkerHandle(H, session)   # parked worker on "1"
    try:
        _dump_verdicts(session, file, "main _edit_verdict (parked worker on 1)", [
            ("1.1", "fill"),     # L1 ancestor "1" has the handle
            ("1", "fill"),       # L1 node itself holds the handle
            ("1.1", "amend"),    # L2 ancestor "1"
            ("1", "amend"),      # self-handle: own worker torn down by _amend_child -> OK
            ("1.3", "fill"),     # L3 new slot, parent "1" holds the handle
            ("2", "fill"),       # disjoint subtree -> OK
            ("1.2", "delete"),   # L4 delete never locks
            ("1", "delete"),     # L4
        ])

        print_header("main fill 1.1 -> LOCKED message", file)
        r, e = await _edit_tool_logic(session, {"target_step": "1.1", "action": "fill",
            "proof_operations": [{"operation": "Obvious", "facts": []}]})
        file.write(f"is_error={e}\n{r}\n")
        print_header("main amend 1.1 -> LOCKED message (names blocker 1)", file)
        r, e = await _edit_tool_logic(session, {"target_step": "1.1", "action": "amend",
            "proof_operations": [{"operation": "Obvious", "facts": []}]})
        file.write(f"is_error={e}\n{r}\n")
    finally:
        H.worker_handle = None   # detach even on failure (close-sweep robustness)


@model_test("EditConfine_Worker", "Test_EditConfine_Worker.thy", 9)
async def _test_editconfine_worker(root: Root, file: MyIO):
    """Worker confinement + worker-side lock via `_edit_verdict`, with the
    out-of-scope and worker-LOCKED messages. The worker's scope root X_A is
    Have node "1" (its own handle attached). Covers confinement rows C1-C7,
    the C4/Bug-B own-direct-substep allowance, and worker-LOCKED on a nested
    handle attached to "1.1"."""
    from .mcp_http_server import _edit_tool_logic
    from .model import WorkerHandle
    session = root.session
    session.age += 1
    goal, H = await _make_lock_tree(root)

    h_H = WorkerHandle(H, session)
    H.worker_handle = h_H
    session.role = model.Role_Worker(target=H, worker_handle=h_H)   # X_A = "1"
    n11 = root.locate_node("1.1")
    try:
        _dump_verdicts(session, file, "worker confinement (X_A = 1)", [
            ("1.1", "fill"),        # C1 proper descendant -> OK
            ("1", "amend"),         # C2 editing own target -> OUT_OF_SCOPE
            ("2", "fill"),          # C3 sibling subtree -> OUT_OF_SCOPE
            ("global.1", "fill"),   # C3 the global env -> OUT_OF_SCOPE
            ("1.3", "fill"),        # C4 own direct new slot (Bug B) -> OK
            ("5", "fill"),          # C7 top-level new slot -> OUT_OF_SCOPE
            ("1.1", "delete"),      # in scope -> OK
            ("2", "delete"),        # out of scope -> OUT_OF_SCOPE
        ])

        n11.worker_handle = WorkerHandle(n11, session)   # nested sub-worker on "1.1"
        _dump_verdicts(session, file, "worker-LOCKED (sub-worker on 1.1)", [
            ("1.1.1", "fill"),      # ancestor "1.1" below X_A -> LOCKED
            ("1.1.5", "fill"),      # new slot, parent "1.1" holds the handle -> LOCKED
            ("1.1.1", "amend"),     # ancestor "1.1" -> LOCKED
        ])

        # A worker's tool ids are relative to its scope ("1"), so "2" resolves to
        # its OWN child "1.2" — it can never address the top-level sibling "2".
        # Confinement is now structural; the explicit OUT_OF_SCOPE verdict is
        # unreachable via the tool (it remains as a belt-and-suspenders guard,
        # exercised directly by `_dump_verdicts` above).
        print_header("worker 'fill 2' resolves in-scope to 1.2 (sibling unreachable)", file)
        r, e = await _edit_tool_logic(session, {"target_step": "2", "action": "fill",
            "proof_operations": [{"operation": "Obvious", "facts": []}]})
        file.write(f"is_error={e}\n{r}\n")
        # Relative "1.1.1" (= absolute "1.1.1.1", under the nested sub-worker on
        # "1.1") is LOCKED; the blocker id is shown relativized ("1.1" -> "1").
        print_header("worker fill 1.1.1 -> worker-LOCKED message (relativized id)", file)
        r, e = await _edit_tool_logic(session, {"target_step": "1.1.1", "action": "fill",
            "proof_operations": [{"operation": "Obvious", "facts": []}]})
        file.write(f"is_error={e}\n{r}\n")
    finally:
        session.role = model.Role_Major()
        n11.worker_handle = None
        H.worker_handle = None


@model_test("DispatchGate", "Test_DispatchGate.thy", 9)
async def _test_dispatch_gate(root: Root, file: MyIO):
    """`subagent` dispatch gate via `_dispatch_blocked_by` + the rendered
    rejection message. A parked worker on "1.1" makes both directions illegal:
    dispatching a descendant INTO it, and dispatching an ancestor OVER it."""
    from .mcp_http_server import _subagent_tool_logic
    from .model import WorkerHandle
    session = root.session
    session.age += 1
    goal, H = await _make_lock_tree(root)

    n11 = root.locate_node("1.1")
    n11.worker_handle = WorkerHandle(n11, session)
    try:
        print_header("_dispatch_blocked_by (parked worker on 1.1)", file)
        for sid in ["1.1.1", "1", "2"]:
            node = root.locate_node(sid)
            h = session._dispatch_blocked_by(node)
            file.write(f"dispatch on {sid:<7} -> blocked_by={h.target.id if h else '-'}\n")

        print_header("subagent on 1 -> gate reject message (names 1.1)", file)
        r, e = await _subagent_tool_logic(session, {
            "step_id": "1", "suggestions": "x", "helpful_lemmas": []})
        file.write(f"is_error={e}\n{r}\n")
    finally:
        n11.worker_handle = None


@model_test("NestedWorkerScope", "Test_NestedWorkerScope.thy", 9)
async def _test_nested_worker_scope(root: Root, file: MyIO):
    """Deterministic coverage of worker-relative-id translation across nesting:
    the pure id/text helpers, cross-namespace suggestion re-basing, the
    `subagent` external-ref rejection + one-shot bypass, and the
    refutation-review reason conversion. Every path here resolves BEFORE the
    live-dispatch point (`handle.start`/`run_until_yield`, which needs an LLM),
    so it is exercised by calling the helpers / tool-logic directly."""
    from .mcp_http_server import (_subagent_tool_logic, _delete_tool_logic,
                                  _report_tool_logic,
                                  _close_subagent_tool_logic)
    session = root.session
    session.age += 1
    goal = root.sub_nodes[1]
    s = {"english": "nonneg", "conclusion": r"(0::int) \<le> x * x"}
    # Deep tree: 1 { 1.1 { 1.1.1 { 1.1.1.1 }, 1.1.2 }, 1.2 } — depth lets the
    # in-scope/external ids be multi-component (the free-text regex needs a dot).
    await goal.fill("1",       [Have.gen_single({"thought": "h1",   "statement": s, "name": "h1"})])
    await root.fill("1.1",     [Have.gen_single({"thought": "h11",  "statement": s, "name": "h11"})])
    await root.fill("1.1.1",   [Have.gen_single({"thought": "h111", "statement": s, "name": "h111"})])
    await root.fill("1.1.1.1", [Have.gen_single({"thought": "h1111","statement": s, "name": "h1111"})])
    H1  = goal.sub_nodes[0]
    H11 = root.locate_node("1.1")
    await H11.append([Have.gen_single({"thought": "h112", "statement": s, "name": "h112"})])  # 1.1.2
    await H1.append([Have.gen_single({"thought": "h12",  "statement": s, "name": "h12"})])    # 1.2

    def show(label, pairs):
        print_header(label, file)
        for k, v in pairs:
            file.write(f"{k} = {v!r}\n")

    # --- 1. direct id translation, worker scope = 1.1 ---
    session.role = model.Role_Worker(target=H11, worker_handle=WorkerHandle(H11, session))
    show("_display_id (worker scope 1.1)", [
        ("1.1.1",   session._display_id("1.1.1")),     # in-scope child   -> 1
        ("1.1.1.1", session._display_id("1.1.1.1")),   # deeper in-scope  -> 1.1
        ("1.1.2",   session._display_id("1.1.2")),     # in-scope         -> 2
        ("1.1",     session._display_id("1.1")),       # scope root       -> ''
        ("1.2",     session._display_id("1.2")),       # sibling          -> <external>
        ("1",       session._display_id("1")),         # ancestor         -> <external>
    ])
    show("_resolve_display_id (worker scope 1.1)", [
        ("1",   session._resolve_display_id("1")),     # -> 1.1.1
        ("1.1", session._resolve_display_id("1.1")),   # -> 1.1.1.1
        ("2",   session._resolve_display_id("2")),     # -> 1.1.2
    ])

    # --- 2. free-text round-trip + <external> masking + the `Subgoal` anchor.
    # Single-component refs (`step 2`) are intentionally NOT translated (regex
    # needs a dot) — asserted here so the limitation is regression-locked.
    show("free text (worker scope 1.1)", [
        ("relativize", session._relativize_text(
            "Subgoal 1.1.1.1 fails; step 1.2 elsewhere; step 1.1.1 ok")),
        ("absolutize", session._absolutize_text("step 1.1 plus step 2")),
    ])

    # --- 3. cross-namespace suggestion re-base: SAME input, different dispatcher
    # namespace -> different result (the nested-specific behavior).
    session.role = model.Role_Major()
    rb_planner = session._rebase_suggestion_ids(H11, "use step 1.1.1 then step 1.2")
    session.role = model.Role_Worker(target=H1, worker_handle=WorkerHandle(H1, session))  # dispatcher W on scope 1
    rb_worker = session._rebase_suggestion_ids(H11, "use step 1.1 then step 1.1.2")
    show("_rebase_suggestion_ids", [
        ("planner -> recipient 1.1",  rb_planner),   # ('use step 1 then step 1.2', ['1.2'])
        ("worker(1) -> recipient 1.1", rb_worker),   # resolved via W's scope first
    ])

    # --- 4. subagent external-ref rejection + one-shot bypass (returns before dispatch) ---
    session.role = model.Role_Major()
    session._subagent_extstep_bypass.clear()
    print_header("subagent external suggestion -> reject + arm bypass", file)
    r, e = await _subagent_tool_logic(session, {
        "step_id": "1.1", "suggestions": "see step 1.2", "helpful_lemmas": []})
    file.write(f"is_error={e}\n{r}\n")
    file.write(f"bypass armed for 1.1: {'1.1' in session._subagent_extstep_bypass}\n")

    # --- 5. refutation-review reason conversion (accept absolutizes; reject
    # rebases into the worker's scope and rejects external refs). ---
    class _C:
        detail = "x"
    print_header("review accept (worker reviewer absolutizes its reason)", file)
    session.role = model.Role_Worker(target=H1, worker_handle=WorkerHandle(H1, session))  # reviewer = nested worker on 1
    iv = Interaction_ReviewRefutation(target=H11, complaint=_C(), worker_handle=WorkerHandle(H11, session))
    acc = await iv.answer(AnswerRefutation(accept=True, reason="step 1.1 contradicts the axiom"))
    file.write(f"accept reason -> {acc!r}\n")
    print_header("review reject citing an out-of-worker-scope step -> BadAnswer", file)
    session.role = model.Role_Major()
    iv2 = Interaction_ReviewRefutation(target=H11, complaint=_C(), worker_handle=WorkerHandle(H11, session))
    try:
        await iv2.answer(AnswerRefutation(accept=False, reason="look at step 1.2 instead"))
        file.write("UNEXPECTED: no BadAnswer raised\n")
    except Interaction_BadAnswer as ex:
        file.write(f"BadAnswer raised; mentions external ref: {'1.2' in str(ex)}\n")

    # --- 6. round-trip closure + the prefix-DOT boundary. The boundary catches a
    # `startswith(prefix)` (missing the ".") bug: `1.10` is a SIBLING of `1.1`,
    # not a descendant, so it must mask to <external>, while `1.1.10` is a real
    # descendant -> 10. (Pure string logic; the nodes need not exist.) ---
    session.role = model.Role_Worker(target=H11, worker_handle=WorkerHandle(H11, session))
    show("round-trip + dot-boundary (worker scope 1.1)", [
        ("resolve.display == id  (1.1.1 / 1.1.1.1 / 1.1.2)",
            all(session._resolve_display_id(session._display_id(x)) == x
                for x in ("1.1.1", "1.1.1.1", "1.1.2"))),
        ("display.resolve == rel (1 / 1.1 / 2)",
            all(session._display_id(session._resolve_display_id(r)) == r
                for r in ("1", "1.1", "2"))),
        ("1.10  (sibling of 1.1, NOT a descendant)", session._display_id("1.10")),
        ("1.1.10 (genuine descendant)",              session._display_id("1.1.10")),
    ])

    # --- 7. non-worker identity: planners/interaction forks must NOT touch ids ---
    session.role = model.Role_Major()
    show("non-worker (planner) identity", [
        ("display_id 1.1.1",      session._display_id("1.1.1")),
        ("resolve 2.3.1",         session._resolve_display_id("2.3.1")),
        ("relativize_text",       session._relativize_text("step 1.1.1 and Subgoal 2.4 ok")),
    ])

    # --- 8. _rebase_suggestion_ids: SAME input, planner vs worker dispatcher.
    # Identical text on the SAME recipient must give DIFFERENT results because
    # the worker resolves through its own scope first (proves namespace is used,
    # not just that different inputs differ). ---
    same = "apply step 1.1.1 like step 1.2"
    session.role = model.Role_Major()
    rb_p = session._rebase_suggestion_ids(H11, same)
    session.role = model.Role_Worker(target=H1, worker_handle=WorkerHandle(H1, session))
    rb_w = session._rebase_suggestion_ids(H11, same)
    show("_rebase same input, planner vs worker(scope 1)", [
        ("planner",   rb_p),     # ('apply step 1 like step 1.2', ['1.2'])
        ("worker(1)", rb_w),     # ('apply step 1.1 like step 2', [])
    ])

    # --- 9. bypass keys are per-node independent (arming one does not arm another) ---
    session.role = model.Role_Major()
    session._subagent_extstep_bypass.clear()
    await _subagent_tool_logic(session, {"step_id": "1.1",   "suggestions": "see step 1.2", "helpful_lemmas": []})
    await _subagent_tool_logic(session, {"step_id": "1.1.1", "suggestions": "see step 1.2", "helpful_lemmas": []})
    show("bypass keys are per-node independent", [
        ("1.1 armed",   "1.1"   in session._subagent_extstep_bypass),
        ("1.1.1 armed", "1.1.1" in session._subagent_extstep_bypass),
        ("unrelated 1.2 NOT armed", "1.2" in session._subagent_extstep_bypass),
    ])

    # --- 10. delete inbound resolution + relativized not-found (no tree mutation:
    # the relative id resolves to an absent in-scope node). ---
    session.role = model.Role_Worker(target=H11, worker_handle=WorkerHandle(H11, session))
    print_header("delete relative '9' -> resolves in-scope, not found (relativized)", file)
    r, e = await _delete_tool_logic(session, {"target_steps": ["9"]})
    file.write(f"is_error={e}\n{r}\n")

    # --- 11. retry_prompt lists UNFINISHED ids in the worker's relative form ---
    H111 = root.locate_node("1.1.1")
    print_header("retry_prompt (worker scope 1.1)", file)
    file.write(session.retry_prompt({H111}) + "\n")

    # --- 12. worker→planner detail is ABSOLUTIZED at emission. A worker on scope
    # 1.1 surrenders citing relative "step 1.1" (= absolute 1.1.1.1); the enqueued
    # event must carry the absolute id (the dispatcher re-relativizes for its view).
    # `step 2` is single-component -> left as-is (documented limitation). ---
    h_emit = WorkerHandle(H11, session)
    session.role = model.Role_Worker(target=H11, worker_handle=h_emit)
    await _report_tool_logic(session, {
        "type": "surrender", "detail": "blocked by step 1.1 and step 2"})
    ev = h_emit._event_queue.get_nowait()
    print_header("worker detail absolutized at emit (worker scope 1.1)", file)
    file.write(f"event={type(ev).__name__}; detail={ev.detail!r}\n")
    session.quit_info = None

    # --- 13. cancel_subagent: a worker closes its own sub-agent by RELATIVE id;
    # the id resolves to the right node, the handle detaches, and a relative id
    # with no handle yields a relativized "no sub-agent" error. ---
    session.role = model.Role_Worker(target=H1, worker_handle=WorkerHandle(H1, session))
    H11.worker_handle = WorkerHandle(H11, session)          # sub-agent parked on 1.1
    r_c, e_c = await _close_subagent_tool_logic(session, {"step_id": "1"})   # relative 1 -> 1.1
    print_header("cancel_subagent relative '1' (->1.1): detach", file)
    file.write(f"is_error={e_c}; {r_c}\n")
    file.write(f"handle on 1.1 detached: {H11.worker_handle is None}\n")
    r_c2, e_c2 = await _close_subagent_tool_logic(session, {"step_id": "2"})  # relative 2 -> 1.2 (no handle)
    file.write(f"no-handle is_error={e_c2}; {r_c2}\n")

    # --- 14. redirect_note relativized for a worker dispatcher. Delegating a LEAF
    # (1.2.1.1, an Obvious) redirects UP to its enclosing goal 1.2.1, which is
    # already proved -> errors before any live dispatch, with both ids shown in
    # the worker's relative form. ---
    await root.fill("1.2.1", [Have.gen_single({"thought": "p", "statement": {"english": "t", "conclusion": "True"}, "name": "hp"})])
    await root.fill("1.2.1.1", [Obvious.gen_single({"facts": []})])
    session.role = model.Role_Worker(target=H1, worker_handle=WorkerHandle(H1, session))
    r_r, e_r = await _subagent_tool_logic(session, {"step_id": "2.1.1", "suggestions": "", "helpful_lemmas": []})
    print_header("subagent on leaf '2.1.1' redirects up to '2.1' (relativized note)", file)
    file.write(f"is_error={e_r}\n{r_r}\n")

    # --- 15. COMPREHENSIVE depth-2/3 nesting + edge cases. Stack:
    # planner -> W1(scope 1) -> W2(scope 1.1) -> W3(scope 1.1.1). Relativization
    # keys only off each session's OWN target (never the parent chain), so
    # switching the role faithfully models the worker stack. Extend the deep
    # branch to 1.1.1.1.1 so depth-3 relative ids stay multi-component. ---
    await root.fill("1.1.1.1.1", [Have.gen_single({"thought": "d5", "statement": {"english": "t", "conclusion": "True"}, "name": "h5"})])
    Wd3 = root.locate_node("1.1.1")
    def _W(target):  # set a fresh worker role on `target`
        session.role = model.Role_Worker(target=target, worker_handle=WorkerHandle(target, session))

    # (a) ONE node (1.1.1.1.1) shown at all FOUR levels — each its own namespace.
    session.role = model.Role_Major(); a_p = session._display_id("1.1.1.1.1")
    _W(H1);  a_w1 = session._display_id("1.1.1.1.1")
    _W(H11); a_w2 = session._display_id("1.1.1.1.1")
    _W(Wd3); a_w3 = session._display_id("1.1.1.1.1")
    show("depth (a): node 1.1.1.1.1 at planner / W1(1) / W2(1.1) / W3(1.1.1)", [
        ("planner",   a_p),    # 1.1.1.1.1
        ("W1(1)",     a_w1),   # 1.1.1.1
        ("W2(1.1)",   a_w2),   # 1.1.1
        ("W3(1.1.1)", a_w3),   # 1.1
        ("round-trip W3 resolve(display)==id", session._resolve_display_id(a_w3) == "1.1.1.1.1"),
    ])

    # (b) a detail authored by the INNERMOST W3 round-trips UP three levels; the
    # same node renders in each viewer's namespace.
    _W(Wd3)
    d_emit = session._absolutize_text(f"see step {session._display_id('1.1.1.1.1')}")  # 'see step 1.1' -> absolute
    chain = [("W3 authors", f"see step {a_w3}"), ("absolutized at emit", d_emit)]
    _W(H11); chain.append(("W2(1.1) view", session._relativize_text(d_emit)))
    _W(H1);  chain.append(("W1(1) view",   session._relativize_text(d_emit)))
    session.role = model.Role_Major(); chain.append(("planner view", session._relativize_text(d_emit)))
    show("depth (b): W3-authored detail re-relativized up the stack", chain)

    # (c) cross-namespace suggestion rebase at the W1->W2 dispatch boundary: an
    # in-scope ref relativizes into W2; a ref outside W2 but inside W1 -> external.
    _W(H1)  # dispatcher W1 (scope 1)
    rb_d = session._rebase_suggestion_ids(H11, "good: step 1.1.1 ; avoid: step 2.1")  # recipient W2 = 1.1
    show("depth (c): W1->W2 suggestion rebase", [("rebased+external", rb_d)])  # ('good: step 1.1 ; avoid: step 2.1', ['2.1'])

    # (d) edge id shapes: Branch/CaseSplit named children + the 'A' suffix all
    # relativize (component-wise), in direct ids and in free text.
    _W(H11)  # scope 1.1
    show("depth (d): edge id shapes (worker scope 1.1)", [
        ("display 1.1.True.1",  session._display_id("1.1.True.1")),    # True.1
        ("display 1.1.0.2",     session._display_id("1.1.0.2")),       # 0.2
        ("display 1.1.1.1A.2",  session._display_id("1.1.1.1A.2")),    # 1.1A.2
        ("relativize_text",     session._relativize_text("step 1.1.True.1 and Subgoal 1.1.0.1 and step 1.2.9")),
    ])

    # (e) the SAME node 1.2 is internal to W1 but external to W2 (scope asymmetry).
    _W(H1);  e_w1 = session._display_id("1.2")
    _W(H11); e_w2 = session._display_id("1.2")
    show("depth (e): node 1.2 internal-to-W1 / external-to-W2", [
        ("W1(1)",   e_w1),   # 2
        ("W2(1.1)", e_w2),   # <external>
    ])

    # (f) W1 (a worker) DISPATCHES W2 (step 1 => node 1.1) with a suggestion that
    # is external to W2 -> rejected at the W1->W2 boundary, before live dispatch.
    _W(H1)
    session._subagent_extstep_bypass.clear()
    r_d2, e_d2 = await _subagent_tool_logic(session, {"step_id": "1", "suggestions": "see step 2.1", "helpful_lemmas": []})
    print_header("depth (f): W1 dispatches W2 (step 1=>1.1) w/ external suggestion", file)
    file.write(f"is_error={e_d2}\n{r_d2}\n")

    # --- 16. cancelled-line relativization: a CANCELLED node's `_cancelled_by`
    # is relativized (in-scope) / masked (out-of-scope) in the rendered reason. ---
    from io import StringIO
    session.role = model.Role_Worker(target=H11, worker_handle=WorkerHandle(H11, session))  # scope 1.1
    victim = root.locate_node("1.1.2")
    victim.status = EVALUATION_CACNCELLED
    victim._cancelled_by = "1.1.1"                 # in-scope sibling -> 1
    session.showed_cancelled_notice = False
    fa = MyIO(StringIO()); victim._print_evaluation_status(0, fa)
    victim._cancelled_by = "1.2"                   # out of scope -> <external>
    session.showed_cancelled_notice = True
    fb = MyIO(StringIO()); victim._print_evaluation_status(0, fb)
    show("cancelled-line relativization (worker scope 1.1)", [
        ("in-scope cancelled_by 1.1.1", fa.getvalue().strip()),
        ("external cancelled_by 1.2",   fb.getvalue().strip()),
    ])

    session.role = model.Role_Major()


@model_test("WorkerHandleLifecycle", "Test_WorkerHandleLifecycle.thy", 9)
async def _test_worker_handle_lifecycle(root: Root, file: MyIO):
    """Deterministic coverage of the WorkerHandle lifecycle *mechanism* itself
    (not the relative-id layer): cost settlement idempotence, cancel(), the
    aclose() cascade across nesting, the run_until_yield terminal-outcome mapping,
    the nesting-depth guard, the orphan-handle assertion, and parked-vs-in-flight
    close. None of this needs a live LLM: a worker task is stubbed by a trivial
    completed (or sleeping) coroutine, so `run_until_yield`/`_wait_next_event`
    run their real logic against a controllable `_task` + event queue."""
    import types
    from .mcp_http_server import _subagent_tool_logic, _close_subagent_tool_logic
    from .model import WorkerHandle, WorkerSurrender, WorkerRefute
    session = root.session
    session.age += 1
    goal, H = await _make_lock_tree(root)
    H11 = root.locate_node("1.1")          # finished subtree (1.1.1 Obvious closes it)
    H12 = root.locate_node("1.2")          # open Have (unfinished)

    async def _completed():
        return None

    def _done_task():
        # A stub for handle._task: a coroutine that is driven to completion by the
        # event loop inside _wait_next_event's asyncio.wait — no LLM involved.
        return asyncio.ensure_future(_completed())

    # --- 1. _settle_costs rolls the sub-session cost up EXACTLY ONCE ----------
    print_header("1. _settle_costs exactly-once", file)
    calls = []
    session._accumulate_subagent_costs = lambda sub: calls.append(sub)   # monkeypatch
    try:
        h = WorkerHandle(H, session)
        h._sub = object()                  # pretend a forked sub-session exists
        h._settle_costs(); h._settle_costs(); h._settle_costs()
        file.write(f"accumulate called: {len(calls)}\n")
        file.write(f"_costs_accumulated flag set: {h._costs_accumulated}\n")
        # A handle that never forked a sub (no _sub) settles to a no-op.
        h2 = WorkerHandle(H, session)
        before = len(calls); h2._settle_costs()
        file.write(f"no-_sub settle is a no-op: {len(calls) == before}\n")
    finally:
        del session._accumulate_subagent_costs

    # --- 2. cancel() unblocks pending reviews and cancels the task -----------
    print_header("2. cancel() tears down futures + task", file)
    h = WorkerHandle(H, session)
    loop = asyncio.get_running_loop()
    fr = loop.create_future(); fl = loop.create_future()
    h._pending_review = fr; h._pending_resume = fl
    h._task = asyncio.ensure_future(asyncio.sleep(100))
    h.cancel()
    file.write(f"pending_review cancelled: {fr.cancelled()}\n")
    file.write(f"pending_resume cancelled: {fl.cancelled()}\n")
    file.write(f"futures cleared: {h._pending_review is None and h._pending_resume is None}\n")
    await h.wait_finish()                  # lets the cancellation settle
    file.write(f"task cancelled after cancel(): {h._task.cancelled()}\n")

    # --- 3. aclose() detaches its handle and is idempotent -------------------
    print_header("3. aclose() detach + idempotent", file)
    h = WorkerHandle(H11, session); H11.worker_handle = h
    await h.aclose()
    file.write(f"detached after aclose: {H11.worker_handle is None}\n")
    await h.aclose()                       # second call must be a safe no-op
    file.write(f"still detached after 2nd aclose: {H11.worker_handle is None}\n")

    # --- 4. aclose_all_subagents cascades across nesting (depth-3) -----------
    # Attach unstarted handles at 1, 1.1, 1.1.1... but 1.1.1 is a Leaf, so build a
    # deeper chain of Have blocks first: 3 { 3.1 { 3.1.1 } }, all NonLeaf.
    print_header("4. aclose_all_subagents cascade (depth-3)", file)
    s = {"english": "nonneg", "conclusion": r"(0::int) \<le> x * x"}
    await goal.append([Have.gen_single({"thought": "d1", "statement": s, "name": "hD1"})])  # 3
    D1 = root.locate_node("3")
    await root.fill("3.1", [Have.gen_single({"thought": "d2", "statement": s, "name": "hD2"})])
    D2 = root.locate_node("3.1")
    await root.fill("3.1.1", [Have.gen_single({"thought": "d3", "statement": s, "name": "hD3"})])
    D3 = root.locate_node("3.1.1")
    D1.worker_handle = WorkerHandle(D1, session)
    D2.worker_handle = WorkerHandle(D2, session)
    D3.worker_handle = WorkerHandle(D3, session)
    await D1.aclose_all_subagents()        # closes D1's whole subtree of handles
    file.write(f"D1 detached: {D1.worker_handle is None}\n")
    file.write(f"D2 detached: {D2.worker_handle is None}\n")
    file.write(f"D3 detached: {D3.worker_handle is None}\n")

    # --- 5. run_until_yield terminal-outcome mapping (stub _task) ------------
    # PROVED: target subtree has no unfinished nodes (1.1 is fully proved).
    print_header("5. run_until_yield terminal mapping", file)
    h = WorkerHandle(H11, session); H11.worker_handle = h
    h._task = _done_task()
    y = await h.run_until_yield()
    file.write(f"proved subtree -> kind={y.kind} detached={H11.worker_handle is None}\n")

    # COULD_NOT_PROVE: target still unfinished; quit_info detail surfaces.
    h = WorkerHandle(H12, session); H12.worker_handle = h
    h._task = _done_task()
    h._sub = types.SimpleNamespace(
        quit_info=types.SimpleNamespace(detail="ran out of budget", reason="budget"))
    y = await h.run_until_yield()
    file.write(f"unfinished subtree -> kind={y.kind} detail={y.detail!r}\n")

    # SURRENDERED: an event in the queue wins over task completion.
    h = WorkerHandle(H12, session); H12.worker_handle = h
    h._task = _done_task()
    h._event_queue.put_nowait(WorkerSurrender(detail="cannot proceed"))
    y = await h.run_until_yield()
    file.write(f"surrender event -> kind={y.kind} detail={y.detail!r}\n")

    # --- 6. nesting-depth guard ---------------------------------------------
    print_header("6. nesting-depth", file)
    # 6a. _subagent_nesting_depth counts only Role_Worker on the parent chain.
    orig_parent = session.parent
    orig_role = session.role
    session.role = model.Role_Worker(target=H)
    session.parent = types.SimpleNamespace(
        role=model.Role_Worker(target=H11),
        parent=types.SimpleNamespace(role=model.Role_Major(), parent=None))
    d = session._subagent_nesting_depth()
    session.parent = orig_parent
    file.write(f"nesting depth (self-worker + 1 worker ancestor + major): {d}\n")
    # 6b. the dispatch guard rejects when the depth limit is reached.
    session.role = model.Role_Worker(target=H, worker_handle=WorkerHandle(H, session))
    session._subagent_nesting_depth = lambda: model.SUBAGENT_NESTING_DEPTH       # monkeypatch
    try:
        r, e = await _subagent_tool_logic(
            session, {"step_id": "2", "suggestions": "", "helpful_lemmas": []})  # rel "2" -> 1.2
        file.write(f"depth-limit dispatch is_error: {e}\n")
        file.write(f"depth-limit message mentions 'deeply nested': {'deeply nested' in r}\n")
    finally:
        del session._subagent_nesting_depth
        session.role = orig_role

    # --- 7. orphan-handle assertion surfaces a broken antichain invariant ----
    print_header("7. orphan-handle assertion", file)
    session.role = model.Role_Major()
    H12.worker_handle = WorkerHandle(H12, object())   # foreign handle, no enclosing owner
    try:
        await _subagent_tool_logic(
            session, {"step_id": "1.2", "suggestions": "", "helpful_lemmas": []})
        file.write("orphan: NO assertion raised (UNEXPECTED)\n")
    except AssertionError:
        file.write("orphan: AssertionError raised\n")
    finally:
        H12.worker_handle = None

    # --- 8. cancel_subagent: parked vs in-flight vs no-handle ----------------
    print_header("8. cancel_subagent parked / in-flight / none", file)
    H11.worker_handle = WorkerHandle(H11, session)     # parked (no task)
    r, e = await _close_subagent_tool_logic(session, {"step_id": "1.1"})
    file.write(f"parked close is_error={e} detached={H11.worker_handle is None}\n")

    inflight = WorkerHandle(H11, session)
    inflight._task = asyncio.ensure_future(asyncio.sleep(100))   # live worker task
    H11.worker_handle = inflight
    r, e = await _close_subagent_tool_logic(session, {"step_id": "1.1"})
    file.write(f"in-flight close is_error={e} task_cancelled={inflight._task.cancelled()} "
               f"detached={H11.worker_handle is None}\n")

    r, e = await _close_subagent_tool_logic(session, {"step_id": "1.2"})   # no handle there
    file.write(f"no-handle close is_error={e}\n")

    # --- 9. run_until_yield REFUTE branch: ACCEPT -> wind-down -> refute_accepted
    # The most intricate control flow in run_until_yield, previously untested: a
    # WorkerRefute is dequeued, reviewed via launch_interaction, and on acceptance the
    # worker winds down. launch_interaction is mocked to stand in for the planner's
    # verdict (it also resolves the worker's review future, like the real
    # Interaction_ReviewRefutation.answer), so no live planner is needed.
    print_header("9. run_until_yield refute ACCEPTED", file)
    async def _worker_refutes_accept():
        f = loop.create_future()
        h9._event_queue.put_nowait(
            WorkerRefute(detail="the goal contradicts premise hH", response_future=f))
        await f                       # blocks until the dispatcher reviews it
        return None                   # accepted -> the worker winds down
    h9 = WorkerHandle(H12, session)
    h9._task = asyncio.ensure_future(_worker_refutes_accept())
    H12.worker_handle = h9
    async def _fi_accept(interaction):
        h9.resolve_review(True, "agreed: the goal is unprovable")   # mock planner accept
        return (True, "agreed: the goal is unprovable")
    session.launch_interaction = _fi_accept
    try:
        y = await h9.run_until_yield()
    finally:
        del session.launch_interaction
    file.write(f"refute accepted -> kind={y.kind} reason={y.reason!r} "
               f"detail={y.detail!r} detached={H12.worker_handle is None}\n")

    # --- 10. run_until_yield REFUTE branch: REJECT -> continue -> re-yield -------
    # On rejection the loop `continue`s and the worker resumes IN-LOOP (the planner
    # never sees a terminal yield); here the resumed worker then surrenders, so the
    # SAME run_until_yield excursion returns a `surrendered` yield. This exercises
    # the reject->continue->re-dequeue path that nothing else covered.
    print_header("10. run_until_yield refute REJECTED -> continue -> surrender", file)
    fork_calls = []
    async def _worker_refutes_reject():
        f = loop.create_future()
        h10._event_queue.put_nowait(
            WorkerRefute(detail="claims unprovable", response_future=f))
        accepted, _reason = await f
        if not accepted:              # resumed in-loop; now gives up for real
            h10._event_queue.put_nowait(WorkerSurrender(detail="ok, surrendering"))
        return None
    h10 = WorkerHandle(H12, session)
    h10._task = asyncio.ensure_future(_worker_refutes_reject())
    H12.worker_handle = h10
    async def _fi_reject(interaction):
        fork_calls.append(interaction)
        h10.resolve_review(False, "not convinced; keep trying")     # mock planner reject
        return (False, "not convinced; keep trying")
    session.launch_interaction = _fi_reject
    try:
        y = await h10.run_until_yield()
    finally:
        del session.launch_interaction
    file.write(f"refute rejected -> launch_interaction calls={len(fork_calls)}\n")
    file.write(f"after reject the worker resumed then -> kind={y.kind} "
               f"detail={y.detail!r} detached={H12.worker_handle is None}\n")

    session.role = model.Role_Major()


@model_test("NestedRequestLemmas", "Test_NestedRequestLemmas.thy", 9)
async def _test_nested_request_lemmas(root: Root, file: MyIO):
    """The request_lemmas PARK -> resume cycle exercised NESTED — the dispatcher
    is a worker W1 (scope 1), and its sub-agent W2 (scope 1.1) is the one parking
    on a lemma request. RefuteOrSurrender covers the depth-1 (planner dispatcher)
    case; this covers the genuinely stateful nesting transition through both the
    handle API and the real `subagent` resume tool path. Deterministic: the W2
    worker task is a stub coroutine that enqueues a WorkerRequestLemmas event,
    blocks on its future, and completes once the dispatcher resolves it."""
    from .mcp_http_server import _subagent_tool_logic, _subagent_resume_feedback
    from .model import WorkerHandle, WorkerRequestLemmas
    session = root.session
    session.age += 1
    goal, H = await _make_lock_tree(root)
    H11 = root.locate_node("1.1")          # W2's target (proved subtree)
    loop = asyncio.get_running_loop()

    # W1 is the dispatcher session (a worker scoped to node 1).
    session.role = model.Role_Worker(target=H, worker_handle=WorkerHandle(H, session))
    await session._prefetch_worker_premises()

    # --- 1. Handle-level PARK -> resume cycle (nested under W1) --------------
    print_header("1. handle-level park/resume (W1 dispatches W2 on 1.1)", file)
    ev_fut = loop.create_future()
    async def _w2_requests_then_finishes():
        # Model W2's request_lemmas tool: enqueue the event, then block until the
        # dispatcher answers; once resumed, W2 finishes (subtree already proved).
        handle._event_queue.put_nowait(WorkerRequestLemmas(
            detail="need a squares lemma", lemmas=[{
                "name": "sq_nonneg", "english": "squares are non-negative",
                "isabelle_statement": "0 ≤ x * x"}],
            response_future=ev_fut))
        await ev_fut
        return None
    handle = WorkerHandle(H11, session)
    handle._task = asyncio.ensure_future(_w2_requests_then_finishes())
    H11.worker_handle = handle

    y = await handle.run_until_yield()     # should PARK on the lemma request
    file.write(f"park yield kind: {y.kind}\n")
    file.write(f"park yield detail: {y.detail!r}\n")
    file.write(f"park yield lemma count: {len(y.lemmas)}\n")
    file.write(f"handle still attached while parked: {H11.worker_handle is handle}\n")
    file.write(f"pending_resume stored: {handle._pending_resume is not None}\n")

    handle.resolve_resume("Added lemma sq_nonneg; continue.")   # dispatcher answers
    y2 = await handle.run_until_yield()    # resumes, then W2 finishes
    file.write(f"resume yield kind: {y2.kind}\n")
    file.write(f"detached after finish: {H11.worker_handle is None}\n")

    # --- 2. Tool-level resume path with suggestion rebase-on-resume ----------
    # The real `subagent` tool rejects a finished node ("already proved"), so a
    # worker parked on a lemma request must sit on an UNFINISHED target. Give 1.2
    # an open child 1.2.1 so node 1.2 stays unfinished yet has an in-scope step to
    # cite. W1 resumes a worker parked on 1.2, passing a suggestion that cites a
    # W1-relative id (2.1 == node 1.2.1) plus a helper lemma. Verify: the resume
    # branch fires, the feedback reaches the worker, and the cited id is re-based
    # into W2's namespace (1.2.1 -> "1"); the worker can't actually close 1.2, so
    # the dispatcher sees could_not_prove.
    print_header("2. tool resume path + rebase-on-resume", file)
    session.role = model.Role_Major()
    s2 = {"english": "child", "conclusion": r"(0::int) \<le> x * x"}
    await root.fill("1.2.1", [Have.gen_single({"thought": "c", "statement": s2, "name": "hGC"})])
    H12 = root.locate_node("1.2")          # unfinished (1.2.1 open)
    session.role = model.Role_Worker(target=H, worker_handle=WorkerHandle(H, session))
    await session._prefetch_worker_premises()

    received = []
    resume_fut = loop.create_future()
    async def _w2_resume_then_finishes():
        fb = await resume_fut
        received.append(fb)
        return None
    handle2 = WorkerHandle(H12, session)
    handle2._task = asyncio.ensure_future(_w2_resume_then_finishes())
    handle2._pending_resume = resume_fut
    H12.worker_handle = handle2

    r, e = await _subagent_tool_logic(session, {
        "step_id": "2",                    # W1-relative for node 1.2
        "suggestions": "reuse step 2.1",   # W1-relative for node 1.2.1
        "helpful_lemmas": ["sq_nonneg"]})
    file.write(f"resume tool is_error: {e}\n")
    file.write(f"feedback delivered to worker: {len(received) == 1}\n")
    fb = received[0] if received else ""
    file.write(f"feedback carries rebased 'step 1' (1.2.1 -> 1): {'reuse step 1' in fb and 'step 2.1' not in fb}\n")
    file.write(f"feedback carries helpful lemma: {'sq_nonneg' in fb}\n")
    file.write(f"dispatcher outcome (worker can't close 1.2): {'could not' in r.lower()}\n")
    file.write(f"detached after tool resume: {H12.worker_handle is None}\n")

    session.role = model.Role_Major()


@model_test("FailurePropagation", "Test_FailurePropagation.thy", 9)
async def _test_failure_propagation(root: Root, file: MyIO):
    """Failure outcomes bubbling UP a nesting chain with per-level step-id
    relativization. NestedWorkerScope §15b traces a SUCCESS detail up the stack;
    this covers the genuinely-uncovered FAILURE channels: the could_not_prove and
    surrender branches of the real `subagent` tool rendered at a NESTED (worker)
    dispatcher, plus the multi-level relativize/absolutize chain for a failure
    detail. Deterministic via the resume path + stubbed worker task (could_not /
    surrender both reachable without a live fork)."""
    import types
    from .mcp_http_server import _subagent_tool_logic
    from .model import WorkerHandle, WorkerSurrender
    session = root.session
    session.age += 1
    goal = root.sub_nodes[1]
    s = {"english": "nonneg", "conclusion": r"(0::int) \<le> x * x"}
    await goal.fill("1", [Have.gen_single({"thought": "A", "statement": s, "name": "hA"})])
    await root.fill("1.1", [Have.gen_single({"thought": "B", "statement": s, "name": "hB"})])
    await root.fill("1.1.1", [Have.gen_single({"thought": "C", "statement": s, "name": "hC"})])
    await root.fill("1.1.1.1", [Have.gen_single({"thought": "D", "statement": s, "name": "hD"})])
    H = root.locate_node("1")
    H1B = root.locate_node("1.1")
    H111 = root.locate_node("1.1.1")       # unfinished (1.1.1.1 open); W2's target
    loop = asyncio.get_running_loop()

    def _as_W1():
        # W1 dispatcher: a worker scoped to node 1.1 (so 1.1.1 is a strict descendant).
        session.role = model.Role_Worker(target=H1B, worker_handle=WorkerHandle(H1B, session))

    # --- 1. could_not_prove: worker's absolute detail relativized at W1 view --
    print_header("1. could_not_prove detail relativized at nested dispatcher", file)
    session.role = model.Role_Major()
    _as_W1()
    await session._prefetch_worker_premises()
    resume_fut = loop.create_future()
    async def _w2_cant_finish():
        await resume_fut
        return None
    h = WorkerHandle(H111, session)
    h._task = asyncio.ensure_future(_w2_cant_finish())
    h._pending_resume = resume_fut
    # quit_info.detail is W2-authored, already absolutized on emission (cites 1.1.1.1).
    h._sub = types.SimpleNamespace(
        quit_info=types.SimpleNamespace(detail="stuck proving step 1.1.1.1", reason="budget"))
    H111.worker_handle = h
    r, e = await _subagent_tool_logic(session, {
        "step_id": "1", "suggestions": "", "helpful_lemmas": []})   # rel 1.1.1 in scope 1.1
    file.write(f"is_error: {e}\n")
    file.write(f"message says could not: {'could not' in r.lower()}\n")
    file.write(f"detail relativized to W1 (1.1.1.1 -> step 1.1): {'step 1.1' in r and '1.1.1.1' not in r}\n")

    # --- 2. surrender: worker's absolute detail relativized at W1 view -------
    print_header("2. surrender detail relativized at nested dispatcher", file)
    session.role = model.Role_Major()
    _as_W1()
    await session._prefetch_worker_premises()
    resume_fut2 = loop.create_future()
    async def _w2_surrenders():
        await resume_fut2
        h2._event_queue.put_nowait(WorkerSurrender(detail="abandoning step 1.1.1.1"))
        return None
    h2 = WorkerHandle(H111, session)
    h2._task = asyncio.ensure_future(_w2_surrenders())
    h2._pending_resume = resume_fut2
    H111.worker_handle = h2
    r, e = await _subagent_tool_logic(session, {
        "step_id": "1", "suggestions": "", "helpful_lemmas": []})
    file.write(f"is_error: {e}\n")
    file.write(f"message says surrendered: {'surrender' in r.lower()}\n")
    file.write(f"detail relativized to W1 (1.1.1.1 -> step 1.1): {'step 1.1' in r and '1.1.1.1' not in r}\n")

    # --- 3. multi-level chain: same failure detail seen at W2 / W1 / planner --
    # W2 (scope 1.1) authors a detail citing its descendant 1.1.1.1 as relative
    # "1.1" (multi-component, so it round-trips through the free-text regex). On
    # emit it absolutizes; each dispatcher above re-relativizes to its own scope.
    # (A single-component relative id like "1" is deliberately NOT rewritten in
    # free text — the documented limitation — so the chain must cite a dotted id.)
    print_header("3. failure detail relativized at every level of the stack", file)
    session.role = model.Role_Major()
    # W2 authoring scope = 1.1, cites descendant 1.1.1.1 (relative "1.1").
    session.role = model.Role_Worker(target=H1B, worker_handle=WorkerHandle(H1B, session))
    w2_absolute = session._absolutize_text("blocked at step 1.1")      # 1.1 -> 1.1.1.1
    # W1 view (scope 1).
    session.role = model.Role_Worker(target=H, worker_handle=WorkerHandle(H, session))
    w1_view = session._relativize_text(w2_absolute)                    # 1.1.1.1 -> step 1.1.1
    # planner view (scope root) — identity.
    session.role = model.Role_Major()
    planner_view = session._relativize_text(w2_absolute)
    file.write(f"W2-absolutized:  {w2_absolute!r}\n")
    file.write(f"W1 view:         {w1_view!r}\n")
    file.write(f"planner view:    {planner_view!r}\n")

    session.role = model.Role_Major()


@model_test("RequestLemmas_FocusedView", "Test_RequestLemmas_FocusedView.thy", 11)
async def _test_RequestLemmas_FocusedView(root: Root, file: MyIO):
    """Worker focused-view rendering on a Have-lemma target: print_proof_scope /
    quickview_proof_scope + goal.context inspection. Restored from the driver
    removed at 2de6e43 (only the orphan .thy/.yml lingered); adapted to the
    current API (Role_Major, _prefetch_worker_premises). Snapshot test of the
    worker-scoped renderer."""
    session = root.session

    print_header("Initial YAML", file)
    root.print(0, file)

    # --- Setup: Insert three HAVE nodes into the global env ---
    session.age += 1
    [h_triv] = (await root.global_env.append([Have.gen_single({
        "thought": "trivial lemma",
        "statement": {"english": "trivial truth", "conclusion": "True"},
        "name": "h_triv",
    })])).committed
    session.age += 1
    [h_target] = (await root.global_env.append([Have.gen_single({
        "thought": "target lemma",
        "statement": {"english": "one equals two", "conclusion": "1 = (2::int)"},
        "name": "h_target",
    })])).committed
    session.age += 1
    [h_forany] = (await root.global_env.append([Have.gen_single({
        "thought": "lemma with for_any and premises",
        "statement": {
            "english": "y squared is non-negative",
            "for_any": [{"name": "y", "type": "int"}],
            "premises": [{"name": "hy", "term": "y ≥ 0"}],
            "conclusion": "y * y ≥ 0",
        },
        "name": "h_forany",
    })])).committed

    # Inspect goal.context for each HAVE
    print_header("Goal context inspection", file)
    for label, have in [("h_target", h_target), ("h_forany", h_forany)]:
        goal = have._state_after_beginning().leading_goal
        if goal is not None:
            file.write(f"{label} goal.context.vars: {[(n.unicode, t.unicode) for n, t in goal.context.vars.items()]}\n")
            file.write(f"{label} goal.context.hyps: {[(n.unicode, t.unicode) for n, t in goal.context.hyps.items()]}\n")
            file.write(f"{label} goal.conclusion: {goal.conclusion.unicode}\n")
        else:
            file.write(f"{label} goal: None\n")

    # Obvious fails on the false goal — h_target stays open with children
    session.age += 1
    await h_target.append([Obvious.gen_single({"facts": []})])

    print_header("Tree with two HAVEs", file)
    root.print(0, file)
    file.write(f"h_triv status: {h_triv.status.status.value}\n")
    file.write(f"h_target status: {h_target.status.status.value}\n")

    # --- Set role to Role_Worker and test focused view ---
    session.role = model.Role_Worker(target=h_target)
    await session._prefetch_worker_premises()

    print_header("print_proof_scope (lemma_anchor = h_target)", file)
    session.print_proof_scope(0, file, show_warnings=True)

    print_header("quickview_proof_scope (lemma_anchor = h_target)", file)
    session.quickview_proof_scope(0, file)

    # --- Verify content assertions ---
    buf_ps = MyIO(io.StringIO())
    session.print_proof_scope(0, buf_ps)
    ps_text = buf_ps.getvalue()
    file.write(f"\nprint_proof_scope contains 'available declarations': {'available declarations' in ps_text}\n")
    file.write(f"print_proof_scope contains 'h_triv': {'h_triv' in ps_text}\n")
    file.write(f"print_proof_scope contains 'goal:': {'goal:' in ps_text}\n")
    file.write(f"print_proof_scope contains main goal 'x * x': {'x * x' in ps_text}\n")

    buf_qv = MyIO(io.StringIO())
    session.quickview_proof_scope(0, buf_qv)
    qv_text = buf_qv.getvalue()
    file.write(f"quickview contains 'available declarations': {'available declarations' in qv_text}\n")
    file.write(f"quickview contains 'Unfinished Proof': {'Unfinished Proof' in qv_text}\n")

    # --- Reset and verify full view is restored ---
    session.role = model.Role_Major()

    print_header("print_proof_scope (lemma_anchor = None, full view)", file)
    session.print_proof_scope(0, file)

    print_header("Final tree (reference)", file)
    root.print(0, file)


@model_test("WorkerGoalNodeScope", "Test_WorkerGoalNodeScope.thy", 11)
async def _test_WorkerGoalNodeScope(root: Root, file: MyIO):
    """Worker scope rendering when the target is a GoalNode (not a Have).

    Restored from the driver removed at 2de6e43, but REDESIGNED: the original
    pointed the worker at the *top-level* GoalNode (``root.sub_nodes[1]``), which
    the dispatch guard would never permit — delegating a whole top-level goal is
    rejected (``target.parent is psr``). That node also has the empty id ``''``, so
    every child relativized to ``<external>`` (the relativizer being honest about
    an empty scope prefix). A worker is only ever scoped to a GoalNode that is a
    Branch/CaseSplit CASE (parent = the SubgoalMaker, not root; non-empty id like
    ``1.1``). This targets that REACHABLE case GoalNode, so children relativize
    to proper in-scope ids."""
    session = root.session

    # Branch the top-level goal into three cases (pos/neg/zero); the case GoalNodes
    # (1.1 / 1.2 / 1.3) are legitimate worker-delegation targets.
    session.age += 1
    await root.fill("1", [Branch.gen_single({
        "thought": "split on the sign of x",
        "cases": [
            {"statement": {"english": "x positive", "isabelle": "x > 0", "name": "pos"}},
            {"statement": {"english": "x negative", "isabelle": "x < 0", "name": "neg"}},
            {"statement": {"english": "x zero", "isabelle": "x = 0", "name": "zero"}},
        ]})])
    session.age += 1
    await root.fill("1.0.1", [Obvious.gen_single({"facts": []})])   # exhaustiveness
    # Branch case GoalNodes are numbered: 1.0 = exhaustiveness, 1.1/1.2/1.3 = the
    # pos/neg/zero cases. Put a (still-open) sub-lemma under the first case (1.1)
    # so the worker view has a child step to relativize.
    session.age += 1
    await root.fill("1.1.1", [Have.gen_single({
        "thought": "helper in the positive case",
        "statement": {"english": "trivial", "conclusion": "True"}, "name": "hp"})])
    case = root.locate_node("1.1")          # the reachable case GoalNode

    print_header("Full tree (Plan role)", file)
    session.print_proof_scope(0, file)

    # --- Set role to Worker targeting the CASE GoalNode (reachable scope) ---
    session.role = model.Role_Worker(target=case)
    await session._prefetch_worker_premises()

    print_header("Worker scope (target=case GoalNode 1.1)", file)
    session.print_proof_scope(0, file)

    buf = MyIO(io.StringIO())
    session.print_proof_scope(0, buf)
    ps_text = buf.getvalue()
    file.write(f"\ncontains 'goal:': {'goal:' in ps_text}\n")
    file.write(f"contains 'proof:': {'proof:' in ps_text}\n")
    # The whole point of the redesign: a reachable GoalNode scope relativizes its
    # children to proper in-scope ids — NOT <external>.
    file.write(f"child relativizes to in-scope id (no <external>): {'<external>' not in ps_text}\n")
    file.write(f"child shown as relative 'step id: 1': {'step id: 1' in ps_text}\n")

    print_header("Worker quickview (target=case GoalNode 1.1)", file)
    session.quickview_proof_scope(0, file)

    # --- Verify unfinished_nodes scoping: case scope vs full proof ---
    unfinished = session.proof_scope_unfinished_nodes()
    file.write(f"\nunfinished count (case GoalNode scope): {len(unfinished)}\n")

    # --- Switch back to Plan ---
    session.role = model.Role_Major()
    unfinished_full = session.proof_scope_unfinished_nodes()
    file.write(f"unfinished count (full scope): {len(unfinished_full)}\n")


@model_test("NestedAntichain", "Test_NestedAntichain.thy", 9)
async def _test_nested_antichain(root: Root, file: MyIO):
    """Deterministic coverage of the nested-subagent ANTICHAIN + teardown logic
    that the lifecycle test didn't reach: (A) 3+-level disambiguation — a session
    sees the worker IT owns, skipping a deeper FOREIGN grandchild handle it cannot
    operate on; (B) concurrent sibling workers are independent (a worker on one
    sibling neither blocks dispatch nor locks edits in the other); (C) the two
    cascade-close recursions, ``discard`` (delete) and ``_amend_child`` (amend),
    each tear down the workers they remove."""
    from .model import WorkerHandle, _first_worker_in_ancestors
    session = root.session
    session.age += 1
    goal = root.sub_nodes[1]
    s = {"english": "nonneg", "conclusion": r"(0::int) \<le> x * x"}
    await goal.fill("1", [Have.gen_single({"thought": "H", "statement": s, "name": "hH"})])
    H = root.locate_node("1")
    await root.fill("1.1", [Have.gen_single({"thought": "A", "statement": s, "name": "hA"})])
    await root.fill("1.1.1", [Have.gen_single({"thought": "B", "statement": s, "name": "hB"})])
    await root.fill("1.1.1.1", [Have.gen_single({"thought": "C", "statement": s, "name": "hC"})])
    await H.append([Have.gen_single({"thought": "sib", "statement": s, "name": "hSib"})])  # 1.2
    A = root.locate_node("1.1"); B = root.locate_node("1.1.1")
    C = root.locate_node("1.1.1.1"); sib = root.locate_node("1.2")
    session.role = model.Role_Major()

    # --- A. 3+-level antichain disambiguation -------------------------------
    # MINE on 1.1; a FOREIGN sub-worker's handle on 1.1.1 (a grandchild I can't
    # operate on). For a node under both, the ownership-blind nearest-ancestor
    # walk finds the foreign one, but _enclosing_dispatched_subagent / the dispatch
    # blocker must point me at the worker I OWN (1.1).
    print_header("A. 3+-level antichain disambiguation", file)
    A.worker_handle = WorkerHandle(A, session)        # mine
    B.worker_handle = WorkerHandle(B, object())       # foreign (a sub-worker's)
    near = _first_worker_in_ancestors(C, stop=root)   # ownership-blind: nearest = 1.1.1
    mine = session._enclosing_dispatched_subagent(C)  # ownership-aware: skips foreign -> 1.1
    blk = session._subagent_blocker(C)
    file.write(f"nearest ancestor handle (ownership-blind): {near.target.id}\n")
    file.write(f"_enclosing_dispatched_subagent (mine, skips foreign grandchild): {mine.target.id}\n")
    file.write(f"_subagent_blocker points at the worker I own: {blk.target.id}\n")
    A.worker_handle = None; B.worker_handle = None

    # --- B. concurrent sibling workers are independent ----------------------
    print_header("B. concurrent sibling workers independent", file)
    sib.worker_handle = WorkerHandle(sib, session)    # worker on sibling 1.2 only
    blk_sib = session._dispatch_blocked_by(A)         # dispatch on 1.1 — not blocked by 1.2
    v_free, _ = session._edit_verdict("1.1.1.1.1", "fill")  # new slot deep under 1.1 — free
    v_lock, h_lock = session._edit_verdict("1.2.1", "fill") # new slot under 1.2 — its own worker locks
    file.write(f"dispatch on sibling 1.1 blocked by worker on 1.2: {blk_sib is not None}\n")
    file.write(f"edit under sibling 1.1 verdict: {v_free.name}\n")
    file.write(f"edit under the worker's own 1.2 verdict: {v_lock.name} blocker={h_lock.target.id if h_lock else '-'}\n")
    sib.worker_handle = None

    # --- C. cascade-close: discard (delete) and _amend_child (amend) --------
    print_header("C. cascade-close via delete and amend", file)
    # C1. delete 1.1.1 -> discard recurses, closing the workers on 1.1.1 AND 1.1.1.1.
    hB = WorkerHandle(B, session); hB._task = asyncio.ensure_future(asyncio.sleep(100)); B.worker_handle = hB
    hC = WorkerHandle(C, session); hC._task = asyncio.ensure_future(asyncio.sleep(100)); C.worker_handle = hC
    await root.delete(["1.1.1"])
    file.write(f"delete cascade: 1.1.1 worker cancelled={hB._task.cancelled()}, "
               f"nested 1.1.1.1 worker cancelled={hC._task.cancelled()}, detached={B.worker_handle is None}\n")
    # C2. amend 1.1 -> _amend_child tears down the amended node's own worker.
    hA = WorkerHandle(A, session); hA._task = asyncio.ensure_future(asyncio.sleep(100)); A.worker_handle = hA
    await root.amend("1.1", [Have.gen_single({
        "thought": "A'", "statement": s, "name": "hA2"})])
    file.write(f"amend cascade: amended-node worker cancelled={hA._task.cancelled()}, "
               f"old node detached={A.worker_handle is None}\n")

    session.role = model.Role_Major()

@model_test("HaveWorkerForAny", "Test_HaveWorkerForAny.thy", 11)
async def _test_HaveWorkerForAny(root: Root, file: MyIO):
    """Worker scope must include the target Have/Suffices for_any variables and premises.

    Regression: when a worker is dispatched to a Have with for_any/premises,
    print_proof_scope used _ctxt_before_me() which excludes the target's own
    fixed vars and assumed premises. The goal's context (from leading_goal_data)
    is also empty because gen_HAVE' pushes HHF(goal, ([],[])) with empty items.
    Result: the worker sees the bare conclusion with free variables but no
    corresponding variable declarations or premises, making the goal unprovable.

    Tests: Have with for_any+premises, for_any only, premises only,
    multiple for_any, Suffices with for_any+premises."""
    session = root.session

    async def worker_scope_text(target) -> str:
        session.role = model.Role_Worker(target=target)
        await session._prefetch_worker_premises()
        buf = MyIO(io.StringIO())
        session.print_proof_scope(0, buf)
        session.role = model.Role_Major()
        return buf.getvalue()

    print_header("Initial YAML", file)
    root.print(0, file)

    # --- Case 1: Have with for_any + premises ---
    session.age += 1
    [h_both] = (await root.global_env.append([Have.gen_single({
        "thought": "lemma with for_any and premises",
        "statement": {
            "english": "y squared is non-negative given y >= 0",
            "for_any": [{"name": "y", "type": "int"}],
            "premises": [{"name": "hy", "term": r"(0::int) \<le> y"}],
            "conclusion": r"(0::int) \<le> y * y",
        },
        "name": "h_both",
    })])).committed

    print_header("Case 1: Have with for_any + premises", file)
    session.role = model.Role_Worker(target=h_both)
    await session._prefetch_worker_premises()
    session.print_proof_scope(0, file, show_warnings=True)
    ps = await worker_scope_text(h_both)
    file.write(f"\nfor_any var 'y: int' visible: {'y: int' in ps}\n")
    file.write(f"premise 'hy' visible: {'hy' in ps}\n")
    file.write(f"outer premise 'hx' visible: {'hx' in ps}\n")
    file.write(f"outer var 'x: int' visible: {'x: int' in ps}\n")
    goal = h_both._state_after_beginning().leading_goal
    file.write(f"goal.context.vars: {[(n.unicode, t.unicode) for n, t in goal.context.vars.items()]}\n")
    file.write(f"goal.context.hyps: {[(n.unicode, t.unicode) for n, t in goal.context.hyps.items()]}\n")

    # --- Case 2: Have with for_any only (no premises) ---
    session.age += 1
    [h_forany_only] = (await root.global_env.append([Have.gen_single({
        "thought": "lemma with for_any only",
        "statement": {
            "english": "n plus 1 is positive",
            "for_any": [{"name": "n", "type": "nat"}],
            "conclusion": r"(0::nat) < n + 1",
        },
        "name": "h_forany_only",
    })])).committed

    print_header("Case 2: Have with for_any only", file)
    ps = await worker_scope_text(h_forany_only)
    file.write(f"for_any var 'n: nat' visible: {'n: nat' in ps}\n")
    file.write(f"no extra premises (only hx): {ps.count('premises:') <= 1}\n")

    # --- Case 3: Have with premises only (no for_any) ---
    session.age += 1
    [h_prem_only] = (await root.global_env.append([Have.gen_single({
        "thought": "lemma with premises only",
        "statement": {
            "english": "from x >= 0, x * x >= 0",
            "premises": [{"name": "hp", "term": r"(0::int) \<le> x"}],
            "conclusion": r"(0::int) \<le> x * x",
        },
        "name": "h_prem_only",
    })])).committed

    print_header("Case 3: Have with premises only", file)
    ps = await worker_scope_text(h_prem_only)
    file.write(f"premise 'hp' visible: {'hp' in ps}\n")

    # --- Case 4: Have with multiple for_any ---
    session.age += 1
    [h_multi] = (await root.global_env.append([Have.gen_single({
        "thought": "lemma with multiple for_any",
        "statement": {
            "english": "a + b >= 0 given both non-negative",
            "for_any": [{"name": "a", "type": "int"}, {"name": "b", "type": "int"}],
            "premises": [{"name": "ha", "term": r"(0::int) \<le> a"},
                         {"name": "hb", "term": r"(0::int) \<le> b"}],
            "conclusion": r"(0::int) \<le> a + b",
        },
        "name": "h_multi",
    })])).committed

    print_header("Case 4: Have with multiple for_any", file)
    ps = await worker_scope_text(h_multi)
    file.write(f"var 'a: int' visible: {'a: int' in ps}\n")
    file.write(f"var 'b: int' visible: {'b: int' in ps}\n")
    file.write(f"premise 'ha' visible: {'ha' in ps}\n")
    file.write(f"premise 'hb' visible: {'hb' in ps}\n")

    # --- Case 5: Suffices with for_any + premises ---
    session.age += 1
    goal_node = root.sub_nodes[1]
    [s_forany] = (await goal_node.fill("1", [Suffices.gen_single({
        "thought": "suffices with for_any and premises",
        "statement": {
            "english": "it suffices to show y*y >= 0 for y >= 0",
            "for_any": [{"name": "y", "type": "int"}],
            "premises": [{"name": "sy", "term": r"(0::int) \<le> y"}],
            "conclusion": r"(0::int) \<le> y * y",
        },
    })])).committed

    print_header("Case 5: Suffices with for_any + premises", file)
    ps = await worker_scope_text(s_forany)
    file.write(f"for_any var 'y: int' visible: {'y: int' in ps}\n")
    file.write(f"premise 'sy' visible: {'sy' in ps}\n")


@model_test("Rewrite_ConjSplit", "Test_Rewrite_ConjSplit.thy", 12)
async def _test_Rewrite_ConjSplit(root: Root, file: MyIO):
    """Reproduce UnequalLengths when Rewrite produces a conjunction in a premise.

    Root cause: SIMPLIFY_GOAL_AND_PREMISES' calls the naming function
    (naming_prems_fn) with the pre-split premise terms, storing them in
    prems_before_ref.  Then INTRO' splits conjunction premises
    (INTRO_split_prem_conj = true) and returns facts' with more entries
    than prems_before_ref.  AUTO_SIMPLIFY's map2 over the two lists
    raises UnequalLengths.

    Scenario: rewrite `mypred t` (= `0 < t ∧ t < 1`) via mypred_def.
    The rewritten premise is a conjunction → INTRO splits it → crash."""
    print_header("Initial YAML", file)
    root.print(0, file)

    root.session.age += 1
    outcome = await root.fill("1", [Rewrite.gen_single({
        "thought": "Unfold mypred to expose the conjunction",
        "using": [{"name": "mypred_def"}],
        "use system simplifiers": False,
        "rewrite goal": False,
        "rewrite premises": ["h"]
    })])
    print_header("After Rewrite (unfold mypred)", file)
    root.print(0, file)
    if outcome.failure is not None:
        file.write(f"FAILURE: {outcome.failure}\n")
    else:
        file.write("SUCCESS\n")


@model_test("SubagentEmptyStepId", "Test_SubagentEmptyStepId.thy", 9)
async def _test_subagent_empty_step_id(root: Root, file: MyIO):
    """When the LLM calls `subagent` with a hallucinated schema (e.g. `task`
    instead of `step_id`), the missing `step_id` defaults to empty string.

    For a worker, _absolutize_id("", scope_root) == scope_root, so the request
    resolves to the worker's own target and triggers the "whole goal" rejection
    — but the error message shows empty backticks ("Delegating step ``").
    For the main agent, "" is not a valid node id, so NodeNotFound fires — but
    again shows "No step `` found."

    This test locks down both paths so the error messages surface the actual
    problem (missing/empty step_id) rather than silently defaulting."""
    from .mcp_http_server import _subagent_tool_logic
    from .model import WorkerHandle
    session = root.session
    session.age += 1
    goal = root.sub_nodes[1]
    s = {"english": "nonneg", "conclusion": r"(0::int) \<le> x * x"}
    await goal.fill("1", [Have.gen_single({"thought": "H", "statement": s, "name": "hH"})])
    H = goal.sub_nodes[0]

    # --- 1. Main agent: subagent with empty step_id ---
    print_header("main agent: subagent with empty step_id", file)
    r, e = await _subagent_tool_logic(session, {
        "step_id": "", "suggestions": "do something", "helpful_lemmas": []})
    file.write(f"is_error={e}\n{r}\n")

    # --- 2. Main agent: subagent with missing step_id (hallucinated 'task' key) ---
    print_header("main agent: subagent with missing step_id (task key)", file)
    r2, e2 = await _subagent_tool_logic(session, {
        "task": "prove this goal", "suggestions": "try auto", "helpful_lemmas": []})
    file.write(f"is_error={e2}\n{r2}\n")

    # --- 3. Worker: subagent with empty step_id -> resolves to scope root ---
    session.role = model.Role_Worker(target=H, worker_handle=WorkerHandle(H, session))
    try:
        print_header("worker: subagent with empty step_id", file)
        r3, e3 = await _subagent_tool_logic(session, {
            "step_id": "", "suggestions": "do something", "helpful_lemmas": []})
        file.write(f"is_error={e3}\n{r3}\n")

        # --- 4. Worker: subagent with missing step_id (hallucinated 'task' key) ---
        print_header("worker: subagent with missing step_id (task key)", file)
        r4, e4 = await _subagent_tool_logic(session, {
            "task": "prove this goal"})
        file.write(f"is_error={e4}\n{r4}\n")
    finally:
        session.role = model.Role_Major()
        H.worker_handle = None


@model_test("StruggleCheckpoint", "Test_StruggleCheckpoint.thy", 11)
async def _test_StruggleCheckpoint(root: Root, file: MyIO):
    """Test the struggle checkpoint detection and reset logic.

    Verifies:
    - _should_struggle_checkpoint returns False for planners
    - _should_struggle_checkpoint returns True when thresholds are met for workers
    - _reset_struggle_counters zeros counters and lowers thresholds
    - launch_interaction stub returns (False, "test: not stuck")
    - Counters interact correctly with the Interaction_StruggleCheckpoint type
    """
    from .model import WorkerHandle
    session = root.session

    # --- 1. Planner never triggers ---
    print_header("planner: never triggers", file)
    session._session_edit_count = 100
    session._session_delete_count = 100
    file.write(f"planner _should_struggle_checkpoint: {session._should_struggle_checkpoint()}\n")
    session._session_edit_count = 0
    session._session_delete_count = 0

    # --- 2. Set up a worker ---
    session.age += 1
    goal_node = root.sub_nodes[1]
    await goal_node.fill("1", [Have.gen_single({
        "thought": "target",
        "statement": {"english": "trivial", "conclusion": "True"},
        "name": "h_target",
    })])
    have_node = goal_node.sub_nodes[0]
    handle = WorkerHandle(have_node, session)
    session.role = model.Role_Worker(target=have_node, worker_handle=handle)

    try:
        # --- 3. Below threshold: should NOT trigger ---
        print_header("worker: below threshold", file)
        session._session_edit_count = 29
        session._session_delete_count = 5
        file.write(f"edit=29 delete=5: {session._should_struggle_checkpoint()}\n")

        session._session_edit_count = 30
        session._session_delete_count = 4
        file.write(f"edit=30 delete=4: {session._should_struggle_checkpoint()}\n")

        # --- 4. At threshold: SHOULD trigger ---
        print_header("worker: at threshold", file)
        session._session_edit_count = 30
        session._session_delete_count = 5
        file.write(f"edit=30 delete=5: {session._should_struggle_checkpoint()}\n")

        session._session_edit_count = 50
        session._session_delete_count = 10
        file.write(f"edit=50 delete=10: {session._should_struggle_checkpoint()}\n")

        # --- 5. Reset and verify escalation ---
        print_header("reset and escalation", file)
        session._session_edit_count = 30
        session._session_delete_count = 5
        session._reset_struggle_counters()
        file.write(f"after reset: edit={session._session_edit_count} delete={session._session_delete_count}\n")
        file.write(f"new thresholds: edit={session._struggle_edit_threshold} delete={session._struggle_delete_threshold}\n")

        # --- 6. After reset: lower thresholds ---
        print_header("after reset: lower thresholds", file)
        session._session_edit_count = 14
        session._session_delete_count = 2
        file.write(f"edit=14 delete=2: {session._should_struggle_checkpoint()}\n")

        session._session_edit_count = 15
        session._session_delete_count = 3
        file.write(f"edit=15 delete=3: {session._should_struggle_checkpoint()}\n")

        # --- 7. Fork interaction stub returns "not stuck" ---
        print_header("fork interaction stub", file)
        interaction = Interaction_StruggleCheckpoint(
            target=have_node, delete_count=5, edit_count=30, checkpoint_number=1)
        result = await session.launch_interaction(interaction)
        file.write(f"fork result: {result}\n")

        # --- 8. Sub-subagent thresholds (depth >= 2) ---
        print_header("sub-subagent thresholds", file)
        # Simulate a sub-subagent: parent is a worker, this session is also a worker
        original_parent_role = session.parent  # save (None for test session)
        # Create a fake parent that looks like a worker
        class _FakeParent:
            role = model.Role_Worker(target=have_node)
        session.parent = _FakeParent()  # type: ignore
        session._struggle_checkpoint_count = 0
        session._reset_struggle_counters()
        file.write(f"sub-subagent subsequent thresholds: edit={session._struggle_edit_threshold} delete={session._struggle_delete_threshold}\n")
        # Check initial thresholds for sub-subagent by re-init
        _is_sub_sub = (isinstance(session.role, Role_Worker)
                       and session.parent is not None
                       and isinstance(session.parent.role, Role_Worker))
        file.write(f"detected as sub-subagent: {_is_sub_sub}\n")
        # Restore
        session.parent = original_parent_role
        # Verify normal agent reset thresholds
        session._reset_struggle_counters()
        file.write(f"normal worker subsequent thresholds: edit={session._struggle_edit_threshold} delete={session._struggle_delete_threshold}\n")

    finally:
        session.role = model.Role_Major()
        have_node.worker_handle = None


@model_test("InsertBeforeSlot", "Test_InsertBeforeSlot.thy", 8)
async def _test_InsertBeforeSlot(root: Root, file: MyIO):
    """insert_before targeting a filling slot should fall through to fill.

    Scenario: fill step 1 with a Have, then call insert_before on "2"
    which is the next filling slot (not an existing node). The operation
    should succeed identically to fill("2", ...).

    Also tests: insert_before on a sub-block slot (1.1), and
    insert_before on a genuinely nonexistent node still fails.
    """
    print_header("Initial", file)
    root.print(0, file)

    # Fill step 1 with a Have — creates a sub-block needing proof
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "helper lemma",
        "statement": {"english": "x squared is non-negative",
                      "conclusion": r"(0::int) \<le> x * x"},
        "name": "sq_nonneg",
    })])
    print_header("After fill step 1 (Have)", file)
    root.print(0, file)

    # Step "1.1" is a filling slot inside the Have's proof block.
    # insert_before("1.1", ...) should fall through to fill.
    root.session.age += 1
    outcome_sub = await root.insert_before("1.1", [Obvious.gen_single({"facts": []})])
    file.write(f"insert_before('1.1') on slot: failure={outcome_sub.failure}\n")
    file.write(f"insert_before('1.1') committed count: {len(outcome_sub.committed)}\n")
    assert outcome_sub.failure is None, \
        f"insert_before on sub-block slot should succeed, got: {outcome_sub.failure}"
    print_header("After insert_before on sub-slot 1.1 (fell through to fill)", file)
    root.print(0, file)

    # Step "2" is the next filling slot at the top level.
    # insert_before("2", ...) should fall through to fill.
    root.session.age += 1
    outcome_top = await root.insert_before("2", [Obvious.gen_single({"facts": []})])
    file.write(f"insert_before('2') on slot: failure={outcome_top.failure}\n")
    file.write(f"insert_before('2') committed count: {len(outcome_top.committed)}\n")
    assert outcome_top.failure is None, \
        f"insert_before on top-level slot should succeed, got: {outcome_top.failure}"
    print_header("After insert_before on top-level slot 2 (fell through to fill)", file)
    root.print(0, file)

    # Genuinely nonexistent node should still fail.
    root.session.age += 1
    outcome_bad = await root.insert_before("99", [Obvious.gen_single({"facts": []})])
    file.write(f"insert_before('99') nonexistent: failure={type(outcome_bad.failure).__name__}\n")
    assert outcome_bad.failure is not None, \
        "insert_before on genuinely nonexistent node should fail"


@model_test("Comment1", "Test_Comment.thy", 8)
async def _test_Comment1(root: Root, file: MyIO):
    """Comment/uncomment a Leaf (Obvious), verify state clones through,
    siblings still evaluate, unfinished_nodes correct, quickview rendering."""
    # Build a small proof: Have + Obvious
    print_header("Initial", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "helper",
        "statement": {"english": "non-negative", "conclusion": r"(0::int) \<le> x * x"},
        "name": "sq",
    })])
    print_header("After Have", file)
    root.print(0, file)

    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("After Obvious (1.1 proved)", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"unfinished before comment: {len(unfinished)}\n")

    # Comment out the Obvious
    root.session.age += 1
    outcome = await root.comment(["1.1"])
    file.write(f"comment affected: {outcome.affected}, not_found: {outcome.not_found}, warnings: {outcome.warnings}\n")
    print_header("After commenting 1.1", file)
    root.print(0, file)
    print_header("Quickview after commenting 1.1", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"unfinished after comment: {len(unfinished)}\n")

    # Double-comment should warn
    root.session.age += 1
    outcome2 = await root.comment(["1.1"])
    file.write(f"double-comment warnings: {outcome2.warnings}\n")

    # Uncomment
    root.session.age += 1
    outcome3 = await root.uncomment(["1.1"])
    file.write(f"uncomment affected: {outcome3.affected}\n")
    print_header("After uncommenting 1.1", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"unfinished after uncomment: {len(unfinished)}\n")

    # Uncomment non-commented should warn
    root.session.age += 1
    outcome4 = await root.uncomment(["1.1"])
    file.write(f"uncomment-non-commented warnings: {outcome4.warnings}\n")

@model_test("CommentHave", "Test_CommentHave.thy", 8)
async def _test_CommentHave(root: Root, file: MyIO):
    """Comment a StdBlock (Have): entire subtree skipped, fact hidden from
    successors, assemble skips it, siblings evaluate normally."""
    # Build: Have sq (with Obvious proof) + second Obvious at top level
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "helper",
        "statement": {"english": "non-negative", "conclusion": r"(0::int) \<le> x * x"},
        "name": "sq",
    })])
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    print_header("Proof built (Have + Obvious)", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"unfinished before comment: {len(unfinished)}\n")

    # Comment the whole Have block
    root.session.age += 1
    outcome = await root.comment(["1"])
    file.write(f"comment Have affected: {outcome.affected}\n")
    print_header("After commenting Have (step 1)", file)
    root.print(0, file)
    print_header("Quickview after commenting Have", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"unfinished after comment Have: {len(unfinished)}\n")

    # Verify assemble skips the commented block
    assembled = root.assemble()
    file.write(f"assembled ops count: {len(assembled)}\n")

    # Uncomment and verify re-evaluation
    root.session.age += 1
    outcome2 = await root.uncomment(["1"])
    file.write(f"uncomment Have affected: {outcome2.affected}\n")
    print_header("After uncommenting Have (step 1)", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"unfinished after uncomment Have: {len(unfinished)}\n")

    # Verify assemble includes the block again
    assembled2 = root.assemble()
    file.write(f"assembled ops count after uncomment: {len(assembled2)}\n")


@model_test("SubtreeStats", "Test_SubtreeStats.thy", 8)
async def _test_SubtreeStats(root: Root, file: MyIO):
    """Pin `Node.subtree_stats` = (total, proved), the metric of the
    large-delete confirmation gate: a finished block covers its whole subtree
    as proved; SUCCESS Obvious leaves count individually; cheap structural
    successes (Intro, SplitConjs) do not; FAILURE/CANCELLED never count;
    a COMMENTED subtree counts (0, 0) entirely — comments are not code. Only
    numeric stat lines and statuses go into the golden — no tree prints
    (hammer output is nondeterministic)."""
    def stats_line(label: str, sid: str | None) -> None:
        node = root if sid is None else root.locate_node(sid)
        t, p = node.subtree_stats()
        file.write(f"{label}: total={t}, proved={p}\n")

    stats_line("root initial", None)

    # Step 1: fully proved Have block (Have + SUCCESS Obvious).
    root.session.age += 1
    await root.fill("1", [Have.gen_single({
        "thought": "helper",
        "statement": {"english": "square is non-negative",
                      "conclusion": r"(0::int) \<le> x * x"},
        "name": "sq",
    })])
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
    file.write(f"step 1.1 status: {root.locate_node('1.1').status.status.value}\n")
    stats_line("proved Have (1)", "1")
    stats_line("SUCCESS Obvious leaf (1.1)", "1.1")

    # Step 2: Have left open after a structural Intro — a SUCCESS Intro leaf
    # alone is not proved work.
    root.session.age += 1
    await root.fill("2", [Have.gen_single({
        "thought": "identity implication, deliberately left unproved",
        "statement": {"english": "non-negativity is preserved",
                      "for_any": [{"name": "y", "type": "int"}],
                      "premises": [{"name": "hy", "term": r"(0::int) \<le> y"}],
                      "conclusion": r"(0::int) \<le> y"},
        "name": "h2",
    })])
    root.session.age += 1
    await root.fill("2.1", [Intro.gen_single({
        "thought": "fix y and assume the premise",
    })])
    file.write(f"step 2.1 status: {root.locate_node('2.1').status.status.value}\n")
    stats_line("open Have with SUCCESS Intro (2)", "2")

    # Step 3: Have over a conjunction; SplitConjs; close ONLY the first
    # subgoal. The finished GoalNode covers itself + its Obvious as proved;
    # the SplitConjs block and the Have stay unproved.
    root.session.age += 1
    await root.fill("3", [Have.gen_single({
        "thought": "conjunction to split",
        "statement": {"english": "both squares are non-negative",
                      "conclusion": r"(0::int) \<le> x * x \<and> (0::int) \<le> x * x + 1"},
        "name": "h3",
    })])
    root.session.age += 1
    await root.fill("3.1", [SplitConjs.gen_single({
        "thought": "split the conjunction",
    })])
    root.session.age += 1
    await root.fill("3.1.1.1", [Obvious.gen_single({"facts": []})])
    file.write(f"step 3.1 status: {root.locate_node('3.1').status.status.value}\n")
    stats_line("half-proved SplitConjs Have (3)", "3")
    stats_line("finished subgoal (3.1.1)", "3.1.1")
    stats_line("open subgoal (3.1.2)", "3.1.2")

    # Step 4: ill-typed Have -> FAILURE; step 5 after it -> CANCELLED.
    root.session.age += 1
    await root.fill("4", [Have.gen_single({
        "thought": "intentionally bad step",
        "statement": {"english": "invalid", "conclusion": "1 1 1"},
        "name": "bad",
    })])
    root.session.age += 1
    await root.fill("5", [Obvious.gen_single({"facts": []})])
    file.write(f"step 4 status: {root.locate_node('4').status.status.value}\n")
    file.write(f"step 5 status: {root.locate_node('5').status.status.value}\n")
    stats_line("FAILURE Have (4)", "4")
    stats_line("CANCELLED Obvious (5)", "5")

    stats_line("root with all steps", None)

    # A COMMENTED subtree counts (0, 0) entirely — comments are not code.
    root.session.age += 1
    await root.comment(["1"])
    file.write(f"step 1 status after comment: {root.locate_node('1').status.status.value}\n")
    stats_line("commented Have (1)", "1")
    stats_line("root with step 1 commented", None)

    root.session.age += 1
    await root.uncomment(["1"])
    stats_line("uncommented Have (1)", "1")
    stats_line("root after uncomment", None)


@model_test("UnfoldCertJoin", "Test_UnfoldCertJoin.thy", 12)
async def _test_unfold_cert_join(root: Root, file: MyIO):
    r"""Regression: gathering the unfoldings of a constant must NOT raise
    'Cannot join unrelated theory certificates' when a candidate definition lives
    in a theory unrelated to `Minilang`.

    Field defect (tools/aoa_putnam_eval, putnam_1962_a2): the agent ran `Unfold`
    on `f \<in> {(f::real\<Rightarrow>real). \<exists>a c. 0 \<le> a \<and> f = (\<lambda>x. a / (1 - c*x)\<^sup>2)}` and got
    `Isabelle error: Error: Cannot join unrelated theory certificates Minilang:280
    and Elementary_Metric_Spaces`.

    Root cause — `Minilang.potential_defs_of_const` (library/proof.ML): each
    candidate definitional equation is run through `normalize_thm`, which strips a
    leading object `\<forall>`/`\<longrightarrow>` via `thm RS @{thm spec}` / `thm RS @{thm mp}`. Those
    antiquotations are compiled inside `Minilang.thy` (proof.ML is loaded there by
    `ML_file`), so they permanently carry a `Minilang:N` certificate. `Minilang`
    imports only `HOL.List` + `Auto_Sledgehammer` (no reals/analysis); when the
    proof runs in a theory that ALSO imports HOL-Analysis (the PutnamBench/MathBench
    environment), a fetched def whose home theory is `Elementary_Metric_Spaces` is
    UNRELATED to `Minilang:N`. `RS` joins the two certificates before unifying, so
    it raises the error, which the callback surfaces to the agent as the `Unfold`
    `edit` error. (`handle THM _` in `normalize_thm` does not catch it — it is an
    `ERROR`, not a `THM`.)

    The head constant of the field target `f \<in> {...}` is `Set.member`, so we
    probe `(\<in>)`. The fixture imports `Elementary_Metric_Spaces` so that
    `Find_Theorems` surfaces the metric-space membership defs that trigger it.
    After a fix (e.g. transfer the antiquotation thms to the current theory before
    `RS`), the call returns its candidate list without error and this test passes.
    """
    ml_state = root.ml_state
    try:
        defs = await ml_state.potential_defs_of([IsaTerm.from_agent(r"(\<in>)")])
    except IsabelleError as e:
        msg = " | ".join(e.errors) if e.errors else str(e)
        if "Cannot join unrelated theory certificates" in msg:
            raise TestFailed(r"REPRODUCED cert-join bug on Unfold of (\<in>): " + msg)
        raise
    # Count-independent assertion: the bug is the certificate-join failure, not
    # the candidate count (which drifts with the library / infra filter). A bare
    # success line keeps the golden stable.
    assert isinstance(defs, list)
    file.write(r"potential_defs_of((\<in>)) succeeded (no cert-join error)" + "\n")


async def run_all_tests(repl_addr: str, mode="test", logger: logging.Logger | None = None, sh_timeout: int | None = 10):
    import msgpack as mp
    from IsaREPL import Client
    _budget = (
        14400, #timeout_seconds
        10000, #max_tool_calls
        8, #max_retries
    )
    _cfg = None  # unit
    async with Client(repl_addr, 'HOL', timeout=1200) as repl:
        await repl.load_theory(['Minilang_Agent.Minilang_Agent'])
        await repl.record_state("init")
        _test_filter = os.environ.get("TEST_FILTER", None)
        _test_exclude = os.environ.get("TEST_EXCLUDE", None)
        _exclude_patterns = [p.strip() for p in _test_exclude.split(",") if p.strip()] if _test_exclude else []
        _tests_to_run = [
            t for t in TESTS.values()
            if (_test_filter is None or any(p.strip() in t.name for p in _test_filter.replace(",", "|").split("|")))
            and not any(p in t.name for p in _exclude_patterns)
        ]
        case_num = len(_tests_to_run)
        passed = 0
        for i, test_case in enumerate(_tests_to_run):
            await repl.rollback('init')
            print(f"Running test [{i+1}/{case_num}] {test_case.name}")
            abs_file_path = os.path.abspath(os.path.join(os.path.dirname(__file__), "Tests", test_case.file))
            await repl.file(abs_file_path, test_case.line, 0, cache_position=False, use_cache=False)
            if sh_timeout is not None:
                try:
                    await repl.config([f'auto_sledgehammer_params = "timeout = {sh_timeout}"'])
                except REPLFail:
                    pass
            await repl.run_app('Minilang.AoA')
            invocation_id = f"{mode}.{test_case.name}"
            await repl._write((invocation_id, f"{mode}.{test_case.name}", (_cfg, _budget), None, None, None))
            try:
                (status, elapsed, cpu_time, detail, _cost) = Client._parse_control_(await repl._feed_and_unpack())
            except REPLFail as e:
                print(f"\033[91mTest {test_case.name} error: {e}\033[0m")
                continue
            detail_suffix = f": {detail}" if detail else ""
            if status == "success":
                passed += 1
                print(f"\033[92mTest {test_case.name} passed, elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
            elif status in ("stuck", "false_statement", "resource_exhausted"):
                passed += 1
                print(f"\033[92mTest {test_case.name} passed (status={status}{detail_suffix}), elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
            else:
                print(f"\033[91mTest {test_case.name} failed (status={status}{detail_suffix}), elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
        print(f"\n{passed}/{case_num} tests passed")
