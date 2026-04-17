import asyncio
import inspect
import os
import time
from IsaREPL import REPLFail
from typing import Any, Awaitable, Coroutine, NamedTuple, Sequence, TypedDict, Callable, TextIO, Union, cast
from . import model
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
    async def run(self, connection: Connection, log_dir: str, global_context: Context, ptree: ML_ProofTree) -> Root:
        raise NotImplementedError("Subclass must implement run method")

type _TestOpr = Callable[[Root, MyIO], Union[None, Awaitable[None]]]

class ModelTestCase(TestCase):
    def __init__(self, name : str, file: str, line: int, opr: _TestOpr):
        super().__init__(name, file, line)
        self.opr = opr
    async def run(self, connection: Connection, log_dir: str, global_context: Context, ptree: ML_ProofTree) -> Root:
        def show_colored_diff(actual: str, expected_path: str, test_name: str):
            """Write actual to a temp file and display colored diff against expected."""
            with tempfile.NamedTemporaryFile(mode='w', suffix='.actual.yaml', delete=False) as actual_file:
                actual_file.write(actual)
                actual_path = actual_file.name
            try:
                diff_result = subprocess.run(
                    ['diff', '--color=always', '-u', expected_path, actual_path],
                    capture_output=True,
                    text=True
                )
                print(f"\n=== Diff for test '{test_name}' ===", file=sys.stderr)
                print(diff_result.stdout, file=sys.stderr)
                if diff_result.stderr:
                    print(diff_result.stderr, file=sys.stderr)
            finally:
                os.unlink(actual_path)
        async with Session(connection.server.logger, log_dir) as session:
            root = Root((global_context, ptree), connection, session)
            await session.initialize(root)
            buffer = io.StringIO()
            result = self.opr(root, MyIO(buffer))
            if inspect.iscoroutine(result):
                await result
            correct_yaml_path = self.correct_yaml_path()
            if correct_yaml_path is not None:
                with open(correct_yaml_path, 'r') as f:
                    if buffer.getvalue() != f.read():
                        show_colored_diff(buffer.getvalue(), correct_yaml_path, self.name)
                        raise TestFailed(f"Test Faild on '{self.name}'")
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
    await goal.append(InferenceRule.gen({"thought": "Proof by contradiction", "rule": None}))
    print_header("Setting the inference rule", file)
    root.print(0, file)
    await goal.append(Obtain.gen({"thought": "I don't know", "variables": [{"name": "m", "type": "nat"}, {"name": "n", "type": "nat"}],
            "constraints": [{"isabelle": "¦sqrt 2¦ = m / n", "english": "some fancy explanation"}]}))
    print_header("Obtain m n", file)
    root.print(0, file)
    #node = root.locate_node("2.1") # not appear
    await root.fill("2.1", Obvious.gen({"facts": []}))
    print_header("Obvious", file)
    root.print(0, file)
    await root.fill("3", Have.gen({"thought": "I don't know", "statement": {"english": "some fancy explanation", "isabelle": "m^2 = (sqrt 2)^2 * n^2"}, "name": "helper_lemma"}))
    await root.fill("3.1", Obvious.gen({"facts": []}))
    print_header("Have", file)
    root.print(0, file)

@model_test("Branch1", "Test_Branch.thy", 8)
async def _test_branch(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", Branch.gen({
        "thought": "I don't know",
        "cases": [
            {"statement": {"english": "in case x is positive", "isabelle": "x > 0"}, "proof": "Given later"},
            {"statement": {"english": "in case x is negative", "isabelle": "x < 0"}, "proof": "Given later"},
            {"statement": {"english": "in case x is zero", "isabelle": "x = 0"}, "proof": "Given later"},
        ]
    }))
    print_header("Branch", file)
    root.print(0, file)

    # Close the exhaustiveness goal 1.0
    root.session.age += 1
    await root.fill("1.0.1", Obvious.gen({"facts": []}))
    print_header("After Obvious on 1.0.1 (exhaustiveness)", file)
    root.print(0, file)
    print_header("Overview after 1.0.1", file)
    root.quickview(0, file)

    # Close case 1.1 (x > 0)
    root.session.age += 1
    await root.fill("1.1.1", Obvious.gen({"facts": []}))
    print_header("After Obvious on 1.1.1 (x > 0)", file)
    root.print(0, file)
    print_header("Overview after 1.1.1", file)
    root.quickview(0, file)

    # Close case 1.2 (x < 0)
    root.session.age += 1
    await root.fill("1.2.1", Obvious.gen({"facts": []}))
    print_header("After Obvious on 1.2.1 (x < 0)", file)
    root.print(0, file)
    print_header("Overview after 1.2.1", file)
    root.quickview(0, file)

    # Close case 1.3 (x = 0)
    root.session.age += 1
    await root.fill("1.3.1", Obvious.gen({"facts": []}))
    print_header("After Obvious on 1.3.1 (x = 0)", file)
    root.print(0, file)
    print_header("Overview after 1.3.1", file)
    root.quickview(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("EquivDerive", "Test003.thy", 8)
async def _test_EquivDerive(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("2", InferenceRule.gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("IntroConj", "Test_IntroConj.thy", 6)
async def _test_IntroConj(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("2", InferenceRule.gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("IntroConj_short", "Test_IntroConj_short.thy", 6)
async def _test_IntroConj_short(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("2", InferenceRule.gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("InferenceRuleSolvesGoal", "Test_InferenceRule_SolvesGoal.thy", 8)
async def _test_InferenceRuleSolvesGoal(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Apply refl which fully solves "a = a" — produces 0 subgoals.
    # This exercises the empty-BUNDL code path in InferenceRule._print_header.
    await root.fill("1", InferenceRule.gen({
        "thought": "Apply reflexivity",
        "rule": {"refer_by": "name", "name": "refl"}
    }))
    print_header("After InferenceRule (goal fully solved)", file)
    root.print(0, file)
    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

@model_test("CaseSplit", "Test006.thy", 9)
async def _test_CaseSplit(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", CaseSplit.gen({
        "thought": "Case split",
        "target_isabelle_term": r"l"
    }))
    print_header("Case Split", file)
    root.print(0, file)
    await root.fill("1.Nil.1", CaseSplit.gen({
        "thought": "Case split",
        "target_isabelle_term": r"l"
    }))
    print_header("Case Split", file)
    root.print(0, file)

@model_test("CaseSplit_Bool", "Test_CaseSplit_Bool.thy", 8)
async def _test_CaseSplit_Bool(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", CaseSplit.gen({
        "thought": "Case split on boolean b",
        "target_isabelle_term": r"b"
    }))
    print_header("Case Split Bool", file)
    root.print(0, file)

@model_test("CaseSplit_Quickview", "Test_CaseSplit_Quickview.thy", 8)
async def _test_CaseSplit_Quickview(root: Root, file: MyIO):
    """Bug: quickview after CaseSplit doesn't print the binding variables
    and premises produced by the case-split. The full print shows them,
    but quickview omits them entirely.
    Uses a list CaseSplit so both case_vars (Cons introduces a, list)
    and case_hyps (e.g. Cons.prem0: l = a # list) are exercised."""
    await root.fill("1", CaseSplit.gen({
        "thought": "Case split on list l",
        "target_isabelle_term": r"l"
    }))
    print_header("Full print (shows variables and premises)", file)
    root.print(0, file)
    print_header("Quickview (should show variables and premises too)", file)
    root.quickview(0, file)

@model_test("GoalCtxQuickview", "Test_GoalCtxQuickview.thy", 8)
async def _test_GoalCtxQuickview(root: Root, file: MyIO):
    """Test that quickview prints goal.context.vars even when case_vars is None.
    After Intro+split_conj on '∀x::nat. P x ∧ Q x', the fixed variable x
    appears in each GoalNode's goal.context.vars but NOT in case_vars (since
    these GoalNodes come from IntroSplitConj, not CaseSplit).

    The leading ⋀x triggers the framework's auto-Intro at step 1 (fixes x,
    split_conj=False) which leaves a single residual goal `P x ∧ Q x` and
    does not open a sub-proof block. We apply the manual split_conj at the
    next step (2) on that residual."""
    root.session.age += 1
    await root.fill("2", Intro.gen({
        "thought": "Split conjunction",
        "split_conj": True
    }))
    print_header("Full print", file)
    root.print(0, file)
    print_header("Quickview (should show x in subgoal context)", file)
    root.quickview(0, file)

@model_test("Induction", "Test_Induction.thy", 8)
async def _test_Induction(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", Induction.gen({
        "thought": "some thought about Induction",
        "target_isabelle_term": r"l",
        "variables": [{"name": "l", "status": "fixed"}],
        "rule": None
    }))
    print_header("Induction", file)
    root.print(0, file)
    await root.fill("1.Nil.1", Obvious.gen({"facts": []}))
    print_header("Obvious", file)
    root.print(0, file)
    await root.fill("1.Cons.1", Obvious.gen({
        "facts": [{"refer_by": "name", "name": "Cons.IH"}]
    }))
    print_header("Obvious", file)
    root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Suffices", "Test_Suffices.thy", 9)
async def _test_Suffices(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use "it suffices to show" that x*x + 1 > 0
    await root.fill("1", Suffices.gen({
        "thought": "It suffices to show a stronger statement",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "isabelle": "x * x + 1 > 0"
        }
    }))
    print_header("After Suffices", file)
    root.print(0, file)
    # Now we need to prove: (x * x + 1 > 0) --> (x * x >= 0)
    await root.fill("1.1", Obvious.gen({"facts": []}))
    print_header("After proving implication", file)
    root.print(0, file)
    # Now we need to prove: x * x + 1 > 0
    await root.fill("2", Obvious.gen({"facts": []}))
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
    await root.fill("1", Rewrite.gen({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"refer_by": "name", "name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["h2"]
    }))
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
    await root.fill("1", Rewrite.gen({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"refer_by": "name", "name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["h2"]
    }))
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
    await root.fill("1", Have.gen({
        "thought": "I don't know",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "isabelle": "x = y"
        },
        "name": "lem1"
    }))
    await root.fill("1.1", Obvious.gen({"facts": []}))
    print_header("After Have", file)
    root.print(0, file)
    await root.fill("2", Rewrite.gen({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"refer_by": "name", "name": "lem1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After Rewrite", file)
    root.print(0, file)
    await root.amend("1", Have.gen({
        "thought": "I don't know!!!",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "isabelle": "x = y * 1"
        },
        "name": "lem1"
    }))
    print_header("After Amend Have", file)
    root.print(0, file)
    await root.amend("1", Have.gen({
        "thought": "I don't know!!!",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "isabelle": "x = y * 2"
        },
        "name": "lem1"
    }))
    print_header("After Amend Have", file)
    root.print(0, file)

@model_test("Rewrite_NoProgress", "Test_Rewrite_NoProgress.thy", 13)
async def _test_Rewrite_NoProgress(root: Root, file: MyIO):
    """Rewrite with an irrelevant rule should fail with 'no progress' after the
    CHANGED_PROP fix in proof.ML."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Rewrite h1 using foo_def — completely irrelevant, should make no progress
    new_node, success, reason = await root.fill("1", Rewrite.gen({
        "thought": "Attempt rewrite with irrelevant rule",
        "using": [{"refer_by": "name", "name": "foo_def"}],
        "use system simplifiers": False,
        "rewrite goal": False,
        "rewrite premises": ["h1"]
    }))
    print_header("Reasponse", file)
    file.write(f"Success: {success}\n")
    file.write(f"Reason: {reason}\n")
    print_header("After Rewrite", file)
    root.print(0, file)

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
#     node1, is_error1, reason1 = await root.fill("1", Rewrite.gen({
#         "thought": "Rewrite the goal using h",
#         "using": [{"refer_by": "name", "name": "h"}],
#         "use system simplifiers": False,
#         "rewrite goal": True,
#         "rewrite premises": []
#     }))
#     file.write(f"Rewrite step 1: status={node1.status.status.value}, is_error={is_error1}\n")
#     if reason1:
#         file.write(f"  reason: {reason1.reason}\n")
#     print_header("After successful Rewrite", file)
#     root.print(0, file)
# 
#     # Step 2: Obvious with no facts. Expected to fail on `P y` (nothing
#     # closes it). The bug surfaces here: instead of returning a graceful
#     # failure_reason, the framework raises InternalError from the
#     # predecessor re-refresh path.
#     root.session.age += 1
#     try:
#         node2, is_error2, reason2 = await root.fill("2", Obvious.gen({"facts": []}))
#         file.write(f"Obvious step 2: status={node2.status.status.value}, is_error={is_error2}\n")
#         if reason2:
#             file.write(f"  reason: {reason2.reason}\n")
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
    await root.fill("1", Witness.gen({
        "thought": "Provide 5 as witness for the existential",
        "witness": "5"
    }))
    print_header("After Witness", file)
    root.print(0, file)

    # Prove the remaining goal (5 = 5) using Obvious
    await root.fill("2", Obvious.gen({"facts": []}))
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
    await root.fill("1", Define.gen({
        "thought": "Introduce the doubling function as a witness",
        "name": "double",
        "type": r"nat \<Rightarrow> nat",
        "equations": ["double n = n + n"],
    }))
    print_header("After Define (auto-proved)", file)
    root.print(0, file)

    # Use `double` to instantiate the existential.
    await root.fill("2", Witness.gen({
        "thought": "Pick the freshly-defined `double` as the witness",
        "witness": "double",
    }))
    print_header("After Witness", file)
    root.print(0, file)

    # Close the remaining equation `double 2 = 4` via Obvious.
    await root.fill("3", Obvious.gen({"facts": []}))
    print_header("After Obvious", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

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
    await root.fill("1", Define.gen({
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
    }))
    print_header("After Define (deferred block opened)", file)
    root.print(0, file)

    # Discharge the first residual inside the deferred block:
    # `wf (measure (\<lambda>n. n))`, closed by `wf_measure`.
    await root.fill("1.1.1", Obvious.gen({"facts": []}))
    print_header("After Obvious on residual 1 (well-foundedness)", file)
    root.print(0, file)

    # Discharge the second residual inside the deferred block:
    # `\<And>n. (n, Suc (Suc n)) \<in> measure (\<lambda>n. n)`,
    # closed by `in_measure` + arithmetic.
    await root.fill("1.2.2", Obvious.gen({"facts": []}))
    print_header("After Obvious on residual 2 (decrease)", file)
    root.print(0, file)

    # Block auto-closes; proceed with the outer proof.
    await root.fill("2", Witness.gen({
        "thought": "Pick the freshly-defined `halve` as the witness",
        "witness": "halve",
    }))
    print_header("After Witness", file)
    root.print(0, file)

    # `halve 4 = Suc (halve 2) = Suc (Suc (halve 0)) = Suc (Suc 0)`.
    await root.fill("3", Obvious.gen({"facts": []}))
    print_header("After Obvious on halve 4 = 2", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Witness2", "Test_Witness2.thy", 8)
async def _test_Witness2(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)

    # Use Witness on a non-existential goal — should fail gracefully
    node, is_error, reason = await root.fill("1", Witness.gen({
        "thought": "Provide 1 as witness, which is positive",
        "witness": "1"
    }))
    if reason:
        file.write(f"Error: {reason}\n")
    else:
        file.write(f"The expected failure did not happen\n")
    print_header("After Witness (expected failure)", file)
    root.print(0, file)

@model_test("Unfold1", "Test_Unfold1.thy", 15)
async def _test_Unfold1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)

    # First Unfold: silently pick XXX_def (index 0) — no interaction printed.
    async def stub_silent(interaction):
        return await interaction.answer([0])
    root.session.fork_interaction = stub_silent
    await root.fill("1", Unfold.gen({
        "thought": "Unfold the goal",
        "targets": ["XXX"],
    }))
    print_header("After Unfold", file)
    root.print(0, file)

    # Amend: re-install stub that prints the prompt and picks XXX_alt (index 1).
    async def stub_fork(interaction):
        print_header("Interaction Prompt", file)
        await interaction.prompt(0, file)
        return await interaction.answer([1])
    root.session.fork_interaction = stub_fork
    await root.amend("1", Unfold.gen({
        "thought": "Unfold the goal",
        "targets": ["XXX"],
    }))
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
    await root.fill("1", Have.gen({
        "thought": "helper",
        "statement": {"english": "x equals y plus 0", "isabelle": "x = y"},
        "name": "lem1"
    }))
    root.session.age += 1
    await root.fill("1.1", Obvious.gen({"facts": []}))
    root.session.age += 1
    await root.fill("2", Rewrite.gen({
        "thought": "rewrite",
        "using": [{"refer_by": "name", "name": "lem1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After building 3 steps", file)
    root.print(0, file, update_line=False)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()
    # Delete the middle step (Have + its substep)
    root.session.age += 1
    await root.delete(["1"])
    print_header("After deleting step 1 (Have)", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()
    # Insert a Have before step 2
    root.session.age += 1
    await root.insert_before("2", Have.gen({
        "thought": "re-add helper",
        "statement": {"english": "x equals y plus 0", "isabelle": "x = y + 0"},
        "name": "lem1"
    }))
    print_header("After inserting Have before step 2", file)
    root.print(0, file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

# @model_test("Delete2", "Test_Delete2.thy", 13)
# async def _test_Delete2(root: Root, file: MyIO):
#     """Test deleting multiple steps at once."""
#     print_header("Initial YAML", file)
#     root.print(0, file)
#     root.session.age += 1
#     await root.fill("1", Have.gen({
#         "thought": "helper",
#         "statement": {"english": "x equals y", "isabelle": "x = y"},
#         "name": "lem1"
#     }))
#     root.session.age += 1
#     await root.fill("1.1", Obvious.gen({"facts": []}))
#     root.session.age += 1
#     await root.fill("2", Have.gen({
#         "thought": "helper2",
#         "statement": {"english": "y equals z", "isabelle": "y = z"},
#         "name": "lem2"
#     }))
#     root.session.age += 1
#     await root.fill("2.1", Obvious.gen({"facts": []}))
#     root.session.age += 1
#     await root.fill("3", Obvious.gen({"facts": []}))
#     print_header("After building 5 steps", file)
#     root.print(0, file)
#     buffer = io.StringIO()
#     root.print(0, MyIO(buffer), update_line=True)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset_changed()
#     # Delete two steps at once
#     root.session.age += 1
#     await root.delete(["1", "2"])
#     print_header("After deleting steps 1 and 2", file)
#     root.print(0, file)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset_changed()
# 
# @model_test("Delete3", "Test_Delete3.thy", 13)
# async def _test_Delete3(root: Root, file: MyIO):
#     """Test deleting with duplicate IDs (deduplication)."""
#     print_header("Initial YAML", file)
#     root.print(0, file)
#     root.session.age += 1
#     await root.fill("1", Have.gen({
#         "thought": "helper",
#         "statement": {"english": "x equals y", "isabelle": "x = y"},
#         "name": "lem1"
#     }))
#     root.session.age += 1
#     await root.fill("1.1", Obvious.gen({"facts": []}))
#     root.session.age += 1
#     await root.fill("2", Obvious.gen({"facts": []}))
#     print_header("After building steps", file)
#     root.print(0, file)
#     buffer = io.StringIO()
#     root.print(0, MyIO(buffer), update_line=True)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset_changed()
#     # Delete with duplicate ID — should deduplicate and not error
#     root.session.age += 1
#     await root.delete(["1", "1"])
#     print_header("After deleting step 1 (with duplicate)", file)
#     root.print(0, file)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset_changed()

@model_test("ReferFactByProposition", "Test001.thy", 6)
async def _test_ReferFactByProposition(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    fullname = await root.ml_state.fetch_facts([{"refer_by": "name", "name": "notI"}])
    file.write(f"Fullname of notI: {fullname}\n")
    return

@model_test("RetrieveFact", "Test_RetrieveFact1.thy", 6)
async def _test_RetrieveFact(root: Root, file: MyIO):
    """Test fetch_facts with FactByName, FactByProposition, and FactByDescription."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # 1. Test fetch_facts with all three fact types
    fetched = await root.ml_state.fetch_facts([
        {"refer_by": "name", "name": "log_nat_power"},           # → IsabelleFact_Presented
        {"refer_by": "name", "name": "nonexistent_lemma"},        # → IsabelleFact_Unfound
        {"refer_by": "proposition", "proposition": "(8::nat) = 2^3"},  # → IsabelleFact_ProveInTime
        {"refer_by": "description", "english": "8 = 2^3"},       # → Interaction_RetrieveForProof
    ])
    for i, f in enumerate(fetched):
        file.write(f"  fetch_facts[{i}]: {type(f).__name__}\n")
    assert isinstance(fetched[0], IsabelleFact_Presented)
    assert isinstance(fetched[1], IsabelleFact_Unfound)
    assert isinstance(fetched[2], IsabelleFact_ProveInTime)
    assert isinstance(fetched[3], Interaction_RetrieveForProof)
    # 2. Test Obvious with FactByProposition and FactByName (no interaction).
    root.session.age += 1
    gn = Obvious.gen({
        "facts": [
            {"refer_by": "proposition", "proposition": "(8::nat) = 2^3"},
            {"refer_by": "name", "name": "log_nat_power"},
        ]
    })
    node, _, _ = await root.fill("2", gn)
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
        {"refer_by": "name", "name": "log_nat_power"},           # → IsabelleFact_Presented
        {"refer_by": "description", "english": "8 = 2^3"},       # → Interaction_RetrieveForProof
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
        result = await interaction.answer("(8::nat) = 2^3")
        assert isinstance(result, list) and len(result) == 1
        pit = result[0]
        file.write(f"    ProveInTime answer: {type(pit).__name__}\n")
        assert isinstance(pit, IsabelleFact_ProveInTime)
        file.write(f"    statement: {pit.statement.unicode}\n")
        return result
    root.session.fork_interaction = stub_fork

    node, _, _ = await root.fill("2", InferenceRule.gen({
        "thought": "test description-based retrieval",
        "rule": {"refer_by": "description", "english": "8 = 2^3"},
    }))
    file.write(f"Filled node: {type(node).__name__}, id={node.id}\n")
    node.print(1, file, show_warnings=True)
    print_header("After fill", file)
    root.print(0, file)
    return

@model_test("Obvious_partial_solve", "Test_Obvious_partial_solve.thy", 11)
async def _test_Obvious_partial_solve(root: Root, file: MyIO):
    """Reproduces HAMMER partially solving a goal, leaving subgoals that cause
    an unexpected Intro node to be auto-appended."""
    # Step 1: Have h2: log 2 8 = 3
    root.session.age += 1
    await root.fill("1", Have.gen({
        "thought": "log_2(8) = 3",
        "name": "h2",
        "statement": {
            "english": "log base 2 of 8 equals 3",
            "isabelle": "log (2::real) (8::real) = (3::real)"
        }
    }))
    # Step 1.1: Obvious with log_pow_cancel
    root.session.age += 1
    await root.fill("1.1", Obvious.gen({"facts": [{"refer_by": "name", "name": "log_pow_cancel"}]}))
    # Step 2: Have h3: log 8 x = log 2 x / 3
    root.session.age += 1
    await root.fill("2", Have.gen({
        "thought": "change of base",
        "name": "h3",
        "statement": {
            "english": "log base 8 of x equals log base 2 of x divided by 3",
            "isabelle": "log (8::real) x = log (2::real) x / (3::real)"
        }
    }))
    # Step 2.1: Obvious with log_base_change and h2
    root.session.age += 1
    await root.fill("2.1", Obvious.gen({"facts": [
        {"refer_by": "name", "name": "log_base_change"},
        {"refer_by": "name", "name": "h2"}
    ]}))
    # Step 3: Have h4: log 8 (log 2 x) = log 2 (log 2 x) / 3
    root.session.age += 1
    await root.fill("3", Have.gen({
        "thought": "change of base again",
        "name": "h4",
        "statement": {
            "english": "log base 8 of (log base 2 of x) equals log base 2 of (log base 2 of x) divided by 3",
            "isabelle": "log (8::real) (log (2::real) x) = log (2::real) (log (2::real) x) / (3::real)"
        }
    }))
    print_header("Before step 3.1", file)
    root.print(0, file)
    # Step 3.1: Obvious with log_base_change + h2 → HAMMER partially solves,
    # leaving subgoals that trigger an unexpected Intro at step 3.2
    root.session.age += 1
    await root.fill("3.1", Obvious.gen({"facts": [
        {"refer_by": "name", "name": "log_base_change"},
        {"refer_by": "name", "name": "h2"}
    ]}))
    print_header("After step 3.1 (unexpected Intro at 3.2)", file)
    root.print(0, file)

@model_test("Hammer_ProveInTime", "Test_Hammer_ProveInTime.thy", 11)
async def _test_Hammer_ProveInTime(root: Root, file: MyIO):
    """Reproduces OutOfData error when HAMMER uses a ProveInTime fact."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Step 1: Have h_log8
    root.session.age += 1
    await root.fill("1", Have.gen({
        "thought": "log base 8 of x equals log base 2 of x divided by 3",
        "name": "h_log8",
        "statement": {
            "english": "log base 8 of x equals (log base 2 of x) / 3",
            "isabelle": "log (8::real) x = log (2::real) x / 3"
        }
    }))
    print_header("After Have h_log8", file)
    root.print(0, file)
    # Step 1.1: Obvious with a ProveInTime fact (by proposition), a library fact, and a local premise
    root.session.age += 1
    await root.fill("1.1", Obvious.gen({"facts": [
        {"refer_by": "proposition", "proposition": "(8::real) = (2::real) ^ (3::nat)"},
        {"refer_by": "name", "name": "log_base_pow"},
        {"refer_by": "name", "name": "h0"},
    ]}))
    print_header("After Obvious with ProveInTime", file)
    root.print(0, file)

@model_test("Simplify_stuck", "Test_Simplify_stuck.thy", 11)
async def _test_Simplify_stuck(root: Root, file: MyIO):
    """Reproduces stuck SIMPLIFY when rewriting with local + library facts inside a Have block."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", Have.gen({
        "thought": "Since 8 = 2^3, log base 8 of x equals log base 2 of x divided by 3",
        "name": "h2",
        "statement": {
            "english": "log base 8 of x equals log base 2 of x divided by 3",
            "isabelle": "log (8::real) x = log (2::real) x / 3"
        }
    }))
    print_header("After Have h2", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1.1", Have.gen({
        "thought": "First establish that 8 = 2^3 as reals",
        "name": "h8",
        "statement": {
            "english": "8 equals 2 to the power 3",
            "isabelle": "(8::real) = (2::real) ^ 3"
        }
    }))
    root.session.age += 1
    await root.fill("1.1.1", Obvious.gen({"facts": []}))
    print_header("After proving h8", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1.2", Rewrite.gen({
        "thought": "Rewrite 8 as 2^3 in the goal using h8, then apply log_base_pow",
        "using": [
            {"refer_by": "name", "name": "h8"},
            {"refer_by": "name", "name": "log_base_pow"}
        ],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After Rewrite", file)
    root.print(0, file)

@model_test("Simplify_no_intro_bindings", "Test_Simplify_no_intro_bindings.thy", 11)
async def _test_Simplify_no_intro_bindings(root: Root, file: MyIO):
    """Reproduces 'Expected exactly one Intro_Bindings_Msg, got 0' when Rewrite
    references a local fact (h8eq) that is out of scope."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # Step 1: Have h2
    root.session.age += 1
    await root.fill("1", Have.gen({
        "thought": "log base 8 of x equals log base 2 of x divided by 3",
        "name": "h2",
        "statement": {
            "english": "log base 8 of x equals log base 2 of x divided by 3",
            "isabelle": "log (8::real) x = log 2 x / 3"
        }
    }))
    # Step 1.1: Have h8eq (inside h2's proof)
    root.session.age += 1
    await root.fill("1.1", Have.gen({
        "thought": "First establish that 8 = 2^3 as reals",
        "name": "h8eq",
        "statement": {
            "english": "8 equals 2 to the power 3",
            "isabelle": "(8::real) = 2 ^ 3"
        }
    }))
    # Step 1.1.1: Obvious (proves h8eq)
    root.session.age += 1
    await root.fill("1.1.1", Obvious.gen({"facts": []}))
    # Step 1.2: Rewrite using h8eq + log_base_pow (triggers timeout fallback)
    root.session.age += 1
    await root.fill("1.2", Rewrite.gen({
        "thought": "Rewrite 8 as 2^3 using h8eq, then apply log_base_pow",
        "using": [
            {"refer_by": "name", "name": "h8eq"},
            {"refer_by": "name", "name": "log_base_pow"}
        ],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    # Step 1.3: Obvious (closes h2's remaining goal)
    root.session.age += 1
    await root.fill("1.3", Obvious.gen({"facts": []}))
    print_header("After completing h2", file)
    root.print(0, file)
    # Step 2: Have h3
    root.session.age += 1
    await root.fill("2", Have.gen({
        "thought": "Rewrite h1 using h2",
        "name": "h3",
        "statement": {
            "english": "log base 2 of (log base 2 of x divided by 3) equals log base 2 of (log base 2 of x) divided by 3",
            "isabelle": "log (2::real) (log 2 x / 3) = log 2 (log 2 x) / 3"
        }
    }))
    # Step 2.1: Have h2b (inside h3's proof)
    root.session.age += 1
    await root.fill("2.1", Have.gen({
        "thought": "log 8 (log 2 x) = log 2 (log 2 x) / 3 by the same log_base_pow argument",
        "name": "h2b",
        "statement": {
            "english": "log base 8 of (log base 2 of x) equals log base 2 of (log base 2 of x) divided by 3",
            "isabelle": "log (8::real) (log 2 x) = log 2 (log 2 x) / 3"
        }
    }))
    # Step 2.1.1: Rewrite using h8eq + log_base_pow with no system simplifiers
    # h8eq is OUT OF SCOPE here (it was local to step 1's proof)
    # This triggers: Expected exactly one Intro_Bindings_Msg, got 0
    root.session.age += 1
    await root.fill("2.1.1", Rewrite.gen({
        "thought": "Rewrite 8 as 2^3 using h8eq and apply log_base_pow",
        "using": [
            {"refer_by": "name", "name": "h8eq"},
            {"refer_by": "name", "name": "log_base_pow"}
        ],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After step 2.1.1", file)
    root.print(0, file)

@model_test("Have1", "Test_Have1.thy", 9)
async def _test_Have1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1", Have.gen({
        "thought": "helper",
        "statement": {"english": "x squared is non-negative", "isabelle": r"(0::int) \<le> x * x"},
        "name": "lem1"
    }))
    print_header("After Have", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1.1", Obvious.gen({"facts": []}))

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
    await root.fill("1", Have.gen({
        "thought": "Derive a simp rule for myf so the outer goal becomes trivial",
        "statement": {
            "english": "myf n equals n plus 7",
            "isabelle": r"myf n = n + 7"
        },
        "name": "myf_eq",
        "auto_apply": True,
    }))
    print_header("After Have (auto_apply=True)", file)
    root.print(0, file)

    # Discharge the Have's subgoal by unfolding the definition; `myf_def`
    # must be passed explicitly because it is not in the default simpset.
    root.session.age += 1
    await root.fill("1.1", Obvious.gen({
        "facts": [{"refer_by": "name", "name": "myf_def"}]
    }))
    print_header("After proving Have sub-goal", file)
    root.print(0, file)

    # Close the outer goal `myf 3 = 10` with Rewrite that uses ONLY the
    # system simplification set (no manually-supplied rules). This only
    # succeeds if `myf_eq` was auto-registered into the simpset by
    # `mini_auto_apply` — otherwise the system simpset has no way to unfold
    # `myf` and the goal cannot be reduced to `10 = 10`.
    root.session.age += 1
    ret = await root.fill("2", Rewrite.gen({
        "thought": "Close the outer goal using only the system simplifier",
        "using": [],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After closing outer goal", file)
    root.print(0, file)

    unfinished = set()
    root.unfinished_nodes(unfinished)
    file.write(f"Unfinished nodes: {len(unfinished)}\n")

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
    node, is_error, reason = await root.fill("1", Rewrite.gen({
        "thought": "Rewrite premise using definitions to derive contradiction",
        "using": [
            {"refer_by": "name", "name": "MyConst1_def"},
            {"refer_by": "name", "name": "MyConst2_def"}
        ],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["eq"]
    }))
    print_header("After Rewrite", file)
    root.print(0, file)
    file.write(f"is_error: {is_error}\n")
    file.write(f"reason: {reason}\n")

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
    node, success, reason = await root.fill("1", Rewrite.gen({
        "thought": "Rewrite h using is_nonzero_def to expose double negation",
        "using": [{"refer_by": "name", "name": "is_nonzero_def"}],
        "use system simplifiers": False,
        "rewrite goal": False,
        "rewrite premises": ["h"]
    }))
    print_header("After Rewrite", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason}\n")
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
        return await interaction.answer(list(range(num_matches)))
    root.session.fork_interaction = stub_fork
    node, success, reason = await root.fill("1", Rewrite.gen({
        "thought": "Rewrite using my_wrap to unfold f into g(f(...))",
        "using": [{"refer_by": "name", "name": "my_wrap"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After Rewrite (via interaction)", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason}\n")

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
        return await interaction.answer([1])
    root.session.fork_interaction = stub_fork
    node, success, reason = await root.fill("1", Rewrite.gen({
        "thought": "Rewrite f a using my_wrap, leave f b alone",
        "using": [{"refer_by": "name", "name": "my_wrap"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After Targeted Rewrite", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason}\n")

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
        # Answer with empty selection — drop the rule
        return await interaction.answer([])
    root.session.fork_interaction = stub_fork
    node, success, reason = await root.fill("1", Rewrite.gen({
        "thought": "Attempt rewrite with looping rule, then dismiss",
        "using": [{"refer_by": "name", "name": "my_wrap"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After Rewrite (rule dropped)", file)
    root.print(0, file)
    file.write(f"success: {success}\n")
    file.write(f"reason: {reason}\n")

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
    root.reset_changed()

    # 1. Fill step 1 with Have eq1
    root.session.age += 1
    await root.fill("1", Have.gen({
        "thought": "Since a(2) < a(1), a(3) < a(2), a(4) < a(3), we know a(1) > a(2) > a(3) > a(4). "
                   "Subtracting h7 from h6, the coefficients factor as (a(1)-a(2))*(-x1+x2+x3+x4)=0. "
                   "Since a(1)-a(2)>0, we get x1=x2+x3+x4.",
        "name": "eq1",
        "statement": {
            "english": "x(1) equals x(2) + x(3) + x(4)",
            "isabelle": "x (1::nat) = x (2::nat) + x (3::nat) + x (4::nat)"
        }
    }))
    print_header("After filling Have eq1", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

    # 2. Try Obvious to prove eq1 — fails (non-trivial)
    root.session.age += 1
    await root.fill("1.1", Obvious.gen({
        "facts": [
            {"refer_by": "name", "name": "h6"},
            {"refer_by": "name", "name": "h7"},
            {"refer_by": "name", "name": "assms(1)"},
            {"refer_by": "name", "name": "assms(2)"},
            {"refer_by": "name", "name": "assms(3)"}
        ]
    }))
    print_header("After failed Obvious on eq1", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

    # 3. Delete the failed Obvious step
    root.session.age += 1
    await root.delete(["1.1"])
    print_header("After deleting failed Obvious", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

    # 4. Fill with intermediate Have: a1_gt_a3
    root.session.age += 1
    await root.fill("1.1", Have.gen({
        "thought": "From assms(1) and assms(2), a(1) > a(3), so |a(1) - a(3)| = a(1) - a(3)",
        "name": "a1_gt_a3",
        "statement": {
            "english": "a(1) is greater than a(3)",
            "isabelle": "a (1::nat) > a (3::nat)"
        }
    }))
    # Prove a1_gt_a3 with Obvious — should succeed
    root.session.age += 1
    await root.fill("1.1.1", Obvious.gen({
        "facts": [
            {"refer_by": "name", "name": "assms(1)"},
            {"refer_by": "name", "name": "assms(2)"}
        ]
    }))
    print_header("After proving a1_gt_a3", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

    # 5. Fill with intermediate Have: a1_gt_a4
    root.session.age += 1
    await root.fill("1.2", Have.gen({
        "thought": "From assms, a(1) > a(2) > a(3) > a(4), so a(1) > a(4)",
        "name": "a1_gt_a4",
        "statement": {
            "english": "a(1) is greater than a(4)",
            "isabelle": "a (1::nat) > a (4::nat)"
        }
    }))
    # Prove a1_gt_a4 with Obvious — should succeed
    root.session.age += 1
    await root.fill("1.2.1", Obvious.gen({
        "facts": [
            {"refer_by": "name", "name": "a1_gt_a3"},
            {"refer_by": "name", "name": "assms(3)"}
        ]
    }))
    print_header("After proving a1_gt_a4", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

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

    # 7a. Mix of valid and invalid theories: valid theory still searched,
    # invalid one produces a warning.
    results_mix, warnings_mix = await ml.semantic_knn(
        "logarithm", 5, [EntityKind.THEOREM],
        theories_include=["HOL.Transcendental", "Nonexistent_Theory_XYZ"])
    file.write(f"Mixed valid/invalid theories: {len(results_mix)} results, {len(warnings_mix)} warnings\n")
    for w in warnings_mix:
        file.write(f"  Warning: {w}\n")
    assert len(results_mix) > 0, "Expected results from the valid theory"
    assert any("Nonexistent_Theory_XYZ" in w for w in warnings_mix), \
        "Expected warning mentioning the unknown theory"

    # 7b. All invalid theories: zero results plus warnings for each.
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
    """semantic_knn: unknown names in theories_include yield warnings,
    not aborts. Reproduces agent log 2026-04-17 where an invalid
    ``theories_include=['Discrete_Sqrt', 'Sqrt']`` killed the whole query.

    Covers four behaviors:
      1. Only unknown → zero results + warning (Option A semantics).
      2. Mixed valid + unknown → valid theory still searched + warning.
      3. Duplicate unknown names → warnings deduplicated.
      4. Unknown name on a non-theorem kind (CONSTANT) → still yields warning.
    """
    from Isabelle_RPC_Host.universal_key import EntityKind
    ml = root.ml_state

    # 1. Only an unknown theory: zero results + one warning, no abort.
    results1, warnings1 = await ml.semantic_knn(
        "list append", 5, [EntityKind.THEOREM],
        theories_include=["Nonexistent_XYZ"])
    file.write(f"Only unknown: {len(results1)} results, {len(warnings1)} warnings\n")
    for w in warnings1:
        file.write(f"  Warning: {w}\n")
    assert len(results1) == 0, "All-invalid theories_include must give zero results"
    assert len(warnings1) == 1
    assert "Nonexistent_XYZ" in warnings1[0]

    # 2. Mixed valid + unknown: still get results from the valid theory.
    results2, warnings2 = await ml.semantic_knn(
        "list append", 5, [EntityKind.THEOREM],
        theories_include=["HOL.List", "Nonexistent_XYZ"])
    file.write(f"Mixed valid/unknown: {len(results2)} results, {len(warnings2)} warnings\n")
    for w in warnings2:
        file.write(f"  Warning: {w}\n")
    assert len(results2) > 0, "Valid HOL.List should still yield results"
    assert any("Nonexistent_XYZ" in w for w in warnings2)
    assert not any("HOL.List" in w for w in warnings2), \
        "Valid theory must not produce a warning"

    # 3. Duplicated unknown name: warnings are deduplicated.
    results3, warnings3 = await ml.semantic_knn(
        "list append", 5, [EntityKind.THEOREM],
        theories_include=["Nonexistent_XYZ", "Nonexistent_XYZ"])
    file.write(f"Duplicate unknown: {len(results3)} results, {len(warnings3)} warnings\n")
    for w in warnings3:
        file.write(f"  Warning: {w}\n")
    assert len(warnings3) == 1, "Duplicate unknown names must dedup to one warning"

    # 4. Unknown theory applied to CONSTANT kind (exercises make_constants_callback
    #    path rather than make_theorems_callback).
    results4, warnings4 = await ml.semantic_knn(
        "append", 5, [EntityKind.CONSTANT],
        theories_include=["Nonexistent_XYZ"])
    file.write(f"Constant kind with unknown: {len(results4)} results, {len(warnings4)} warnings\n")
    for w in warnings4:
        file.write(f"  Warning: {w}\n")
    assert len(results4) == 0
    assert len(warnings4) == 1
    assert "Nonexistent_XYZ" in warnings4[0]


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


@model_test("IntroSplitConj", "Test_IntroSplitConj.thy", 10)
async def _test_intro_split_conj(root: Root, file: MyIO):
    """Test Intro with split_conj=True splits P ∧ Q ∧ R into separate subgoals."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # After auto-Intro (step 1) introduces premises P, Q, R,
    # the remaining goal is P ∧ Q ∧ R.
    # Apply Intro with split_conj=True to split the conjunction.
    root.session.age += 1
    await root.fill("1", Intro.gen({
        "thought": "Split conjunction into separate subgoals",
        "split_conj": True
    }))
    print_header("After Intro split_conj=True", file)
    root.print(0, file)
    print_header("Overview after split", file)
    root.quickview(0, file)

    # Close each subgoal with Obvious
    for i in range(1, 4):
        root.session.age += 1
        try:
            await root.fill(f"1.{i}.1", Obvious.gen({"facts": []}))
        except Exception as e:
            file.write(f"Cannot fill 1.{i}.1: {type(e).__name__}: {e}\n")
    print_header("After closing subgoals", file)
    root.print(0, file)
    print_header("Final overview", file)
    root.quickview(0, file)

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
    try:
        await root.fill("1.1.1", Obvious.gen({"facts": []}))
        print_header("After Obvious on 1.1.1 (subgoal existed)", file)
        root.print(0, file)
        print_header("Overview after 1.1.1", file)
        root.quickview(0, file)
    except Exception as e:
        file.write(f"No step 1.1.1 needed (auto-proved): {type(e).__name__}: {e}\n")

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
    await root.fill("1", Have.gen({
        "thought": "helper",
        "statement": {"english": "x equals y", "isabelle": "x = y"},
        "name": "lem1"
    }))
    await root.fill("1.1", Obvious.gen({"facts": []}))
    print_header("After step 1 (Have x=y, should succeed)", file)
    root.print(0, file)

    # Step 2: Have with INVALID Isabelle syntax (should FAIL)
    root.session.age += 1
    await root.fill("2", Have.gen({
        "thought": "intentionally bad step",
        "statement": {"english": "invalid", "isabelle": "1 1 1"},
        "name": "bad"
    }))
    step2 = root.locate_node("2")
    file.write(f"Step 2 status: {step2.status.status.value}\n")
    print_header("After step 2 (invalid Have, should fail)", file)
    root.print(0, file)

    # Step 3 (fill): Should be CANCELLED because step 2 failed
    root.session.age += 1
    await root.fill("3", Obvious.gen({"facts": []}))
    step3 = root.locate_node("3")
    file.write(f"Step 3 status (fill after failed): {step3.status.status.value}\n")
    assert step3.status.status == EvaluationStatus.Status.CANCELLED, \
        f"fill: Expected CANCELLED but got {step3.status.status.value}"
    print_header("After step 3 (fill, should be cancelled)", file)
    root.print(0, file)

    # Insert before step 3: predecessor is step 2 (FAILURE), should be CANCELLED
    root.session.age += 1
    inserted, _, _ = await root.insert_before("3", Have.gen({
        "thought": "inserted step",
        "statement": {"english": "x equals z", "isabelle": "x = z"},
        "name": "lem2"
    }))
    file.write(f"Inserted step status (insert_before after failed): {inserted.status.status.value}\n")
    assert inserted.status.status == EvaluationStatus.Status.CANCELLED, \
        f"insert_before: Expected CANCELLED but got {inserted.status.status.value}"
    print_header("After insert_before (should be cancelled)", file)
    root.print(0, file)

    # Amend step 2 to fix it (valid statement)
    root.session.age += 1
    await root.amend("2", Have.gen({
        "thought": "fixed step",
        "statement": {"english": "y equals x", "isabelle": "y = x"},
        "name": "lem_fixed"
    }))
    step2_fixed = root.locate_node("2")
    file.write(f"Step 2 status after amend (should succeed): {step2_fixed.status.status.value}\n")
    # After fixing step 2, subsequent steps should be refreshed (no longer CANCELLED)
    step2A = root.locate_node("2A")
    step3_after = root.locate_node("3")
    file.write(f"Inserted step status after amend: {step2A.status.status.value}\n")
    file.write(f"Step 3 status after amend: {step3_after.status.status.value}\n")
    print_header("After amend (fix step 2, should refresh all after)", file)
    root.print(0, file)


@model_test("ProveInTime_ParseError", "Test_ProveInTime_ParseError.thy", 6)
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
    bad_pit = IsabelleFact_ProveInTime(IsaTerm.from_agent(stmt_ascii))
    file.write(f"_filter_unprovable([ProveInTime(\"{stmt_ascii}\")]): ")
    try:
        kept, warnings = await _filter_unprovable([bad_pit], ml_state)
        file.write(f"kept={len(kept)}, warnings={warnings}\n")
    except IsabelleError as e:
        file.write(f"UNCAUGHT IsabelleError: {e}\n")
    except Exception as e:
        file.write(f"UNCAUGHT {type(e).__name__}: {e}\n")

    # --- Test 4: _filter_unprovable with Unicode ¦ variant ---
    bad_pit_unicode = IsabelleFact_ProveInTime(IsaTerm.from_agent(stmt_unicode))
    file.write(f"_filter_unprovable([ProveInTime(unicode ¦ variant)]): ")
    try:
        kept, warnings = await _filter_unprovable([bad_pit_unicode], ml_state)
        file.write(f"kept={len(kept)}, warnings={warnings}\n")
    except IsabelleError as e:
        file.write(f"UNCAUGHT IsabelleError: {e}\n")
    except Exception as e:
        file.write(f"UNCAUGHT {type(e).__name__}: {e}\n")

    # --- Test 5: Obvious.gen() with bad ProveInTime (HAMMER path) ---
    root.session.age += 1
    try:
        await root.fill("1", Obvious.gen({"facts": [
            {"refer_by": "proposition", "proposition": stmt_ascii}
        ]}))
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
                  Obvious.gen({"facts": []}))
        file.write("Subsequent fill succeeded (tree not stuck)\n")
    except Exception as e:
        file.write(f"Subsequent fill: {type(e).__name__}: {e}\n")

    print_header("Final State", file)
    root.print(0, file)


@model_test("ObviousProofFail", "Test_ObviousProofFail.thy", 8)
async def _test_ObviousProofFail(root: Root, file: MyIO):
    """Test that Have with proof='Obvious' where HAMMER fails doesn't crash quickview."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Have with an easy statement — Obvious should succeed
    root.session.age += 1
    await root.fill("1", Have.gen({
        "thought": "trivial identity",
        "statement": {"english": "x equals x", "isabelle": "x = x"},
        "name": "lem1",
        "proof": "Obvious"
    }))
    print_header("After Have x=x (Obvious succeeds)", file)
    root.print(0, file)

    # Have with a hard/false statement — Obvious (HAMMER) should fail
    root.session.age += 1
    await root.fill("2", Have.gen({
        "thought": "this is false",
        "statement": {"english": "x equals x plus one", "isabelle": "x = x + 1"},
        "name": "bad",
        "proof": "Obvious"
    }))
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
    await root.fill("1", Have.gen({
        "thought": "x times x is non-negative because x times x equals x squared",
        "statement": {
            "english": "x times x equals x squared",
            "isabelle": "x * x = x^2"
        },
        "name": "sq",
        "proof": "Obvious"
    }))
    print_header("After Have with proof=Obvious", file)
    root.print(0, file)

    # The remaining goal should still need a proof
    root.session.age += 1
    await root.fill("2", Obvious.gen({"facts": []}))
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
    await root.fill("1", Suffices.gen({
        "thought": "It suffices to show a stronger statement",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "isabelle": "x * x + 1 > 0"
        },
        "proof": "Obvious"
    }))
    print_header("After Suffices with proof=Obvious", file)
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
    await root.fill("1", Induction.gen({
        "thought": "Induction on list l",
        "target_isabelle_term": "l",
        "variables": [],
        "proof": "Obvious"
    }))
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
        try:
            await root.fill(f"{goal_name}.1", Obvious.gen({"facts": []}))
            print_header(f"Overview ({goal_name} filled manually)", file)
            root.quickview(0, file)
        except Exception as e:
            file.write(f"No step {goal_name}.1 needed (auto-proved): {type(e).__name__}: {e}\n")

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
    await root.fill("1", Obvious.gen({"facts": []}))
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
    await root.fill("1", Have.gen({
        "thought": "x squared is non-negative",
        "statement": {
            "english": "x times x equals x squared",
            "isabelle": "x * x = x^2"
        },
        "name": "sq",
        "proof": {"operation": "Obvious", "facts": [], "timeout": 15}
    }))
    print_header("After Have with proof=Obvious(timeout=15)", file)
    root.print(0, file)

    # Close the remaining goal
    root.session.age += 1
    await root.fill("2", Obvious.gen({"facts": [], "timeout": 30}))
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
    await root.fill("1", Derive.gen({
        "thought": "Instantiate h2 with x=0 and discharge with h1",
        "rule": {"refer_by": "name", "name": "h2"},
        "instantiations": [{"name": "x", "value": "0"}],
        "discharging_facts": [{"refer_by": "name", "name": "h1"}],
        "result_name": "derived_Q0"
    }))
    print_header("After Derive", file)
    root.print(0, file)
    # Close goal using the derived fact — may already be auto-proved
    root.session.age += 1
    try:
        await root.fill("2", Obvious.gen({
            "facts": [{"refer_by": "name", "name": "derived_Q0"}]
        }))
        print_header("After Obvious", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"No step 2 needed (auto-proved after Derive): {type(e).__name__}: {e}\n")
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
    await root.fill("1", Derive.gen({
        "thought": "Discharge h2 with h1 via modus ponens",
        "rule": {"refer_by": "name", "name": "h2"},
        "discharging_facts": [{"refer_by": "name", "name": "h1"}],
        "result_name": "mp_result"
    }))
    print_header("After Derive", file)
    root.print(0, file)
    # Close goal using the named result
    root.session.age += 1
    await root.fill("2", Obvious.gen({
        "facts": [{"refer_by": "name", "name": "mp_result"}]
    }))
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
    node, is_error, reason = await root.fill("1", Derive.gen({
        "thought": "Try to use a nonexistent rule",
        "rule": {"refer_by": "name", "name": "nonexistent_rule"},
        "result_name": "should_fail"
    }))
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
    node, is_error, reason = await root.fill("1", Derive.gen({
        "thought": "Derive h2 with x = 1 - 1, discharge with h1 (P 0) — should fail: no unifiers",
        "rule": {"refer_by": "name", "name": "h2"},
        "instantiations": [{"name": "x", "value": "1 - (1::nat)"}],
        "discharging_facts": [{"refer_by": "name", "name": "h1"}],
        "result_name": "bad_result"
    }))
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
    node, is_error, reason = await root.fill("1", Derive.gen({
        "thought": "Apply mult_mod_cancel_left — h1 lacks ?n*?a pattern, OF will fail",
        "rule": {"refer_by": "name", "name": "mult_mod_cancel_left"},
        "discharging_facts": [
            {"refer_by": "name", "name": "h1"},
            {"refer_by": "name", "name": "h2"}
        ],
        "result_name": "should_fail"
    }))
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
    node, is_error, reason = await root.fill("1", Derive.gen({
        "thought": "Apply mult_mod_cancel_left on nat — type mismatch, OF will fail",
        "rule": {"refer_by": "name", "name": "mult_mod_cancel_left"},
        "discharging_facts": [
            {"refer_by": "name", "name": "h1"},
            {"refer_by": "name", "name": "h2"}
        ],
        "result_name": "should_fail"
    }))
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
    node, is_error, reason = await root.fill("1", Derive.gen({
        "thought": "mult_mod_cancel_left on nat — type mismatch expected",
        "rule": {"refer_by": "name", "name": "mult_mod_cancel_left"},
        "discharging_facts": [
            {"refer_by": "name", "name": "h1"},
            {"refer_by": "name", "name": "h2"}
        ],
        "result_name": "should_fail_type"
    }))
    print_header("Sub-test 1: Type clash", file)
    file.write(f"Is error: {is_error}\n")
    file.write(f"Reason: {reason}\n")
    assert is_error, "Expected type clash error"
    assert reason is not None and "does not unify with" in reason.reason, \
        f"Expected 'does not unify with' in reason, got: {reason}"

    print_header("Final state", file)
    root.print(0, file)

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
    print_header("Initial Overview", file)
    root.quickview(0, file)
    file.write(f"GlobalEnv children: {len(root.global_env.sub_nodes)}\n")

    # === ADD: Append a global equation Have and prove it ===
    root.session.age += 1
    have1 = await root.global_env.append(Have.gen({
        "thought": "Restate h1 as a global rewrite rule",
        "statement": {"english": "P", "isabelle": "P"},
        "name": "t1",
        "proof": "Given later"
    }))
    file.write(f"Added have1: id={have1.id}, local_step={have1.local_step}, status={have1.status.status.value}\n")
    # Discharge the subgoal using the original assumption h1
    root.session.age += 1
    obv1 = await have1.append(Obvious.gen({
        "facts": [{"refer_by": "name", "name": "h1"}]
    }))
    file.write(f"Obvious in have1: status={obv1.status.status.value}\n")
    print_header("After ADD global Have (t1) + prove", file)
    root.print(0, file)
    print_header("Overview after ADD", file)
    root.quickview(0, file)

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
    node1, is_error1, reason1 = await root.fill("1", Rewrite.gen({
        "thought": "Rewrite the goal using the (broken) global equation t1",
        "using": [{"refer_by": "name", "name": "t1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    file.write(f"Rewrite step 1 using broken t1: status={node1.status.status.value}, is_error={is_error1}\n")
    if reason1:
        file.write(f"  reason: {reason1.reason}\n")
    print_header("After failed Rewrite at step 1 (broken t1)", file)
    root.print(0, file)

    # === AMEND (recovery): replace the bare `P` with a provable equation
    # `x = 0` that the inherited Obvious sub-step (which already references
    # h1: x = 0) can actually discharge. Verifies:
    #   (a) AMEND structurally swaps in the new Have on a GlobalEnv child,
    #   (b) _amend_from carries the existing Obvious sub-step across,
    #   (c) re-refresh after amend turns the previously-failing Have into
    #       a SUCCESS — a real recovery, not a no-op rename.
    root.session.age += 1
    amended, is_error2, reason2 = await root.amend("global.1", Have.gen({
        "thought": "Amended: replace unprovable y=x with the equation x=0 (= h1)",
        "statement": {"english": "x equals zero", "isabelle": "x = 0"},
        "name": "t1",
        "proof": "Given later"
    }))
    file.write(f"Amend global.1: id={amended.id}, local_step={amended.local_step}, is_error={is_error2}\n")
    if reason2:
        file.write(f"  reason: {reason2.reason}\n")
    file.write(f"Amended Have status: {amended.status.status.value}\n")
    file.write(f"Amended Have inherited children: {len(amended.sub_nodes)}\n")
    if amended.sub_nodes:
        first_child = amended.sub_nodes[0]
        file.write(f"  inherited child[0]: type={type(first_child).__name__}, status={first_child.status.status.value}\n")
    print_header("After AMEND global.1 (recovery)", file)
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
    have1 = await root.global_env.append(Have.gen({
        "thought": "Restate h1 as a global rewrite rule",
        "statement": {"english": "y equals x", "isabelle": "y = x"},
        "name": "g_eq",
        "proof": "Given later"
    }))
    file.write(f"Added have1: id={have1.id}, local_step={have1.local_step}, status={have1.status.status.value}\n")
    # Discharge the subgoal using h1 (trivially true since h1 IS y = x)
    root.session.age += 1
    obv1 = await have1.append(Obvious.gen({
        "facts": [{"refer_by": "name", "name": "h1"}]
    }))
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
    node1, is_error1, reason1 = await root.fill("1", Rewrite.gen({
        "thought": "Rewrite the goal using the global equation g_eq",
        "using": [{"refer_by": "name", "name": "g_eq"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    file.write(f"Rewrite step 1 using g_eq: status={node1.status.status.value}, is_error={is_error1}\n")
    if reason1:
        file.write(f"  reason: {reason1.reason}\n")
    print_header("After Rewrite proof body using global decl", file)
    root.print(0, file)

    # Close the now-trivial residual `x + x = x + x` via an explicit Rewrite
    # with system simplifiers. No `using` facts needed — simp alone closes
    # reflexive equalities.
    root.session.age += 1
    node2, is_error2, reason2 = await root.fill("2", Rewrite.gen({
        "thought": "Close residual reflexive equation via system simplifiers",
        "using": [],
        "use system simplifiers": True,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    file.write(f"Rewrite step 2 (system simp): status={node2.status.status.value}, is_error={is_error2}\n")
    if reason2:
        file.write(f"  reason: {reason2.reason}\n")
    print_header("After Rewrite closes residual goal", file)
    root.print(0, file)

    # === AMEND: Replace the global Have with a reoriented equation ===
    root.session.age += 1
    amended, is_error3, reason3 = await root.amend("global.1", Have.gen({
        "thought": "Amended: reverse orientation of the equation",
        "statement": {"english": "x equals y", "isabelle": "x = y"},
        "name": "g_eq",
        "proof": "Given later"
    }))
    file.write(f"Amend global.1: id={amended.id}, local_step={amended.local_step}, is_error={is_error3}\n")
    if reason3:
        file.write(f"  reason: {reason3.reason}\n")
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
    ret, is_error, reason = await root.fill("global.1", Have.gen({
        "thought": "global declaration via fill",
        "statement": {"english": "x is zero", "isabelle": "x = 0"},
        "name": "g1",
        "proof": "Given later"
    }))
    file.write(f"fill('global.1'): id={ret.id}, status={ret.status.status.value}, is_error={is_error}\n")
    print_header("After fill global.1", file)
    root.print(0, file)

    # Prove the global Have
    root.session.age += 1
    obv = await ret.append(Obvious.gen({
        "facts": [{"refer_by": "name", "name": "h1"}]
    }))
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
    await root.fill("1", Chaining.gen({
        "thought": "Chain ab and bc by transitivity to derive a <= c",
        "name": "ac",
        "facts": [
            {"refer_by": "name", "name": "ab"},
            {"refer_by": "name", "name": "bc"},
        ],
    }))
    print_header("After Chaining (named)", file)
    root.print(0, file)

    # Close the main goal using the chained fact.
    await root.fill("2", Obvious.gen({
        "facts": [{"refer_by": "name", "name": "ac"}],
    }))
    print_header("After Obvious using ac", file)
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
    ret1, is_error1, _ = await root.fill("1", Have.gen({
        "thought": "intentionally bad",
        "statement": {"english": "bad", "isabelle": "1 1 1"},
        "name": "bad"
    }))
    assert is_error1, "bad Have should report as error"
    step1 = root.locate_node("1")
    assert step1.status.status == EvaluationStatus.Status.FAILURE, \
        f"Expected FAILURE but got {step1.status.status.value}"
    file.write(f"Step 1 status: {step1.status.status.value}\n")
    print_header("After step 1 (bad Have, should fail)", file)
    root.print(0, file)

    # Step 2: Fill an Obvious AFTER the failed Have.
    # It should be CANCELLED because step 1 failed.
    root.session.age += 1
    await root.fill("2", Obvious.gen({"facts": []}))
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
    ret3, is_error3, _ = await root.fill("1", Have.gen({
        "thought": "valid helper",
        "statement": {"english": "x is positive", "isabelle": "x > 0"},
        "name": "x_pos"
    }))
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
    await root.fill("1.1", Obvious.gen({"facts": []}))
    root.session.age += 1
    await root.fill("2", Obvious.gen({"facts": []}))
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
            short_name, exprs, roles, abbrev_names = r
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
            short_name, exprs, roles, abbrev_names = r
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
            short_name, exprs, roles, abbrev_names = r
            file.write(f"  {short_name.unicode}: abbrevs={abbrev_names}\n")
        else:
            file.write("  None\n")

    # 4. abbreviation_defs: look up the definition of `even`
    file.write("=== abbreviation_defs ===\n")
    abbrev_names_to_query: list[str] = []
    # Collect abbreviation names from the theorem retrieval above
    thm_result = await ml._retrieve_entity([(EntityKind.THEOREM, "even_Suc")])
    if thm_result[0] is not None:
        _, _, _, abbrev_names_to_query = thm_result[0]
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
            short_name, exprs, roles, abbrev_names = r
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
            short_name, exprs, roles, abbrev_names = r
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
    await root.fill("1", Have.gen({
        "thought": "intermediate step",
        "statement": {"english": "x is greater than 1", "isabelle": "x > 1"},
        "name": "x_gt_1"
    }))
    # Prove the Have subgoal.
    root.session.age += 1
    await root.fill("1.1", Obvious.gen({"facts": []}))

    # Step 2: First fill with plain Obvious (no fact reference).
    root.session.age += 1
    await root.fill("2", Obvious.gen({"facts": []}))
    print_header("After initial fill (proof complete)", file)
    root.print(0, file)

    # Now AMEND step 2 with a FactByName reference to "x_gt_1".
    # _amend_child passes position = index of step 2 (< len(sub_nodes)),
    # so _find_alive_state_among_children skips the _state_before_ending_
    # shortcut and returns step1.ml_state — the pre-Have state.
    root.session.age += 1
    step2_new, is_error, _ = await root.amend("2", Obvious.gen({
        "facts": [{"refer_by": "name", "name": "x_gt_1"}]
    }))

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
    # await root.fill("1", Intro.gen({
    #     "thought": "Introduce n",
    # }))
    # print_header("After outer Intro (introduce n)", file)
    # root.print(0, file)

    # Step 2: Have with a meta-quantified + implicational statement.
    # The Have auto-inserts an Intro child (with auto-detected bindings)
    # because the proof obligation is ∀-quantified at the meta level.
    await root.fill("2", Have.gen({
        "thought": "Auxiliary: product of positives is positive",
        "statement": {
            "english": "product of positives is positive",
            "isabelle": r"\<And>(a::int) b. a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> a * b > 0"
        },
        "name": "pos_mult"
    }))
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
        await root.amend("2.1", Intro.gen({
            "thought": "Introduce a, b and the premises",
            "variable_bindings": ["a", "b"],
            "fact_bindings": ["a_pos", "b_pos"]
        }))
        print_header("After Intro amend (no error — bug not reproduced)", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"BUG REPRODUCED: {type(e).__name__}: {e}\n")

    print_header("Final state", file)
    root.print(0, file)


@model_test("InductionGeneralize", "Test_InductionGeneralize.thy", 8)
async def _test_InductionGeneralize(root: Root, file: MyIO):
    """Reproduce issue from log D91DC33B9_1A88D48: Induction with a generalized
    variable drops premises that mention that variable.

    The goal ∀N m. m ≤ N ⟶ m * m ≤ N * N gets auto-Intro'd (step 1) to fix
    N, m and assume m ≤ N.  Then Induction on N with m generalized (step 2)
    should preserve the premise m ≤ N in the induction cases.

    Expected (correct) behavior:
      - Base case: premise m ≤ 0 should appear
      - Suc case IH: should be ∀m. m ≤ N ⟶ m * m ≤ N * N (bounded)

    Actual (buggy) behavior:
      - Base case: no premise m ≤ 0 — goal is m * m ≤ 0 for all m (unprovable)
      - Suc case IH: unconditional ∀m. m * m ≤ N * N (no bound)"""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 2 (step 1 is auto-Intro): Induction on N with m generalized.
    # BUG: the premise "m ≤ N" from the auto-Intro should be preserved in
    # induction cases, but it gets dropped when m is generalized.
    await root.fill("2", Induction.gen({
        "thought": "Induction on N with m generalized",
        "target_isabelle_term": "N",
        "variables": [
            {"name": "N", "status": "fixed"},
            {"name": "m", "status": "generalized"},
        ],
        "rule": None,
    }))
    print_header("After Induction (check premises in cases)", file)
    root.print(0, file)


@model_test("UpstreamChangeResetsObvious", "Test_UpstreamChangeResetsObvious.thy", 11)
async def _test_UpstreamChangeResetsObvious(root: Root, file: MyIO):
    """After Obvious fails, _is_trivial=False blocks retries.  Amending or
    inserting before the parent step should call _on_upstream_change, resetting
    _is_trivial so Obvious can be attempted again."""
    print_header("Initial YAML", file)
    root.print(0, file)

    # Step 1: Have True (trivially provable, Obvious succeeds)
    root.session.age += 1
    await root.fill("1", Have.gen({
        "thought": "trivial helper",
        "statement": {"english": "True", "isabelle": "True"},
        "name": "triv",
    }))
    root.session.age += 1
    await root.fill("1.1", Obvious.gen({"facts": []}))
    print_header("After step 1 (Have True, Obvious succeeds)", file)
    root.print(0, file)

    # Step 2: Have False (given later — impossible to prove)
    root.session.age += 1
    await root.fill("2", Have.gen({
        "thought": "impossible statement",
        "statement": {"english": "False", "isabelle": "False"},
        "name": "bad",
    }))
    print_header("After step 2 (Have False, open proof)", file)
    root.print(0, file)

    # Step 2.1: Obvious — must fail (can't prove False)
    root.session.age += 1
    await root.fill("2.1", Obvious.gen({"facts": []}))
    step2 = root.locate_node("2")
    assert step2._is_trivial is False, \
        f"Expected _is_trivial=False after Obvious failure, got {step2._is_trivial}"
    print_header("After step 2.1 (Obvious fails on False)", file)
    root.print(0, file)

    # Retry Obvious on step 2.1 — should be BLOCKED by GoalIsNontrivial
    root.session.age += 1
    try:
        await root.fill("2.1", Obvious.gen({"facts": []}))
        raise TestFailed("Expected CannotFill_GoalIsNontrivial but fill succeeded")
    except CannotFill_GoalIsNontrivial:
        pass  # expected
    file.write("Obvious retry correctly blocked by GoalIsNontrivial\n")

    # --- Test amend: amend step 1 → _on_upstream_change should reset step2._is_trivial ---
    root.session.age += 1
    await root.amend("1", Have.gen({
        "thought": "amended helper",
        "statement": {"english": "x + y = 3", "isabelle": "x + y = 3"},
        "name": "sum",
    }))
    step2 = root.locate_node("2")
    assert step2._is_trivial is None, \
        f"Expected _is_trivial=None after amend of predecessor, got {step2._is_trivial}"
    file.write("After amend: step2._is_trivial correctly reset to None\n")
    print_header("After amending step 1", file)
    root.print(0, file)

    # Obvious on step 2.1 should now be ALLOWED (not blocked), though it will still fail
    root.session.age += 1
    await root.fill("2.1", Obvious.gen({"facts": []}))
    file.write("Obvious retry allowed after amend (fails on False, as expected)\n")
    assert step2._is_trivial is False, \
        f"Expected _is_trivial=False after Obvious fails again, got {step2._is_trivial}"
    print_header("After Obvious retry (allowed, fails)", file)
    root.print(0, file)

    # --- Test insert_before: insert before step 2 → _on_upstream_change resets again ---
    root.session.age += 1
    await root.insert_before("2", Have.gen({
        "thought": "inserted step",
        "statement": {"english": "True", "isabelle": "True"},
        "name": "ins",
    }))
    step2 = root.locate_node("2")
    assert step2._is_trivial is None, \
        f"Expected _is_trivial=None after insert_before, got {step2._is_trivial}"
    file.write("After insert_before: step2._is_trivial correctly reset to None\n")
    print_header("After inserting before step 2", file)
    root.print(0, file)

    # Obvious on step 2.1 should be ALLOWED again
    root.session.age += 1
    await root.fill("2.1", Obvious.gen({"facts": []}))
    file.write("Obvious retry allowed after insert_before\n")
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

    # --- RetrieveForProof: text that IS a valid theorem name ---
    # "log_nat_power" is a theorem in Complex_Main
    inter1 = Interaction_RetrieveForProof(
        state=ml_state, query="logarithm of a power", kinds=[EntityKind.THEOREM])
    result1 = await inter1.answer("log_nat_power")
    file.write(f"RetrieveForProof('log_nat_power'): {type(result1[0]).__name__}\n")
    assert isinstance(result1[0], IsabelleFact_Presented), \
        f"Expected IsabelleFact_Presented, got {type(result1[0]).__name__}"
    file.write(f"  short_name: {result1[0].short_name.unicode}\n")

    # --- RetrieveForProof: text that is NOT a valid theorem name ---
    inter2 = Interaction_RetrieveForProof(
        state=ml_state, query="something trivial", kinds=[EntityKind.THEOREM])
    result2 = await inter2.answer("(8::nat) = 2 ^ 3")
    file.write(f"RetrieveForProof('(8::nat) = 2 ^ 3'): {type(result2[0]).__name__}\n")
    assert isinstance(result2[0], IsabelleFact_ProveInTime), \
        f"Expected IsabelleFact_ProveInTime, got {type(result2[0]).__name__}"

    # --- ChooseDef: text matching a candidate short name ---
    cand_a = IsabelleFact_Presented(
        full_name="Test_NamedFactResolution.NF_XXX_def",
        short_name=IsaTerm.from_isabelle("NF_XXX_def"),
        fact=FactByName(refer_by="name", name="NF_XXX_def"),
        expression=[IsaTerm.from_isabelle("NF_XXX ?a ?b = ?a + ?b")])
    cand_b = IsabelleFact_Presented(
        full_name="Test_NamedFactResolution.NF_XXX_alt",
        short_name=IsaTerm.from_isabelle("NF_XXX_alt"),
        fact=FactByName(refer_by="name", name="NF_XXX_alt"),
        expression=[IsaTerm.from_isabelle("NF_XXX ?a ?b = ?b + ?a")])
    inter3 = Interaction_ChooseDef(["NF_XXX"], [cand_a, cand_b], state=ml_state)
    result3 = await inter3.answer("NF_XXX_def")
    file.write(f"ChooseDef('NF_XXX_def'): {[type(r).__name__ for r in result3]}\n")
    assert len(result3) == 1 and result3[0] is cand_a, \
        "Expected cand_a to be selected by short name"

    # --- ChooseDef: text matching a candidate full name ---
    inter4 = Interaction_ChooseDef(["NF_XXX"], [cand_a, cand_b], state=ml_state)
    result4 = await inter4.answer("Test_NamedFactResolution.NF_XXX_alt")
    file.write(f"ChooseDef(full_name NF_XXX_alt): {[type(r).__name__ for r in result4]}\n")
    assert len(result4) == 1 and result4[0] is cand_b, \
        "Expected cand_b to be selected by full name"

    # --- ChooseDef: text not matching any candidate, but IS an accessible fact ---
    inter5 = Interaction_ChooseDef(["NF_XXX"], [cand_a, cand_b], state=ml_state)
    result5 = await inter5.answer("conjI")
    file.write(f"ChooseDef('conjI'): {[type(r).__name__ for r in result5]}\n")
    assert len(result5) == 1 and isinstance(result5[0], IsabelleFact_Presented), \
        f"Expected IsabelleFact_Presented via RPC lookup, got {type(result5[0]).__name__}"
    file.write(f"  resolved short_name: {result5[0].short_name.unicode}\n")

    # --- ChooseDef: text not matching anything ---
    inter6 = Interaction_ChooseDef(["NF_XXX"], [cand_a, cand_b], state=ml_state)
    try:
        await inter6.answer("xyzzy_nonexistent_thm")
        raise TestFailed("Expected Interaction_BadAnswer for nonexistent name")
    except Interaction_BadAnswer as e:
        file.write(f"ChooseDef('xyzzy_nonexistent_thm'): Interaction_BadAnswer as expected\n")

    print_header("Done", file)


@model_test("UnfoldSyntax", "Test_UnfoldSyntax.thy", 33)
async def _test_unfold_syntax(root: Root, file: MyIO):
    """Test the unfold_syntax callback.

    Verifies:
    1. A standard HOL term returns identical normal and raw displays
    2. A term using a higher-theory abbreviation (my_conj) is unfolded in raw display
    3. The head constant name is correctly extracted
    4. A non-constant head (lambda) returns empty head_name
    5. An unparseable term raises InternalError_UnparsedTerm
    """
    ml = root.ml_state

    # 1. Standard HOL term — no higher-theory syntax to strip
    file.write("=== standard HOL term ===\n")
    head, raw, normal = await ml.unfold_syntax("True ∧ False")
    file.write(f"  head: {head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")
    assert head == "HOL.conj", f"Expected HOL.conj, got {head}"

    # 2. Term using the custom abbreviation `my_conj` defined in the theory
    file.write("=== custom abbreviation ===\n")
    head, raw, normal = await ml.unfold_syntax("my_conj True False")
    file.write(f"  head: {head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 3. Term with `even` (abbreviation from Parity, above Main)
    file.write("=== even abbreviation ===\n")
    head, raw, normal = await ml.unfold_syntax("even (n::nat)")
    file.write(f"  head: {head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 4. Lambda head — head_name should be empty
    file.write("=== lambda head ===\n")
    head, raw, normal = await ml.unfold_syntax("λx::nat. x + 1")
    file.write(f"  head: '{head}'\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")
    assert head == "", f"Expected empty head for lambda, got '{head}'"

    # 5. Unparseable term — should raise InternalError_UnparsedTerm
    file.write("=== unparseable term ===\n")
    try:
        await ml.unfold_syntax("%%% bad syntax")
        raise TestFailed("Expected InternalError_UnparsedTerm")
    except InternalError_UnparsedTerm:
        file.write("  raised InternalError_UnparsedTerm as expected\n")

    # 6. Mixfix notation — the real syntax unfolding test
    file.write("=== mixfix: a ⊕ b ===\n")
    head, raw, normal = await ml.unfold_syntax("(a::nat) ⊕ b")
    file.write(f"  head: {head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    file.write("=== mixfix: (a ⊕ b) ⊕ c ===\n")
    head, raw, normal = await ml.unfold_syntax("((a::nat) ⊕ b) ⊕ c")
    file.write(f"  head: {head}\n")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 7. Custom bind notation
    file.write("=== bind: m ⤜ f ===\n")
    head, raw, normal = await ml.unfold_syntax("(Some (1::nat)) ⤜ (λx. if x > 0 then Some (x ⊕ x) else None)")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 8. Custom quantifier with syntax translation
    file.write("=== custom forall ===\n")
    head, raw, normal = await ml.unfold_syntax("∀⇩m x ∈ {1,2,3::nat}. x ⊕ x > 0")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 9. Custom sum with syntax translation
    file.write("=== custom sum ===\n")
    head, raw, normal = await ml.unfold_syntax("Σ⇩m x ∈ {1,2,3::nat}. x ⊕ x")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 10. Nested: custom quantifier + custom operator + custom sum
    file.write("=== nested custom syntax ===\n")
    head, raw, normal = await ml.unfold_syntax("∀⇩m x ∈ {1,2,3::nat}. (Σ⇩m y ∈ {0..<x}. y ⊕ x) > 0")
    file.write(f"  normal: {normal}\n")
    file.write(f"  raw: {raw}\n")

    # 11. Full query output via _handle_exact_term_query
    from .retrieval import _handle_exact_term_query
    file.write("=== query output: nested ===\n")
    result = await _handle_exact_term_query(root.session, "∀⇩m x ∈ {1,2,3::nat}. (Σ⇩m y ∈ {0..<x}. y ⊕ x) > 0")
    file.write(result + "\n")

    print_header("Done", file)


async def run_all_tests(repl_addr: str, mode="test", logger: logging.Logger | None = None):
    import msgpack as mp
    from IsaREPL import Client
    _budget = (
        -1, #step_limit
        600, #timeout
        1, #parallel_runs
        40, # query_ret_num
    )
    _cfg = (
        True, #drafting
        True, #gussing_num_typ
    )
    async with Client(repl_addr, 'HOL', timeout=1200) as repl:
        await repl.load_theory(['Minilang_Agent.Minilang_Agent'])
        await repl.record_state("init")
        _test_filter = os.environ.get("TEST_FILTER", None)
        _test_exclude = os.environ.get("TEST_EXCLUDE", None)
        _exclude_patterns = [p.strip() for p in _test_exclude.split(",") if p.strip()] if _test_exclude else []
        _tests_to_run = [
            t for t in TESTS.values()
            if (_test_filter is None or _test_filter in t.name)
            and not any(p in t.name for p in _exclude_patterns)
        ]
        case_num = len(_tests_to_run)
        passed = 0
        for i, test_case in enumerate(_tests_to_run):
            await repl.rollback('init')
            print(f"Running test [{i+1}/{case_num}] {test_case.name}")
            abs_file_path = os.path.abspath(os.path.join(os.path.dirname(__file__), "Tests", test_case.file))
            await repl.file(abs_file_path, test_case.line, 0, cache_position=False, use_cache=False)
            await repl.run_app('Minilang.AoA')
            invocation_id = f"{mode}.{test_case.name}"
            await repl._write((invocation_id, f"{mode}.{test_case.name}", (_cfg, _budget), None))
            try:
                (status, elapsed, cpu_time) = Client._parse_control_(await repl._feed_and_unpack())
            except REPLFail as e:
                print(f"\033[91mTest {test_case.name} error: {e}\033[0m")
                continue
            if status == "success" or status == "agent_gives_up":
                passed += 1
                print(f"\033[92mTest {test_case.name} passed (status={status}), elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
            else:
                print(f"\033[91mTest {test_case.name} failed (status={status}), elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
        print(f"\n{passed}/{case_num} tests passed")
