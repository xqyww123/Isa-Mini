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
# The `line` argument must be the line number of `by AgentAoA` in the .thy file.
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
    await goal.append(InferenceRule.interactive_gen({"thought": "Proof by contradiction", "rule": None}))
    print_header("Setting the inference rule", file)
    root.print(0, file)
    await goal.append(Obtain.gen({"thought": "I don't know", "variables": [{"name": "m", "type": "nat"}, {"name": "n", "type": "nat"}],
            "constraints": [{"isabelle": "¦sqrt 2¦ = m / n", "english": "some fancy explanation"}]}))
    print_header("Obtain m n", file)
    root.print(0, file)
    #node = root.locate_node("2.1") # not appear
    await root.fill("2.1", Obvious.interactive_gen({"facts": []}))
    print_header("Obvious", file)
    root.print(0, file)
    await root.fill("3", Have.gen({"thought": "I don't know", "statement": {"english": "some fancy explanation", "isabelle": "m^2 = (sqrt 2)^2 * n^2"}, "name": "helper_lemma"}))
    await root.fill("3.1", Obvious.interactive_gen({"facts": []}))
    print_header("Have", file)
    root.print(0, file)

@model_test("Branch1", "Test_Branch.thy", 8)
async def _test_branch(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("1", Branch.gen({
        "thought": "I don't know",
        "cases": [
            {"english": "in case x is positive", "isabelle": "x > 0"},
            {"english": "in case x is negative", "isabelle": "x < 0"},
            {"english": "in case x is zero", "isabelle": "x = 0"},
        ]
    }))
    print_header("Branch", file)
    root.print(0, file)

    # Close the exhaustiveness goal 1.0
    root.session.age += 1
    await root.fill("1.0.1", Obvious.interactive_gen({"facts": []}))
    print_header("After Obvious on 1.0.1 (exhaustiveness)", file)
    root.print(0, file)
    print_header("Overview after 1.0.1", file)
    root.quickview(0, file)

    # Close case 1.1 (x > 0)
    root.session.age += 1
    await root.fill("1.1.1", Obvious.interactive_gen({"facts": []}))
    print_header("After Obvious on 1.1.1 (x > 0)", file)
    root.print(0, file)
    print_header("Overview after 1.1.1", file)
    root.quickview(0, file)

    # Close case 1.2 (x < 0)
    root.session.age += 1
    await root.fill("1.2.1", Obvious.interactive_gen({"facts": []}))
    print_header("After Obvious on 1.2.1 (x < 0)", file)
    root.print(0, file)
    print_header("Overview after 1.2.1", file)
    root.quickview(0, file)

    # Close case 1.3 (x = 0)
    root.session.age += 1
    await root.fill("1.3.1", Obvious.interactive_gen({"facts": []}))
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
    await root.fill("2", InferenceRule.interactive_gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("IntroConj", "Test_IntroConj.thy", 6)
async def _test_IntroConj(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("2", InferenceRule.interactive_gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("IntroConj_short", "Test_IntroConj_short.thy", 6)
async def _test_IntroConj_short(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    await root.fill("2", InferenceRule.interactive_gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

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
    await root.fill("1.Nil.1", Obvious.interactive_gen({"facts": []}))
    print_header("Obvious", file)
    root.print(0, file)
    await root.fill("1.Cons.1", Obvious.interactive_gen({
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
    await root.fill("1.1", Obvious.interactive_gen({"facts": []}))
    print_header("After proving implication", file)
    root.print(0, file)
    # Now we need to prove: x * x + 1 > 0
    await root.fill("2", Obvious.interactive_gen({"facts": []}))
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
    await root.fill("1", Rewrite.interactive_gen({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"refer_by": "name", "name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["h2"]
    }))
    print_header("After Rewrite", file)
    root.print(0, file)
    await root.rename_fact("premise0", "my_premise")
    await root.rename_var("aAa", "yyy")
    print_header("After Rename Fact", file)
    root.print(0, file)

@model_test("Rewrite2", "Test_Rewrite2.thy", 12)
async def _test_Rewrite2(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    await root.insert_before("1", Rewrite.interactive_gen({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"refer_by": "name", "name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["h2"]
    }))
    print_header("After Rewrite", file)
    root.print(0, file)
    await root.rename_fact("premise0", "my_premise")
    await root.rename_var("aAa", "yyy")
    print_header("After Rename Fact", file)
    root.print(0, file)
    await root.delete(["0A"])
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
    await root.fill("1.1", Obvious.interactive_gen({"facts": []}))
    print_header("After Have", file)
    root.print(0, file)
    await root.fill("2", Rewrite.interactive_gen({
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
    await root.fill("2", Obvious.interactive_gen({"facts": []}))
    print_header("After Obvious", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Witness2", "Test_Witness2.thy", 8)
async def _test_Witness2(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)

    try:
    # Use Witness to provide a witness (1) for the existential with property
        await root.fill("1", Witness.gen({
            "thought": "Provide 1 as witness, which is positive",
            "witness": "1"
        }))
    except CannotAppend as e:
        file.write(f"Error: {e}\n")
        return
    file.write(f"The excepted eception not happen")
    return

@model_test("Unfold1", "Test_Unfold1.thy", 15)
async def _test_Unfold1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)

    # Use Witness to provide a witness for the existential goal
    await root.fill("1", Unfold.gen(Unfold_ToolArg_internal(
        thought="Unfold the goal",
        targets=["XXX"],
        fact_refs=[IsabelleFact_Presented("XXX_def", "XXX_def", {"refer_by": "name", "name": "XXX_def"}, ["Fake"])]
    )))
    print_header("After Unfold", file)
    root.print(0, file)
    try:
        await root.amend("1", Unfold.interactive_gen({
            "thought": "Unfold the goal",
            "targets": ["XXX"],
        }))
    except RaiseInteraction as e:
        print_header("Interaction Prompt", file)
        assert len(e.interactions) == 1
        e.interactions[0].prompt(0, file)
        gn = await e.kontinuation([await inter.answer([1]) for inter in e.interactions])
        await root.amend("1", _trivial_parsing(gn))
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
    await root.fill("1.1", Obvious.interactive_gen({"facts": []}))
    root.session.age += 1
    await root.fill("2", Rewrite.interactive_gen({
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
#     await root.fill("1.1", Obvious.interactive_gen({"facts": []}))
#     root.session.age += 1
#     await root.fill("2", Have.gen({
#         "thought": "helper2",
#         "statement": {"english": "y equals z", "isabelle": "y = z"},
#         "name": "lem2"
#     }))
#     root.session.age += 1
#     await root.fill("2.1", Obvious.interactive_gen({"facts": []}))
#     root.session.age += 1
#     await root.fill("3", Obvious.interactive_gen({"facts": []}))
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
#     await root.fill("1.1", Obvious.interactive_gen({"facts": []}))
#     root.session.age += 1
#     await root.fill("2", Obvious.interactive_gen({"facts": []}))
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

@model_test("ReferFactByStatement", "Test001.thy", 6)
async def _test_ReferFactByStatement(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    fullname = await root.ml_state.fetch_facts([{"refer_by": "name", "name": "notI"}])
    file.write(f"Fullname of notI: {fullname}\n")
    # FactByStatement search is not yet implemented; just test FactByName for now
    return

@model_test("RetrieveFact", "Test_RetrieveFact1.thy", 6)
async def _test_RetrieveFact(root: Root, file: MyIO):
    """Test retrieve_facts and FactByStatement interaction.
    Reproduces 'Unknown ancestor theory ""' bug."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # 1. Test fetch_facts with various fact types
    fetched = await root.ml_state.fetch_facts([
        {"refer_by": "name", "name": "log_nat_power"},       # known fact → IsabelleFact_Presented
        {"refer_by": "name", "name": "nonexistent_lemma"},    # unknown fact → IsabelleFact_Unfound
        {"refer_by": "statement", "statement": "8 = 2^3"},   # statement → Interaction_RetrieveForProof
    ])
    for i, f in enumerate(fetched):
        file.write(f"  fetch_facts[{i}]: {type(f).__name__}\n")
    assert isinstance(fetched[0], IsabelleFact_Presented)
    assert isinstance(fetched[1], IsabelleFact_Unfound)
    assert isinstance(fetched[2], Interaction_RetrieveForProof)
    # 2. Test Obvious with both a FactByStatement and a FactByName.
    #    The FactByStatement triggers Interaction_RetrieveForProof which calls
    #    semantic_knn → entities_of → retrieve_facts internally.
    root.session.age += 1
    try:
        await root.fill("2", Obvious.interactive_gen({
            "facts": [
                {"refer_by": "statement", "statement": "8 = 2^3"},
                {"refer_by": "name", "name": "log_nat_power"},
            ]
        }))
    except RaiseInteraction as e:
        file.write(f"RaiseInteraction raised with {len(e.interactions)} interaction(s)\n")
        results: list[Any] = [None] * len(e.interactions)
        for i, inter in enumerate(e.interactions):
            file.write(f"  interaction[{i}]: {type(inter).__name__}\n")
            if isinstance(inter, Interaction_RetrieveForProof):
                file.write(f"    query: {inter.query}\n")
                file.write(f"    candidates: {len(inter.candidate_facts)}\n")
                # Answer with a ProveInTime statement
                result = await inter.answer("(8::nat) = 2^3")
                assert isinstance(result, list) and len(result) == 1
                pit = result[0]
                file.write(f"    ProveInTime answer: {type(pit).__name__}\n")
                assert isinstance(pit, IsabelleFact_ProveInTime)
                file.write(f"    statement: {pit.statement}\n")
                file.write(f"    pack: {pit.pack()}\n")
                results[i] = result
        # Invoke the continuation to get a gen_node, then fill
        gn = await e.kontinuation(results)
        root.session.age += 1
        node = await root.fill("2", _trivial_parsing(gn))
        file.write(f"Filled node: {type(node).__name__}, id={node.id}\n")
        node.print(1, file, show_warnings=True)
    print_header("After fill", file)
    root.print(0, file)
    return

@model_test("RetrieveFact2", "Test_RetrieveFact2.thy", 6)
async def _test_RetrieveFact2(root: Root, file: MyIO):
    """Test retrieve_facts and FactByStatement interaction.
    Reproduces 'Unknown ancestor theory ""' bug."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # 1. Test fetch_facts with various fact types
    fetched = await root.ml_state.fetch_facts([
        {"refer_by": "name", "name": "log_nat_power"},       # known fact → IsabelleFact_Presented
        {"refer_by": "name", "name": "nonexistent_lemma"},    # unknown fact → IsabelleFact_Unfound
        {"refer_by": "statement", "statement": "8 = 2^3"},   # statement → Interaction_RetrieveForProof
    ])
    for i, f in enumerate(fetched):
        file.write(f"  fetch_facts[{i}]: {type(f).__name__}\n")
    assert isinstance(fetched[0], IsabelleFact_Presented)
    assert isinstance(fetched[1], IsabelleFact_Unfound)
    assert isinstance(fetched[2], Interaction_RetrieveForProof)
    # 2. Test Obvious with both a FactByStatement and a FactByName.
    #    The FactByStatement triggers Interaction_RetrieveForProof which calls
    #    semantic_knn → entities_of → retrieve_facts internally.
    root.session.age += 1
    try:
        await root.fill("2", Obvious.interactive_gen({
            "facts": [
                {"refer_by": "statement", "statement": "8 = 2^3"},
                {"refer_by": "name", "name": "log_nat_power"},
            ]
        }))
    except RaiseInteraction as e:
        file.write(f"RaiseInteraction raised with {len(e.interactions)} interaction(s)\n")
        results: list[Any] = [None] * len(e.interactions)
        for i, inter in enumerate(e.interactions):
            file.write(f"  interaction[{i}]: {type(inter).__name__}\n")
            if isinstance(inter, Interaction_RetrieveForProof):
                file.write(f"    query: {inter.query}\n")
                file.write(f"    candidates: {len(inter.candidate_facts)}\n")
                # Answer with a ProveInTime statement
                result = await inter.answer("(9::nat) = 2^3")
                assert isinstance(result, list) and len(result) == 1
                pit = result[0]
                file.write(f"    ProveInTime answer: {type(pit).__name__}\n")
                assert isinstance(pit, IsabelleFact_ProveInTime)
                file.write(f"    statement: {pit.statement}\n")
                file.write(f"    pack: {pit.pack()}\n")
                results[i] = result
        # Invoke the continuation to get a gen_node, then fill
        gn = await e.kontinuation(results)
        root.session.age += 1
        node = await root.fill("2", _trivial_parsing(gn))
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
    await root.fill("1.1", Obvious.interactive_gen({"facts": [{"refer_by": "name", "name": "log_pow_cancel"}]}))
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
    await root.fill("2.1", Obvious.interactive_gen({"facts": [
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
    await root.fill("3.1", Obvious.interactive_gen({"facts": [
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
    # Step 1.1: Obvious with a ProveInTime fact, a library fact, and a local premise
    # Resolve the by-name facts first, then combine with the ProveInTime
    ml_state = root.locate_node("1").resulting_state()
    fetched = await ml_state.fetch_facts([
        {"refer_by": "name", "name": "log_base_pow"},
        {"refer_by": "name", "name": "h0"},
    ])
    facts: list[IsabelleFact] = [
        IsabelleFact_ProveInTime("(8::real) = (2::real) ^ (3::nat)"),
        *[f for f in fetched if isinstance(f, IsabelleFact_Presented)],
    ]
    root.session.age += 1
    await root.fill("1.1", Obvious.gen(Obvious_InternalToolArg(facts=facts)))
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
    await root.fill("1.1.1", Obvious.interactive_gen({"facts": []}))
    print_header("After proving h8", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1.2", Rewrite.interactive_gen({
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
    await root.fill("1.1.1", Obvious.interactive_gen({"facts": []}))
    # Step 1.2: Rewrite using h8eq + log_base_pow (triggers timeout fallback)
    root.session.age += 1
    await root.fill("1.2", Rewrite.interactive_gen({
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
    await root.fill("1.3", Obvious.interactive_gen({"facts": []}))
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
    await root.fill("2.1.1", Rewrite.interactive_gen({
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
        "statement": {"english": "x equals x plus 0", "isabelle": r"x + x \<ge> 0 \<Longrightarrow> x = x + 0"},
        "name": "lem1"
    }))
    print_header("After Have", file)
    root.print(0, file)
    root.session.age += 1
    await root.fill("1.1", Obvious.interactive_gen({"facts": []}))

# class TestCase_Interactive_Unfold:
#     pass

@model_test("IMO_1966_p5", "Test_imo_1966_p5.thy", 19)
async def _test_imo_1966_p5(root: Root, file: MyIO):
    """Test that inserting Have before Intro leaves the Intro unchanged.
    Reproduces the calling trace where Have nodes are inserted before the Intro step,
    and the Intro's proof state ($6 → $8) remains identical because unproven Have
    blocks use SORRY to restore the same enclosing state."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

    # 1. Insert Have eq1 before step 1 (Intro)
    root.session.age += 1
    await root.insert_before("1", Have.gen({
        "thought": "Since a(2) < a(1), a(3) < a(2), a(4) < a(3), we know a(1) > a(2) > a(3) > a(4). "
                   "Subtracting h7 from h6, the coefficients factor as (a(1)-a(2))*(-x1+x2+x3+x4)=0. "
                   "Since a(1)-a(2)>0, we get x1=x2+x3+x4.",
        "name": "eq1",
        "statement": {
            "english": "x(1) equals x(2) + x(3) + x(4)",
            "isabelle": "x (1::nat) = x (2::nat) + x (3::nat) + x (4::nat)"
        }
    }))
    print_header("After inserting Have eq1 before Intro", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

    # 2. Try Obvious to prove eq1 — fails (non-trivial)
    root.session.age += 1
    await root.fill("0A.1", Obvious.interactive_gen({
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
    await root.delete(["0A.1"])
    print_header("After deleting failed Obvious", file)
    buffer = io.StringIO()
    root.print(0, MyIO(buffer), update_line=True)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()

    # 4. Fill with intermediate Have: a1_gt_a3
    root.session.age += 1
    await root.fill("0A.1", Have.gen({
        "thought": "From assms(1) and assms(2), a(1) > a(3), so |a(1) - a(3)| = a(1) - a(3)",
        "name": "a1_gt_a3",
        "statement": {
            "english": "a(1) is greater than a(3)",
            "isabelle": "a (1::nat) > a (3::nat)"
        }
    }))
    # Prove a1_gt_a3 with Obvious — should succeed
    root.session.age += 1
    await root.fill("0A.1.1", Obvious.interactive_gen({
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
    await root.fill("0A.2", Have.gen({
        "thought": "From assms, a(1) > a(2) > a(3) > a(4), so a(1) > a(4)",
        "name": "a1_gt_a4",
        "statement": {
            "english": "a(1) is greater than a(4)",
            "isabelle": "a (1::nat) > a (4::nat)"
        }
    }))
    # Prove a1_gt_a4 with Obvious — should succeed
    root.session.age += 1
    await root.fill("0A.2.1", Obvious.interactive_gen({
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

    # 1. Baseline: no patterns
    results_base, warnings_base = await ml.semantic_knn("logarithm power", 5, [EntityKind.THEOREM])
    file.write(f"Baseline (no patterns): {len(results_base)} results, {len(warnings_base)} warnings\n")
    for score, rec in results_base:
        file.write(f"  {score:.3f} {rec.pretty_print}\n")
    assert not warnings_base, "Expected no warnings for baseline"

    # 2. With term_patterns: restrict to theorems containing "ln"
    results_term, warnings_term = await ml.semantic_knn("logarithm power", 10, [EntityKind.THEOREM],
                                   term_patterns=["ln ?x"])
    file.write(f"With term_patterns=[\"ln ?x\"]: {len(results_term)} results, {len(warnings_term)} warnings\n")
    for score, rec in results_term:
        file.write(f"  {score:.3f} {rec.pretty_print}\n")
    assert len(results_term) > 0, "Expected at least one result with term pattern 'ln ?x'"

    # 3. With type_patterns: restrict to theorems involving nat
    results_type, warnings_type = await ml.semantic_knn("logarithm", 10, [EntityKind.THEOREM],
                                   type_patterns=["nat"])
    file.write(f"With type_patterns=[\"nat\"]: {len(results_type)} results, {len(warnings_type)} warnings\n")
    for w in warnings_type:
        file.write(f"  Warning: {w}\n")
    for score, rec in results_type:
        file.write(f"  {score:.3f} {rec.pretty_print}\n")

    # 4. With theories_include
    results_thy, warnings_thy = await ml.semantic_knn("logarithm", 10, [EntityKind.THEOREM],
                                  theories_include=["HOL.Transcendental"])
    file.write(f"With theories_include=[\"HOL.Transcendental\"]: {len(results_thy)} results, {len(warnings_thy)} warnings\n")
    for w in warnings_thy:
        file.write(f"  Warning: {w}\n")
    for score, rec in results_thy:
        file.write(f"  {score:.3f} {rec.pretty_print}\n")

    # 5. Constants with type_patterns
    results_const, warnings_const = await ml.semantic_knn("logarithm", 5, [EntityKind.CONSTANT],
                                    type_patterns=["real \\<Rightarrow> real"])
    file.write(f"Constants with type_patterns=[\"real => real\"]: {len(results_const)} results, {len(warnings_const)} warnings\n")
    for w in warnings_const:
        file.write(f"  Warning: {w}\n")
    for score, rec in results_const:
        file.write(f"  {score:.3f} {rec.pretty_print}\n")

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
    for score, rec in results_nc:
        file.write(f"  {score:.3f} {rec.pretty_print}\n")
        assert "ln" in rec.name.lower(), f"Expected 'ln' in name: {rec.name}"
    assert len(results_nc) > 0, "Expected at least one result with name containing 'ln'"

    # 6c. name_contains: multiple substrings (conjunction)
    results_nc2, warnings_nc2 = await ml.semantic_knn("logarithm", 10, [EntityKind.THEOREM],
                                    name_contains=["ln", "real"])
    file.write(f"With name_contains=[\"ln\", \"real\"]: {len(results_nc2)} results\n")
    for score, rec in results_nc2:
        file.write(f"  {score:.3f} {rec.pretty_print}\n")
        assert "ln" in rec.name.lower() and "real" in rec.name.lower(), \
            f"Expected both 'ln' and 'real' in name: {rec.name}"
    assert len(results_nc2) <= len(results_nc), "Conjunction should narrow results"

    # 6d. name_contains with constants
    results_nc_c, warnings_nc_c = await ml.semantic_knn("logarithm", 5, [EntityKind.CONSTANT],
                                    name_contains=["ln"])
    file.write(f"Constants with name_contains=[\"ln\"]: {len(results_nc_c)} results\n")
    for score, rec in results_nc_c:
        file.write(f"  {score:.3f} {rec.pretty_print}\n")
        assert "ln" in rec.name.lower(), f"Expected 'ln' in name: {rec.name}"

    # 6e. Empty name_contains = same as baseline
    results_nc_e, _ = await ml.semantic_knn("logarithm power", 5, [EntityKind.THEOREM],
                                    name_contains=[])
    assert len(results_nc_e) == len(results_base), "Empty name_contains should match baseline"

    # 6f. Pattern-only search (query=None) with limit
    results_lim, warnings_lim = await ml.semantic_knn(None, 3, [EntityKind.THEOREM],
                                    name_contains=["ln"])
    file.write(f"Pattern-only with limit=3, name_contains=[\"ln\"]: {len(results_lim)} results\n")
    for _, rec in results_lim:
        file.write(f"  {rec.pretty_print}\n")
        assert "ln" in rec.name.lower(), f"Expected 'ln' in name: {rec.name}"
    assert len(results_lim) <= 3, f"Expected at most 3 results, got {len(results_lim)}"
    assert len(results_lim) > 0, "Expected at least one result"

    # 6g. Pattern-only with limit=1 returns exactly 1
    results_lim1, _ = await ml.semantic_knn(None, 1, [EntityKind.THEOREM],
                                    name_contains=["ln"])
    file.write(f"Pattern-only with limit=1: {len(results_lim1)} results\n")
    assert len(results_lim1) == 1, f"Expected exactly 1 result, got {len(results_lim1)}"

    # --- Error cases ---
    from Isabelle_RPC_Host.rpc import IsabelleError

    # 7. Invalid theory name in theories_include
    try:
        await ml.semantic_knn("logarithm", 5, [EntityKind.THEOREM],
                        theories_include=["Nonexistent_Theory_XYZ"])
        assert False, "Expected IsabelleError for invalid theory name"
    except IsabelleError as e:
        file.write(f"Invalid theory name error: {e}\n")

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
            await root.fill(f"1.{i}.1", Obvious.interactive_gen({"facts": []}))
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
    """Reproduce: Intro splits A ∧ B ∧ C into subgoals, then Obvious
    on a subgoal may generate infinite 'True' pending goals."""
    print_header("Initial State", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)

    # The auto-Intro at step 1 should introduce premises P, Q, R
    # and split the conjunction P ∧ Q ∧ R into subgoals.
    # Try Obvious on the first subgoal (1.1.1).
    root.session.age += 1
    await root.fill("1.1.1", Obvious.interactive_gen({"facts": []}))
    print_header("After Obvious on 1.1.1", file)
    root.print(0, file)
    print_header("Overview after 1.1.1", file)
    root.quickview(0, file)

    # If the bug exists, a "True" pending goal appears in 1.1,
    # requiring step 1.1.2 to be filled.
    root.session.age += 1
    try:
        await root.fill("1.1.2", Obvious.interactive_gen({"facts": []}))
        print_header("After Obvious on 1.1.2 (True subgoal appeared)", file)
        root.print(0, file)
        print_header("Overview after 1.1.2", file)
        root.quickview(0, file)
    except Exception as e:
        file.write(f"No step 1.1.2 needed (no bug): {type(e).__name__}: {e}\n")

    # If the bug persists, yet another "True" would appear for 1.1.3.
    root.session.age += 1
    try:
        await root.fill("1.1.3", Obvious.interactive_gen({"facts": []}))
        print_header("After Obvious on 1.1.3 (True subgoal appeared again)", file)
        root.print(0, file)
        print_header("Overview after 1.1.3", file)
        root.quickview(0, file)
    except Exception as e:
        file.write(f"No step 1.1.3 needed (no bug): {type(e).__name__}: {e}\n")

    # Now try to close the remaining subgoals 1.2 and 1.3.
    root.session.age += 1
    try:
        await root.fill("1.2.1", Obvious.interactive_gen({"facts": []}))
        print_header("After Obvious on 1.2.1", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"Cannot fill 1.2.1: {type(e).__name__}: {e}\n")

    root.session.age += 1
    try:
        await root.fill("1.3.1", Obvious.interactive_gen({"facts": []}))
        print_header("After Obvious on 1.3.1", file)
        root.print(0, file)
    except Exception as e:
        file.write(f"Cannot fill 1.3.1: {type(e).__name__}: {e}\n")

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


@model_test("ForeNodeFail", "Test_ForeNodeFail.thy", 13)
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
    await root.fill("1.1", Obvious.interactive_gen({"facts": []}))
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
    await root.fill("3", Obvious.interactive_gen({"facts": []}))
    step3 = root.locate_node("3")
    file.write(f"Step 3 status (fill after failed): {step3.status.status.value}\n")
    assert step3.status.status == EvaluationStatus.Status.CANCELLED, \
        f"fill: Expected CANCELLED but got {step3.status.status.value}"
    print_header("After step 3 (fill, should be cancelled)", file)
    root.print(0, file)

    # Insert before step 3: predecessor is step 2 (FAILURE), should be CANCELLED
    root.session.age += 1
    inserted = await root.insert_before("3", Have.gen({
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
    by the driver, leaving working_interactions stuck."""
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
    bad_pit = IsabelleFact_ProveInTime(stmt_ascii)
    file.write(f"_filter_unprovable([ProveInTime(\"{stmt_ascii}\")]): ")
    try:
        kept, warnings = await _filter_unprovable([bad_pit], ml_state)
        file.write(f"kept={len(kept)}, warnings={warnings}\n")
    except IsabelleError as e:
        file.write(f"UNCAUGHT IsabelleError: {e}\n")
    except Exception as e:
        file.write(f"UNCAUGHT {type(e).__name__}: {e}\n")

    # --- Test 4: _filter_unprovable with Unicode ¦ variant ---
    bad_pit_unicode = IsabelleFact_ProveInTime(stmt_unicode)
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
        await root.fill("1", Obvious.gen(Obvious_InternalToolArg(facts=[bad_pit])))
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
                  Obvious.interactive_gen({"facts": []}))
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
    await root.fill("2", Obvious.interactive_gen({"facts": []}))
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
        case_num = len(TESTS)
        passed = 0
        for i, test_case in enumerate(TESTS.values()):
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
