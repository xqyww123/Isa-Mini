import asyncio
import inspect
import os
import time
from IsaREPL import REPLFail
from typing import Any, Awaitable, Coroutine, NamedTuple, Sequence, TypedDict, Callable, TextIO, Union, cast
from . import model
from .model import *
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
    def run(self, connection: Connection, log_dir: str, global_context: Context, ptree: ML_ProofTree) -> Root:
        raise NotImplementedError("Subclass must implement run method")
    
type _TestOpr = Callable[[Root, MyIO], Union[None, Awaitable[None]]]

class ModelTestCase(TestCase):
    def __init__(self, name : str, file: str, line: int, opr: _TestOpr):
        super().__init__(name, file, line)
        self.opr = opr
    def run(self, connection: Connection, log_dir: str, global_context: Context, ptree: ML_ProofTree) -> Root:
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
        with Session(connection.server.logger, log_dir) as session:
            root = Root((global_context, ptree), connection, session)
            session.initialize(root)
            buffer = io.StringIO()
            result = self.opr(root, MyIO(buffer))
            if inspect.iscoroutine(result):
                asyncio.run(result)
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
def _test_sqrt2(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    #goal = root.locate_node("goal1") # the same as root.sub_nodes[1]
    goal = root.sub_nodes[1]
    goal.append(InferenceRule.interactive_gen({"thought": "Proof by contradiction", "rule": None}))
    print_header("Setting the inference rule", file)
    root.print(0, file)
    goal.append(Obtain.gen({"thought": "I don't know", "variables": [{"name": "m", "type": "nat"}, {"name": "n", "type": "nat"}],
            "constraints": [{"isabelle": "¦sqrt 2¦ = m / n", "english": "some fancy explanation"}]}))
    print_header("Obtain m n", file)
    root.print(0, file)
    #node = root.locate_node("2.1") # not appear
    root.fill("2.1", Obvious.interactive_gen({"facts": []}))
    print_header("Obvious", file)
    root.print(0, file)
    root.fill("3", Have.gen({"thought": "I don't know", "statement": {"english": "some fancy explanation", "isabelle": "m^2 = (sqrt 2)^2 * n^2"}, "name": "helper_lemma"}))
    root.fill("3.1", Obvious.interactive_gen({"facts": []}))
    print_header("Have", file)
    root.print(0, file)

@model_test("Branch1", "Test_Branch.thy", 8)
def _test_branch(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("1", Branch.gen({
        "thought": "I don't know",
        "cases": [
            {"english": "in case x is positive", "isabelle": "x > 0"},
            {"english": "in case x is negative", "isabelle": "x < 0"},
            {"english": "in case x is zero", "isabelle": "x = 0"},
        ]
    }))
    print_header("Branch", file)
    root.print(0, file)

@model_test("EquivDerive", "Test003.thy", 8)
def _test_EquivDerive(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("2", InferenceRule.interactive_gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("IntroConj", "Test003.thy", 8)
def _test_IntroConj(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("2", InferenceRule.interactive_gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("IntroConj_short", "Test003.thy", 8)
def _test_IntroConj_short(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("2", InferenceRule.interactive_gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@model_test("CaseSplit", "Test006.thy", 9)
def _test_CaseSplit(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("1", CaseSplit.gen({
        "thought": "Case split",
        "target_isabelle_term": r"l"
    }))
    print_header("Case Split", file)
    root.print(0, file)
    root.fill("1.Nil.1", CaseSplit.gen({
        "thought": "Case split",
        "target_isabelle_term": r"l"
    }))
    print_header("Case Split", file)
    root.print(0, file)

@model_test("Induction", "Test006.thy", 9)
def _test_Induction(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("1", Induction.gen({
        "thought": "some thought about Induction",
        "target_isabelle_term": r"l",
        "variables": [{"name": "l", "status": "fixed"}],
        "rule": None
    }))
    print_header("Induction", file)
    root.print(0, file)
    root.fill("1.Nil.1", Obvious.interactive_gen({"facts": []}))
    print_header("Obvious", file)
    root.print(0, file)
    root.fill("1.Cons.1", Obvious.interactive_gen({
        "facts": [{"refer_by": "name", "name": "Cons.IH"}]
    }))
    print_header("Obvious", file)
    root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Suffices", "Test_Suffices.thy", 9)
def _test_Suffices(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use "it suffices to show" that x*x + 1 > 0
    root.fill("1", Suffices.gen({
        "thought": "It suffices to show a stronger statement",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "isabelle": "x * x + 1 > 0"
        }
    }))
    print_header("After Suffices", file)
    root.print(0, file)
    # Now we need to prove: (x * x + 1 > 0) --> (x * x >= 0)
    root.fill("1.1", Obvious.interactive_gen({"facts": []}))
    print_header("After proving implication", file)
    root.print(0, file)
    # Now we need to prove: x * x + 1 > 0
    root.fill("2", Obvious.interactive_gen({"facts": []}))
    print_header("After proving suffices goal", file)
    root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Rewrite1", "Test_Rewrite.thy", 12)
def _test_Rewrite1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    root.fill("1", Rewrite.interactive_gen({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"refer_by": "name", "name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["h2"]
    }))
    print_header("After Rewrite", file)
    root.print(0, file)
    root.rename_fact("premise0", "my_premise")
    root.rename_var("aAa", "yyy")
    print_header("After Rename Fact", file)
    root.print(0, file)

@model_test("Rewrite2", "Test_Rewrite2.thy", 12)
def _test_Rewrite2(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    root.insert_before("1", Rewrite.interactive_gen({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"refer_by": "name", "name": "h1"}],
        "use system simplifiers": True,
        "rewrite goal": False,
        "rewrite premises": ["h2"]
    }))
    print_header("After Rewrite", file)
    root.print(0, file)
    root.rename_fact("premise0", "my_premise")
    root.rename_var("aAa", "yyy")
    print_header("After Rename Fact", file)
    root.print(0, file)
    root.delete(["0A"])
    print_header("After Remove the Rewrite", file)
    root.print(0, file)

@model_test("Rewrite3", "Test_Rewrite3.thy", 13)
def _test_Rewrite3(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    root.fill("1", Have.gen({
        "thought": "I don't know",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "isabelle": "x = y"
        },
        "name": "lem1"
    }))
    root.fill("1.1", Obvious.interactive_gen({"facts": []}))
    print_header("After Have", file)
    root.print(0, file)
    root.fill("2", Rewrite.interactive_gen({
        "thought": "Rewrite the premises to simplify the equations",
        "using": [{"refer_by": "name", "name": "lem1"}],
        "use system simplifiers": False,
        "rewrite goal": True,
        "rewrite premises": []
    }))
    print_header("After Rewrite", file)
    root.print(0, file)
    root.amend("1", Have.gen({
        "thought": "I don't know!!!",
        "statement": {
            "english": "x squared plus 1 is greater than 0",
            "isabelle": "x = y * 1"
        },
        "name": "lem1"
    }))
    print_header("After Amend Have", file)
    root.print(0, file)
    root.amend("1", Have.gen({
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
def _test_Witness1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)

    # Use Witness to provide a witness for the existential goal
    root.fill("1", Witness.gen({
        "thought": "Provide 5 as witness for the existential",
        "witness": "5"
    }))
    print_header("After Witness", file)
    root.print(0, file)

    # Prove the remaining goal (5 = 5) using Obvious
    root.fill("2", Obvious.interactive_gen({"facts": []}))
    print_header("After Obvious", file)
    root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Witness2", "Test_Witness2.thy", 8)
def _test_Witness2(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)

    try:
    # Use Witness to provide a witness (1) for the existential with property
        root.fill("1", Witness.gen({
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
    root.fill("1", Unfold.gen(Unfold_ToolArg_internal(
        thought="Unfold the goal",
        targets=["XXX"],
        fact_refs=[IsabelleFact_Presented("XXX_def", "XXX_def", {"refer_by": "name", "name": "XXX_def"}, ["Fake"])]
    )))
    print_header("After Unfold", file)
    root.print(0, file)
    try:
        root.amend("1", Unfold.interactive_gen({
            "thought": "Unfold the goal",
            "targets": ["XXX"],
        }))
    except RaiseInteraction as e:
        print_header("Interaction Prompt", file)
        assert len(e.interactions) == 1
        e.interactions[0].prompt(0, file)
        gen_node = await e.kontinuation([inter.answer([1]) for inter in e.interactions])
        root.amend("1", gen_node)
        print_header("After Answer", file)
        root.print(0, file)

    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@model_test("Delete1", "Test_Delete1.thy", 13)
def _test_Delete1(root: Root, file: MyIO):
    """Test deleting a single step."""
    print_header("Initial YAML", file)
    root.print(0, file)
    root.session.age += 1
    root.fill("1", Have.gen({
        "thought": "helper",
        "statement": {"english": "x equals y plus 0", "isabelle": "x = y"},
        "name": "lem1"
    }))
    root.session.age += 1
    root.fill("1.1", Obvious.interactive_gen({"facts": []}))
    root.session.age += 1
    root.fill("2", Rewrite.interactive_gen({
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
    root.delete(["1"])
    print_header("After deleting step 1 (Have)", file)
    root.print(0, file)
    print_header("Overview", file)
    root.quickview(0, file)
    root.reset_changed()
    # Insert a Have before step 2
    root.session.age += 1
    root.insert_before("2", Have.gen({
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
# def _test_Delete2(root: Root, file: MyIO):
#     """Test deleting multiple steps at once."""
#     print_header("Initial YAML", file)
#     root.print(0, file)
#     root.session.age += 1
#     root.fill("1", Have.gen({
#         "thought": "helper",
#         "statement": {"english": "x equals y", "isabelle": "x = y"},
#         "name": "lem1"
#     }))
#     root.session.age += 1
#     root.fill("1.1", Obvious.interactive_gen({"facts": []}))
#     root.session.age += 1
#     root.fill("2", Have.gen({
#         "thought": "helper2",
#         "statement": {"english": "y equals z", "isabelle": "y = z"},
#         "name": "lem2"
#     }))
#     root.session.age += 1
#     root.fill("2.1", Obvious.interactive_gen({"facts": []}))
#     root.session.age += 1
#     root.fill("3", Obvious.interactive_gen({"facts": []}))
#     print_header("After building 5 steps", file)
#     root.print(0, file)
#     buffer = io.StringIO()
#     root.print(0, MyIO(buffer), update_line=True)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset_changed()
#     # Delete two steps at once
#     root.session.age += 1
#     root.delete(["1", "2"])
#     print_header("After deleting steps 1 and 2", file)
#     root.print(0, file)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset_changed()
# 
# @model_test("Delete3", "Test_Delete3.thy", 13)
# def _test_Delete3(root: Root, file: MyIO):
#     """Test deleting with duplicate IDs (deduplication)."""
#     print_header("Initial YAML", file)
#     root.print(0, file)
#     root.session.age += 1
#     root.fill("1", Have.gen({
#         "thought": "helper",
#         "statement": {"english": "x equals y", "isabelle": "x = y"},
#         "name": "lem1"
#     }))
#     root.session.age += 1
#     root.fill("1.1", Obvious.interactive_gen({"facts": []}))
#     root.session.age += 1
#     root.fill("2", Obvious.interactive_gen({"facts": []}))
#     print_header("After building steps", file)
#     root.print(0, file)
#     buffer = io.StringIO()
#     root.print(0, MyIO(buffer), update_line=True)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset_changed()
#     # Delete with duplicate ID — should deduplicate and not error
#     root.session.age += 1
#     root.delete(["1", "1"])
#     print_header("After deleting step 1 (with duplicate)", file)
#     root.print(0, file)
#     print_header("Overview", file)
#     root.quickview(0, file)
#     root.reset_changed()

@model_test("ReferFactByStatement", "Test001.thy", 6)
def _test_ReferFactByStatement(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    fullname = root.ml_state.fetch_facts([{"refer_by": "name", "name": "notI"}])
    file.write(f"Fullname of notI: {fullname}\n")
    # FactByStatement search is not yet implemented; just test FactByName for now
    return

@model_test("RetrieveFact", "Test_RetrieveFact.thy", 8)
async def _test_RetrieveFact(root: Root, file: MyIO):
    """Test retrieve_facts and FactByStatement interaction.
    Reproduces 'Unknown ancestor theory ""' bug."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # 1. Test fetch_facts with various fact types
    fetched = root.ml_state.fetch_facts([
        {"refer_by": "name", "name": "log_nat_power"},       # known fact → IsabelleFact_Presented
        {"refer_by": "name", "name": "nonexistent_lemma"},    # unknown fact → IsabelleFact_Unfound
        {"refer_by": "statement", "statement": "8 = 2^3"},   # statement → Interaction_RetrieveFact
    ])
    for i, f in enumerate(fetched):
        file.write(f"  fetch_facts[{i}]: {type(f).__name__}\n")
    assert isinstance(fetched[0], IsabelleFact_Presented)
    assert isinstance(fetched[1], IsabelleFact_Unfound)
    assert isinstance(fetched[2], Interaction_RetrieveFact)
    # 2. Test Obvious with both a FactByStatement and a FactByName.
    #    The FactByStatement triggers Interaction_RetrieveFact which calls
    #    semantic_knn → entities_of → retrieve_facts internally.
    root.session.age += 1
    try:
        root.fill("2", Obvious.interactive_gen({
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
            if isinstance(inter, Interaction_RetrieveFact):
                file.write(f"    query: {inter.query}\n")
                file.write(f"    candidates: {len(inter.candidate_facts)}\n")
                # Answer with a ProveInTime statement
                result = inter.answer("(8::nat) = 2^3")
                file.write(f"    ProveInTime answer: {type(result).__name__}\n")
                assert isinstance(result, IsabelleFact_ProveInTime)
                file.write(f"    statement: {result.statement}\n")
                file.write(f"    pack: {result.pack()}\n")
                results[i] = result
        # Invoke the continuation to get a gen_node, then fill
        gen = await e.kontinuation(results)
        root.session.age += 1
        node = root.fill("2", gen)
        file.write(f"Filled node: {type(node).__name__}, id={node.id}\n")
        node.print(1, file, show_warnings=True)
    print_header("After fill", file)
    root.print(0, file)
    return

@model_test("RetrieveFact2", "Test_RetrieveFact.thy", 8)
async def _test_RetrieveFact2(root: Root, file: MyIO):
    """Test retrieve_facts and FactByStatement interaction.
    Reproduces 'Unknown ancestor theory ""' bug."""
    print_header("Initial YAML", file)
    root.print(0, file)
    # 1. Test fetch_facts with various fact types
    fetched = root.ml_state.fetch_facts([
        {"refer_by": "name", "name": "log_nat_power"},       # known fact → IsabelleFact_Presented
        {"refer_by": "name", "name": "nonexistent_lemma"},    # unknown fact → IsabelleFact_Unfound
        {"refer_by": "statement", "statement": "8 = 2^3"},   # statement → Interaction_RetrieveFact
    ])
    for i, f in enumerate(fetched):
        file.write(f"  fetch_facts[{i}]: {type(f).__name__}\n")
    assert isinstance(fetched[0], IsabelleFact_Presented)
    assert isinstance(fetched[1], IsabelleFact_Unfound)
    assert isinstance(fetched[2], Interaction_RetrieveFact)
    # 2. Test Obvious with both a FactByStatement and a FactByName.
    #    The FactByStatement triggers Interaction_RetrieveFact which calls
    #    semantic_knn → entities_of → retrieve_facts internally.
    root.session.age += 1
    try:
        root.fill("2", Obvious.interactive_gen({
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
            if isinstance(inter, Interaction_RetrieveFact):
                file.write(f"    query: {inter.query}\n")
                file.write(f"    candidates: {len(inter.candidate_facts)}\n")
                # Answer with a ProveInTime statement
                result = inter.answer("(9::nat) = 2^3")
                file.write(f"    ProveInTime answer: {type(result).__name__}\n")
                assert isinstance(result, IsabelleFact_ProveInTime)
                file.write(f"    statement: {result.statement}\n")
                file.write(f"    pack: {result.pack()}\n")
                results[i] = result
        # Invoke the continuation to get a gen_node, then fill
        gen = await e.kontinuation(results)
        root.session.age += 1
        node = root.fill("2", gen)
        file.write(f"Filled node: {type(node).__name__}, id={node.id}\n")
        node.print(1, file, show_warnings=True)
    print_header("After fill", file)
    root.print(0, file)
    return

# class TestCase_Interactive_Unfold:
#     pass

def run_all_tests(repl_addr: str, mode="test", logger: logging.Logger | None = None):
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
    repl = Client(repl_addr, 'HOL', timeout=1200)
    repl.load_theory(['Minilang_Agent.Minilang_Agent'])
    repl.record_state("init")
    case_num = len(TESTS)
    passed = 0
    for i, test_case in enumerate(TESTS.values()):
        repl.rollback('init')
        print(f"Running test [{i+1}/{case_num}] {test_case.name}")
        abs_file_path = os.path.abspath(os.path.join(os.path.dirname(__file__), "Tests", test_case.file))
        repl.file(abs_file_path, test_case.line, 0, cache_position=False, use_cache=False)
        repl.run_app('Minilang.AoA')
        invocation_id = f"{mode}.{test_case.name}"
        mp.pack((invocation_id, f"{mode}.{test_case.name}", (_cfg, _budget), None), repl.cout)
        repl.cout.flush()
        try:
            (status, elapsed, cpu_time) = Client._parse_control_(repl.unpack.unpack())
        except REPLFail as e:
            print(f"\033[91mTest {test_case.name} error: {e}\033[0m")
            continue
        if status == "success" or status == "agent_gives_up":
            passed += 1
            print(f"\033[92mTest {test_case.name} passed (status={status}), elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
        else:
            print(f"\033[91mTest {test_case.name} failed (status={status}), elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
    print(f"\n{passed}/{case_num} tests passed")
