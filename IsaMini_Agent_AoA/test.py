import os
import time
from IsaREPL import REPLFail
from typing import Any, NamedTuple, Sequence, TypedDict, Callable, TextIO, cast
from . import model
from .model import *

class TestCase(NamedTuple):
    name: str
    opr: Callable[[Root, MyIO], None]
    file: str
    line: int

    def expected_yaml(self) -> str:
        correct_yaml_path = os.path.join(os.path.dirname(__file__), 'Tests', self.name + '.yml')
        if os.path.isfile(correct_yaml_path):
            with open(correct_yaml_path, 'r') as f:
                return f.read()
        else:
            return ""
    def write_expected_yaml(self, yaml: str):
        correct_yaml_path = os.path.join(os.path.dirname(__file__), 'Tests', self.name + '.yml')
        with open(correct_yaml_path, 'w') as f:
            f.write(yaml)
    

TESTS : dict[str, TestCase] = {}
def test(name: str, file: str, line: int):
    def decorator(func: Callable[[Root, MyIO], None]):
        TESTS[name] = TestCase(name, func, file, line)
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
    goal.append(InferenceRule.gen({"thought": "Proof by contradiction", "rule": None}))
    print_header("Setting the inference rule", file)
    root.print(0, file)
    goal.append(Obtain.gen({"thought": "I don't know", "variables": [{"name": "m", "type": "nat"}, {"name": "n", "type": "nat"}],
            "constraints": [{"isabelle": "¦sqrt 2¦ = m / n", "english": "some fancy explanation"}]}))
    print_header("Obtain m n", file)
    root.print(0, file)
    #node = root.locate_node("2.1") # not appear
    root.fill("2.1", Obvious.gen({"thought": "Obviously the statement holds.", "facts": []}))
    print_header("Obvious", file)
    root.print(0, file)
    root.fill("3", Have.gen({"thought": "I don't know", "statement": {"english": "some fancy explanation", "isabelle": "m^2 = (sqrt 2)^2 * n^2"}}))
    root.fill("3.1", Obvious.gen({"thought": "Obviously the statement holds.", "facts": []}))
    print_header("Have", file)
    root.print(0, file)

@test("branch", "Test001.thy", 6)
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

@test("EquivDerive", "Test003.thy", 8)
def _test_EquivDerive(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("2", InferenceRule.gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@test("IntroConj", "Test003.thy", 8)
def _test_IntroConj(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("2", InferenceRule.gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@test("IntroConj_short", "Test003.thy", 8)
def _test_IntroConj_short(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    root.fill("2", InferenceRule.gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

@test("CaseSplit", "Test006.thy", 9)
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

@test("Induction", "Test006.thy", 9)
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
    root.fill("1.Nil.1", Obvious.gen({
        "thought": "Obviously the statement holds.",
        "facts": []
    }))
    print_header("Obvious", file)
    root.print(0, file)
    root.fill("1.Cons.1", Obvious.gen({
        "thought": "Obviously the statement holds.",
        "facts": [{"refer_by": "name", "name": "Cons.IH"}]
    }))
    print_header("Obvious", file)
    root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@test("Suffices", "Test_Suffices.thy", 7)
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
    root.fill("1.1", Obvious.gen({
        "thought": "The implication is obvious",
        "facts": []
    }))
    print_header("After proving implication", file)
    root.print(0, file)
    # Now we need to prove: x * x + 1 > 0
    root.fill("2", Obvious.gen({
        "thought": "This is obviously true",
        "facts": []
    }))
    print_header("After proving suffices goal", file)
    root.print(0, file)
    unfinished_nodes = set()
    root.unfinished_nodes(unfinished_nodes)
    file.write(f"Unfinished nodes: {len(unfinished_nodes)}\n")

@test("Rewrite1", "Test_Rewrite.thy", 9)
def _test_Rewrite1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    root.fill("1", Rewrite.gen({
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

@test("Rewrite2", "Test_Rewrite2.thy", 9)
def _test_Rewrite1(root: Root, file: MyIO):
    print_header("Initial YAML", file)
    root.print(0, file)
    # Use Rewrite to simplify the premises h1 and h2
    root.fill("1", Rewrite.gen({
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
    for i, test_case in enumerate(TESTS.values()):
        repl.rollback('init')
        print(f"Running test [{i+1}/{case_num}] {test_case.name}")
        abs_file_path = os.path.abspath(os.path.join(os.path.dirname(__file__), "Tests", test_case.file))
        repl.file(abs_file_path, test_case.line, 0, cache_position=False, use_cache=False)
        repl.run_app('Minilang.AoA')
        invocation_id = f"{mode}.{test_case.name}"
        mp.pack((invocation_id, f"{mode}.{test_case.name}", (_cfg, _budget)), repl.cout)
        repl.cout.flush()
        try:
            (success, elapsed, cpu_time) = Client._parse_control_(repl.unpack.unpack())
        except REPLFail as e:
            if str(e) == 'Agent gives up':
                continue
            else:
                raise
        if success:
            print(f"\033[92mTest {test_case.name} passed, elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
        else:
            print(f"\033[91mTest {test_case.name} failed, elapsed: {elapsed}ms, cpu_time: {cpu_time}ms\033[0m")
