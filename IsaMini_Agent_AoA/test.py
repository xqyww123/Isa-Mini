import os
from typing import Any, NamedTuple, Sequence, TypedDict, Callable, TextIO, cast
from . import model
from .model import *

class TestCase(NamedTuple):
    name: str
    opr: Callable[[Root, TextIO], None]
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
    def decorator(func: Callable[[Root, TextIO], None]):
        TESTS[name] = TestCase(name, func, file, line)
        return func
    return decorator

def print_header(msg: str, file: TextIO):
    print("-"*50, file=file)
    print(msg, file=file)
    print("-"*50, file=file)

#@test("sqrt2", "Test_sqrt2.thy", 6)
def _test_sqrt2(root: Root, file: TextIO):
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

#@test("branch", "Test001.thy", 6)
def _test_branch(root: Root, file: TextIO):
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

@test("EquivDerive", "Test003.thy", 6)
def _test_EquivDerive(root: Root, file: TextIO):
    print_header("Initial YAML", file)
    #root.print(0, file)
    root.fill("1", Intro.gen({
        "thought": "Destruct equivalence",
        "variable_bindings": ["AAA"],
        "fact_bindings": []
    }))
    root.fill("2", InferenceRule.gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    import sys
    file = sys.stdout
    print_header("Inference Rule", file)
    root.print(0, file)
    root.fill("2", InferenceRule.gen({
        "thought": "Destruct equivalence",
        "rule": None
    }))
    print_header("Inference Rule", file)
    root.print(0, file)

def run_all_tests(repl_addr: str, mode="test", logger: logging.Logger | None = None):
    model.GLOBAL_LOGGER = logger
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
        mp.pack((f"{mode}.{test_case.name}", (_cfg, _budget)), repl.cout)
        repl.cout.flush()
        (success, elapsed, cpu_time) = Client._parse_control_(repl.unpack.unpack())
        if success:
            print(f"\033[92mTest {test_case.name} passed, elapsed: {elapsed}s, cpu_time: {cpu_time}s\033[0m")
        else:
            print(f"\033[91mTest {test_case.name} failed, elapsed: {elapsed}s, cpu_time: {cpu_time}s\033[0m")
