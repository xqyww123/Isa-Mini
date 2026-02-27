from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import Goals, Root, Minilang_Operation, unpack_MLPT, InferenceRule, Obtain, Obvious, Have
from typing import Any
import sys

class TestFailed(Exception):
    pass

@isabelle_remote_procedure("IsaMini.AoA")
def IsaMini_AoA(data: tuple[Any, Any, str], connection: Connection):
    (goals, ptree, driver) = data
    goals = Goals.unpack(goals)
    ptree = unpack_MLPT(ptree)
    root = Root((goals, ptree), connection)
    if driver.startswith("test."):
        # Run specific test associated with the driver
        test_name = driver[len("test."):]
        from .test import TESTS
        import io
        import os
        if test_name in TESTS:
            buffer = io.StringIO()
            case = TESTS[test_name]
            case.opr(root, buffer)
            correct_yaml = case.expected_yaml()
            if correct_yaml != "":
                if buffer.getvalue() != correct_yaml:
                    raise TestFailed(f"Test '{test_name}' failed: \n{buffer.getvalue()}\n------------------\nExpected:\n{correct_yaml}")
            else:
                case.write_expected_yaml(buffer.getvalue())
        else:
            raise TestFailed(f"Test '{test_name}' not found in TESTS")
    else:
        # handle drivers here
        # Do the Agent proof here
        # You can use `root.locate_node(id)` to locate a node by its id
        # then call target_node.insert_before(gen_node) to insert a new node before the target node
        # or target_node.append(gen_node) to append a new node after the target node
        # In this way you edit the abstract proof tree
        # until the root.is_proof_finished() is True
        # then you can claim the proof is constructed successfully
        raise NotImplementedError(f"Unknown driver: {driver}")

    connection.write((0, None))
    if root.is_proof_finished():
        return ([x.pack() for x in root.assemble()], root.final_ml_state.name)
    else:
        return ([x.pack() for x in root.assemble()], None)
    # Finally, we return the constructed proof



