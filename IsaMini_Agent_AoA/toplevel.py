from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import *
from typing import Any
from . import driver_claude_code
import sys

class TestFailed(Exception):
    pass

class UnknownDriver(AoA_Error):
    def __init__(self, driver: str):
        super().__init__(f"Unknown driver: {driver}")

@isabelle_remote_procedure("IsaMini.AoA")
def IsaMini_AoA(data: tuple[Any, Any, str], connection: Connection):
    (global_context, ptree, driver) = data
    global_context = Context.unpack(global_context)
    ptree = unpack_MLPT(ptree)
    if driver.startswith("test."):
        # Run specific test associated with the driver
        session = Session(connection.server.logger)
        root = Root((global_context, ptree), connection)
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
        drv = Session.Driver.get(driver)
        if drv is None:
            raise UnknownDriver(driver)
        session = drv(connection.server.logger)
        root = Root((global_context, ptree), connection)
        session.initialize(root)
        session.run()

    connection.write((0, None))
    if root.is_proof_finished():
        return ([x.pack() for x in root.assemble()], root.final_ml_state.name)
    else:
        return ([x.pack() for x in root.assemble()], None)
    # Finally, we return the constructed proof



