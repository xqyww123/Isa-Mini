from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import *
from typing import Any
from . import driver_claude_code
import sys
import io
import os
import tempfile
import subprocess

class TestFailed(Exception):
    pass

class UnknownDriver(AoA_Error):
    def __init__(self, driver: str):
        super().__init__(f"Unknown driver: {driver}")

def show_colored_diff(actual: str, expected: str, test_name: str):
    """Write two versions to temporary files and display colored diff."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.actual.yaml', delete=False) as actual_file:
        actual_file.write(actual)
        actual_path = actual_file.name

    with tempfile.NamedTemporaryFile(mode='w', suffix='.expect.yaml', delete=False) as expected_file:
        expected_file.write(expected)
        expected_path = expected_file.name

    try:
        # Run colored diff
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
        # Clean up temporary files
        os.unlink(actual_path)
        os.unlink(expected_path)

@isabelle_remote_procedure("IsaMini.AoA")
def IsaMini_AoA(data: tuple[Any, Any, str, str, str], connection: Connection):
    (global_context, ptree, driver, log_dir, invocation_id) = data

    # Environment variable AoA_LOG_DIR overrides user-provided log_dir
    env_log_dir = os.environ.get('AoA_LOG_DIR')
    if env_log_dir:
        log_dir = env_log_dir

    # Construct actual log path: log_dir/invocation_id
    if log_dir != "":
        actual_log_path = os.path.join(log_dir, invocation_id)
    else:
        actual_log_path = ""

    global_context = Context.unpack(global_context)
    ptree = unpack_MLPT(ptree)
    if driver.startswith("test."):
        # Run specific test associated with the driver
        with Session(connection.server.logger, actual_log_path) as session:
            root = Root((global_context, ptree), connection)
            session.initialize(root)
            test_name = driver[len("test."):]
            from .test import TESTS
            if test_name in TESTS:
                buffer = io.StringIO()
                case = TESTS[test_name]
                case.opr(root, MyIO(buffer))
                correct_yaml = case.expected_yaml()
                if correct_yaml != "":
                    if buffer.getvalue() != correct_yaml:
                        show_colored_diff(buffer.getvalue(), correct_yaml, test_name)
                        #raise TestFailed(f"Test Faild on '{test_name}': \n{buffer.getvalue()}\n------------------\nExpected:\n{correct_yaml}")
                        raise TestFailed(f"Test Faild on '{test_name}'")
                else:
                    case.write_expected_yaml(buffer.getvalue())
            else:
                raise TestFailed(f"Test Not Found on '{test_name}'")
    else:
        drv = Session.Driver.get(driver)
        if drv is None:
            raise UnknownDriver(driver)
        with drv(connection.server.logger, actual_log_path) as session:
            root = Root((global_context, ptree), connection)
            session.initialize(root)
            session.run()

    connection.write((0, None))
    if root.is_proof_finished():
        return ([x.pack() for x in root.assemble()], root.final_ml_state.name)
    else:
        return ([x.pack() for x in root.assemble()], None)
    # Finally, we return the constructed proof



