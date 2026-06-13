#!/usr/bin/env python3
# NOTE: Full test output is very long. Redirect to a file when running all tests:
#   python test_AoA.py > /tmp/aoa_test_results.txt 2>&1
# IMPORTANT: Never delete golden YAML in test cases (Tests/*.yml).
#   You may edit them manually to update expected output if you are absolutely certain.
# NOTE: "remote_error" failures ARE actually mismatches against golden YAML, not RPC
#   failures. After running tests, merge all diffs against golden YAMLs to a single
#   file for review if any such diffs are present.
import argparse
import os
import sys
import threading
import time
import traceback
import asyncio
import Isabelle_RPC_Host
from IsaMini.AoA.test import run_all_tests

parser = argparse.ArgumentParser(description="Run IsaMini Agent AoA tests")
parser.add_argument(
    "--repl-addr",
    default="127.0.0.1:6666",
    help="REPL server address (host:port), default: 127.0.0.1:6666",
)
parser.add_argument(
    "--filter", "-f",
    default=None,
    help="Run only test cases whose name contains this substring",
)
parser.add_argument(
    "--exclude", "-x",
    default=None,
    help="Skip test cases whose name contains any of these substrings (comma-separated)",
)
parser.add_argument(
    "--sh-timeout",
    type=int,
    default=10,
    help="Sledgehammer timeout in seconds (default: 10)",
)
parser.add_argument(
    "--rpc-addr",
    default="127.0.0.1:27182",
    help="RPC host address to serve on (host:port), default: 127.0.0.1:27182. "
         "Must match the RPC_Host environment of the target REPL server; use a "
         "non-default port to run isolated from other RPC hosts on this machine.",
)
args = parser.parse_args()
if args.filter is not None:
    os.environ["TEST_FILTER"] = args.filter
if args.exclude is not None:
    os.environ["TEST_EXCLUDE"] = args.exclude
rpc_addr = args.rpc_addr
logger = Isabelle_RPC_Host.mk_logger_(rpc_addr, None)

# Headless test harness: nobody can click a PIDE dialogue (Active.dialog_text
# blocks forever in a REPL), so auto-answer every dialogue with its first
# option — e.g. the Semantic_Embedding "N entities to embed. Proceed?" gate,
# which fires after each heap rebuild invalidates the theory hashes.
import Isabelle_RPC_Host.dialogue  # ensure Connection.dialogue exists before override
from Isabelle_RPC_Host.rpc import Connection as _Connection

async def _auto_dialogue(self, question: str, options: list) -> str:
    logger.warning(f"[auto-dialogue] {question!r} -> answering {options[0]!r}")
    return options[0]

_Connection.dialogue = _auto_dialogue  # type: ignore[method-assign]

async def run_tests():
    await run_all_tests(args.repl_addr, logger=logger, sh_timeout=args.sh_timeout)

def run_server():
    Isabelle_RPC_Host.launch_server_(rpc_addr, logger, debugging=True)

test_thread = threading.Thread(target=run_server, daemon=True)
test_thread.start()
time.sleep(1)
asyncio.run(run_tests())
