#!/usr/bin/env python3
import argparse
import os
import sys
import threading
import time
import traceback
import asyncio
import Isabelle_RPC_Host
from IsaMini_Agent_AoA.test import run_all_tests

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
args = parser.parse_args()
if args.filter is not None:
    os.environ["TEST_FILTER"] = args.filter
rpc_addr = "127.0.0.1:27182"
logger = Isabelle_RPC_Host.mk_logger_(rpc_addr, None)

async def run_tests():
    await run_all_tests(args.repl_addr, logger=logger)

def run_server():
    Isabelle_RPC_Host.launch_server_(rpc_addr, logger, debugging=True)

test_thread = threading.Thread(target=run_server, daemon=True)
test_thread.start()
time.sleep(1)
asyncio.run(run_tests())
