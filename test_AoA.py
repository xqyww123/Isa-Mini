#!/usr/bin/env python3
import argparse
import os
import sys
import threading
import time
import traceback
import Isabelle_RPC_Host
from IsaMini_Agent_AoA.test import run_all_tests

parser = argparse.ArgumentParser(description="Run IsaMini Agent AoA tests")
parser.add_argument(
    "--repl-addr",
    default="127.0.0.1:6666",
    help="REPL server address (host:port), default: 127.0.0.1:6666",
)
args = parser.parse_args()
rpc_addr = "127.0.0.1:27182"
logger = Isabelle_RPC_Host.mk_logger_(rpc_addr, None)

def run_tests():
    # 等待服务端完成绑定
    run_all_tests(args.repl_addr, logger=logger)

def run_server():
    Isabelle_RPC_Host.launch_server_(rpc_addr, logger, debugging=True)

test_thread = threading.Thread(target=run_server, daemon=True)
test_thread.start()
time.sleep(1)
run_tests()