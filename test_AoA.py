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

def run_server():
    # 在线程中运行，继承当前进程的 stdout；任何异常导致主进程退出
    try:
        Isabelle_RPC_Host.launch_server_(rpc_addr, logger, debugging=True)
    except BaseException:
        traceback.print_exc(file=sys.stderr)
        os._exit(1)

server_thread = threading.Thread(target=run_server, daemon=True)
server_thread.start()
# 等待服务端完成绑定
time.sleep(1)
run_all_tests(args.repl_addr)