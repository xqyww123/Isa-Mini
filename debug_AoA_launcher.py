from Isabelle_RPC_Host import launch_server_, mk_logger_
import IsaMini_Agent_AoA

if __name__ == "__main__":
    addr = "127.0.0.1:27180"
    logger = mk_logger_(addr, None)
    launch_server_(addr, logger, debugging=True)