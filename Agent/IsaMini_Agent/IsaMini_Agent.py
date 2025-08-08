import msgpack as mp
import IsaREPL as REPL
import socket
import threading
import logging
import os
#from . import driver
import driver
import sys

class ColorFormatter(logging.Formatter):
    COLORS = {
        'DEBUG': '\033[94m',    # Blue
        'INFO': '\033[92m',     # Green
        'WARNING': '\033[93m',  # Yellow
        'ERROR': '\033[91m',    # Red
        'CRITICAL': '\033[95m', # Magenta
    }
    RESET = '\033[0m'

    def format(self, record):
        color = self.COLORS.get(record.levelname, self.RESET)
        message = super().format(record)
        return f"{color}{message}{self.RESET}"

class Agent:
    class Cancel(Exception):
        pass

    API_VERSION = '0.1'

    def __init__(self, socket, logger=None):
        """
        @param socket: the socket towards Isabelle MiniLang Agent.
        """
        self.logger = logger
        self.sock = socket
        self.cout = self.sock.makefile('wb')
        self.cin = self.sock.makefile('rb', buffering=0)
        self.unpack = mp.Unpacker(self.cin)

        mp.pack(Agent.API_VERSION, self.cout)
        self.cout.flush()
        driver_name, banner = REPL.Client._parse_control_(self.unpack.unpack())
        banner = REPL.Client.pretty_unicode(banner)
        if self.logger:
            self.logger.debug(f"Driver: {driver_name}, Banner:\n{banner}")

        if driver_name == '':
            driver_name = 'Gemini'
        self.driver = driver.proof_chat(driver_name)(banner)
    
    def run(self):
        def ascii(s):
            if s is None:
                return None
            else:
                return REPL.Client.ascii_of_unicode(s)
        def ascii_lst(lst):
            return [REPL.Client.ascii_of_unicode(item) for item in lst]
        def pack(name, args):
            match name:
                case 'ATP':
                    return ascii_lst(args.get('lemmas', []))
                case 'RETRIEVE':
                    return (ascii_lst(args.get('patterns', [])), ascii_lst(args.get('negative patterns', [])), args.get('names', []))
                case 'SIMPLIFY':
                    return ascii_lst(args.get('rules', []))
                case 'UNFOLD':
                    return ascii_lst(args.get('targets', []))
                case 'WITNESS':
                    return ascii_lst(args.get('witnesses', []))
                case 'RULE':
                    return ascii_lst(args.get('rule', None) or [])
                case 'CASE_SPLIT':
                    return (ascii(args.get('target', '')), ascii(args.get('rule', None)))
                case 'INDUCT':
                    return (ascii(args.get('target', '')), ascii_lst(args.get('arbitrary', [])), ascii(args.get('rule', None)))
                case 'BRANCH':
                    return ascii_lst(args.get('cases', []))
                case 'HAVE':
                    return ascii_lst(args.get('subgoals', []))
                case 'OBTAIN':
                    return (ascii_lst(args.get('variables', [])), ascii_lst(args.get('conditions', [])))
                case 'ROLLBACK':
                    return args.get('step', 0)
                case _:
                    raise Exception(f"Unknown operation: {name}")
        def opr(name, args):
            if self.logger:
                self.logger.debug(f"Call {name}:\n{args}")
            mp.pack((name, pack(name, args)), self.cout)
            self.cout.flush()
            try:
                state, response = REPL.Client._parse_control_(self.unpack.unpack())
                response = REPL.Client.pretty_unicode(response)
                if state == 2:
                    raise Agent.Cancel
                is_proved = state == 1
            except REPL.REPLFail as e:
                is_proved = False
                response = 'Operation failed.\n\n' + str(e)
            if self.logger:
                self.logger.debug(f"Response:\n{response}")
            return is_proved, response
        self.driver.run(opr)


class Manager:
    def __init__(self, addr, log_file=None):
        """
        Initialize the TCP server manager.
        
        Args:
            addr: String in format "host:port" for the server to bind to
            log_file: Optional path to log file. If provided, logs will be written to this file.
        """
        self.host, port_str = addr.split(':')
        self.port = int(port_str)
        self.socket = None
        self.running = False
        self.clients = {}
        self.log_file = log_file
        
        # Configure logging
        self.logger = logging.getLogger(__name__)
        self.logger.propagate = False  # Prevent duplicate logging to root logger
        if log_file:
            file_handler = logging.FileHandler(log_file)
            #file_handler.setLevel(logging.DEBUG)
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            file_handler.setFormatter(formatter)
            
            # Add handler to logger
            self.logger.addHandler(file_handler)
        else:
            stream_handler = logging.StreamHandler(sys.stderr)
            #stream_handler.setLevel(logging.DEBUG)
            color_formatter = ColorFormatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
            stream_handler.setFormatter(color_formatter)
            self.logger.addHandler(stream_handler)
        self.logger.setLevel(logging.DEBUG)
        
    def handle_client(self, client_socket, client_addr):
        """Handle a client connection."""
        try:
            agent = Agent(client_socket, self.logger)
            self.clients[client_addr] = agent
            agent.run()
        except Exception as e:
            self.logger.error(f"Error handling client: {e}")
        finally:
            try:
                client_socket.close()
            except:
                pass
            if client_addr in self.clients:
                del self.clients[client_addr]
                
    def stop_server(self):
        """Stop the TCP server."""
        self.running = False
        if self.socket:
            try:
                self.socket.close()
            except:
                pass
        self.logger.info("Server stopped")
        
    def start_server(self):
        """Start the TCP server and begin accepting connections."""
        try:
            self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.socket.bind((self.host, self.port))
            self.socket.listen(5)
            self.running = True
            
            self.logger.info(f"TCP Server started on {self.host}:{self.port}")
            print('OK')
            
            while self.running:
                try:
                    client_socket, client_addr = self.socket.accept()
                    self.logger.debug(f"New client connected from {client_addr}")
                    
                    # Handle each client in a separate thread
                    client_thread = threading.Thread(
                        target=self.handle_client,
                        args=(client_socket, client_addr)
                    )
                    client_thread.daemon = True
                    client_thread.start()
                    
                except socket.error as e:
                    if self.running:
                        self.logger.error(f"Socket error: {e}")
                        
        except Exception as e:
            self.logger.error(f"Failed to start server: {e}")

# Example usage
if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    import sys

    if len(sys.argv) > 1:
        addr = sys.argv[1]
    else:
        addr = 'localhost:2357'
    
    # Check for log file argument
    log_file = None
    if len(sys.argv) > 2:
        log_file = sys.argv[2]

    # Create and start the server
    server = Manager(addr, log_file)
    
    try:
        server.start_server()
    except KeyboardInterrupt:
        print("\nShutting down server...")
        server.stop_server()