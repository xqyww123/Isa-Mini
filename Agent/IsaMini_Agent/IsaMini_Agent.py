import msgpack as mp
import IsaREPL as REPL
import socket
import threading
import logging

from google import genai
from google.genai import types

class Agent:
    VERSION = '0.1.0'
    def __init__(self, socket):
        """
        @param socket: the socket towards Isabelle MiniLang Agent.
        """
        self.sock = socket
        self.cout = self.sock.makefile('wb')
        self.cin = self.sock.makefile('rb', buffering=0)
        self.unpack = mp.Unpacker(self.cin)

        mp.pack(Agent.VERSION, self.cout)
        self.cout.flush()



class Manager:
    def __init__(self, addr):
        """
        Initialize the TCP server manager.
        
        Args:
            addr: String in format "host:port" for the server to bind to
        """
        self.host, port_str = addr.split(':')
        self.port = int(port_str)
        self.socket = None
        self.running = False
        self.clients = []
        self.logger = logging.getLogger(__name__)
        
    def start_server(self):
        """Start the TCP server and begin accepting connections."""
        try:
            self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.socket.bind((self.host, self.port))
            self.socket.listen(5)
            self.running = True
            
            self.logger.info(f"TCP Server started on {self.host}:{self.port}")
            
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
            
    def handle_client(self, client_socket, client_addr):
        """Handle individual client connections."""
        self.clients.append(client_socket)
        
        try:
            while self.running:
                # Receive data from client
                data = client_socket.recv(4096)
                if not data:
                    break
                    
                try:
                    # Unpack msgpack data
                    message = mp.unpackb(data, raw=False)
                    self.logger.info(f"Received from {client_addr}: {message}")
                    
                    # Process the message
                    response = self.process_message(message)
                    
                    # Send response back to client
                    if response:
                        packed_response = mp.packb(response)
                        client_socket.send(packed_response)
                        
                except mp.exceptions.ExtraData:
                    self.logger.error("Invalid msgpack data received")
                except Exception as e:
                    self.logger.error(f"Error processing message: {e}")
                    
        except Exception as e:
            self.logger.error(f"Error handling client {client_addr}: {e}")
        finally:
            self.clients.remove(client_socket)
            client_socket.close()
            self.logger.info(f"Client {client_addr} disconnected")
            
    def process_message(self, message):
        """
        Process incoming messages and return appropriate responses.
        
        Args:
            message: Unpacked message from client
            
        Returns:
            Response to send back to client
        """
        # Basic message processing - can be extended based on requirements
        if isinstance(message, dict):
            command = message.get('command')
            
            if command == 'ping':
                return {'status': 'pong', 'version': Agent.VERSION}
            elif command == 'info':
                return {
                    'status': 'ok',
                    'server_info': {
                        'version': Agent.VERSION,
                        'host': self.host,
                        'port': self.port,
                        'connected_clients': len(self.clients)
                    }
                }
            elif command == 'repl':
                # Handle REPL commands if needed
                repl_command = message.get('data')
                if repl_command:
                    # Process with IsaREPL - this would need to be implemented
                    # based on your IsaREPL module's interface
                    return {'status': 'repl_response', 'data': f"Processed: {repl_command}"}
            else:
                return {'status': 'error', 'message': f'Unknown command: {command}'}
        else:
            return {'status': 'error', 'message': 'Invalid message format'}
            
    def broadcast_message(self, message):
        """Broadcast a message to all connected clients."""
        packed_message = mp.packb(message)
        disconnected_clients = []
        
        for client in self.clients:
            try:
                client.send(packed_message)
            except socket.error:
                disconnected_clients.append(client)
                
        # Remove disconnected clients
        for client in disconnected_clients:
            if client in self.clients:
                self.clients.remove(client)
                client.close()
                
    def stop_server(self):
        """Stop the TCP server and close all connections."""
        self.running = False
        
        # Close all client connections
        for client in self.clients:
            client.close()
        self.clients.clear()
        
        # Close server socket
        if self.socket:
            self.socket.close()
            
        self.logger.info("TCP Server stopped")

# Example usage
if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    
    # Create and start the server
    server = Manager('localhost:8080')
    
    try:
        server.start_server()
    except KeyboardInterrupt:
        print("\nShutting down server...")
        server.stop_server()