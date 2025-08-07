import importlib.util
import sys
import os

class ProofFail(Exception):
    pass

class ProofChat:
    def run(self, opr):
        raise NotImplementedError("ProofChat.run is not implemented")
    
def proof_chat(name):
    module_name = f"driver_{name}"
    
    # Check if module is already in sys.modules (built-in cache)
    if module_name in sys.modules:
        module = sys.modules[module_name]
    else:
        # Construct the path to the driver module
        driver_path = os.path.join(os.path.dirname(__file__), 'drivers', f"{name}.py")
        
        # Check if the file exists
        if not os.path.exists(driver_path):
            raise FileNotFoundError(f"Driver file not found: {driver_path}")
        
        # Load the module dynamically
        spec = importlib.util.spec_from_file_location(module_name, driver_path)
        if spec is None or spec.loader is None:
            raise ImportError(f"Cannot load module from {driver_path}")
        
        module = importlib.util.module_from_spec(spec)
        # Add to sys.modules before execution to enable proper caching
        sys.modules[module_name] = module
        spec.loader.exec_module(module)
    
    # Check if the module has the required class
    if not hasattr(module, 'Proof_Chat'):
        raise AttributeError(f"Module {driver_path if 'driver_path' in locals() else module_name} does not have a 'Proof_Chat' class")
    
    return module.Proof_Chat


