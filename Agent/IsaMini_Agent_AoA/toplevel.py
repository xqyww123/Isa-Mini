from re import I
from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from .model import Goals, Root, Minilang_Operation, unpack_MLPT, InferenceRule, Obtain, Obvious, Have
import sys

@isabelle_remote_procedure("IsaMini.AoA")
def IsaMini_AoA(data, connection: Connection):
    (goals, ptree) = data
    goals = Goals.unpack(goals)
    ptree = unpack_MLPT(ptree)
    root = Root.new((goals, ptree), connection)
    # Do the Agent proof here
    # You can use `root.locate_node(id)` to locate a node by its id
    # then call target_node.insert_before(gen_node) to insert a new node before the target node
    # or target_node.append(gen_node) to append a new node after the target node
    # In this way you edit the abstract proof tree
    # until the root.is_proof_finished() is True
    # then you can claim the proof is constructed successfully
    #
    # Some example code is provided here for testing, but it should be replaced with the interaction with LLMs
    
    def print_header(msg: str):
        print("-"*50)
        print(msg)
        print("-"*50)
    print_header("Initial YAML")
    root.print(0, sys.stdout)
    #goal = root.locate_node("goal1") # the same as root.sub_nodes[1]
    goal = root.sub_nodes[1]
    goal.append(InferenceRule.gen({"thought": "Proof by contradiction", "rule": None}))
    print_header("Setting the inference rule")
    root.print(0, sys.stdout)
    goal.append(Obtain.gen({"thought": "I don't know", "variables": [{"name": "m", "type": "nat"}, {"name": "n", "type": "nat"}],
            "constraints": [{"isabelle": "¦sqrt 2¦ = m / n", "english": "some fancy explanation"}]}))
    print_header("Obtain m n")
    root.print(0, sys.stdout)
    #node = root.locate_node("2.1") # not appear
    root.fill("2.1", Obvious.gen({"thought": "Oviously the statement holds.", "facts": []}))
    print_header("Obvious")
    root.print(0, sys.stdout)
    root.fill("3", Have.gen({"thought": "I don't know", "statement": {"english": "some fancy explanation", "isabelle": "m^2 = (sqrt 2)^2 * n^2"}}))
    root.fill("3.1", Obvious.gen({"thought": "Oviously the statement holds.", "facts": []}))
    print_header("Have")
    root.print(0, sys.stdout)
    # omit ...
    connection.write((0, None))
    if root.is_proof_finished():
        return ([x.pack() for x in root.assemble()], root.final_ml_state.name)
    else:
        return ([x.pack() for x in root.assemble()], None)
    # Finally, we return the constructed proof



