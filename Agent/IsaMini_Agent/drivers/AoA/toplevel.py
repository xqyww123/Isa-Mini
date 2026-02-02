from Isabelle_RPC_Host import isabelle_remote_procedure, Connection
from model import Goals, Root

@isabelle_remote_procedure("IsaMini.AoA")
def IsaMini_AoA(goals, connection: Connection):
    goals = Goals.unpack(goals)
    root = Root(goals)
    connection.write((0, None))
    return connection.read()



