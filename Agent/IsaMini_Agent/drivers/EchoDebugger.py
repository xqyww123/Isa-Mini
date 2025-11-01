import os
import driver
from google import genai
from google.genai import types
import os
import json

ECHO = [("SIMPLIFY", {}), ("END", {})]

class Proof_Chat(driver.ProofChat):
    def __init__(self, initial_state_printing):
        pass

    def run(self, opr):
        for cmd, arg in ECHO:
            opr(cmd, arg)