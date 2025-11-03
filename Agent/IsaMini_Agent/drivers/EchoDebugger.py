import os
import driver
from google import genai
from google.genai import types
import os
import json

ECHO = [("OBTAIN", {'variables': ['k'], 'conditions': ['k > 0']})]
#ECHO = [("SIMPLIFY", {}), ("END", {})]
#ECHO = [
#    ("BRANCH", {'cases': ['a mod 3 = 0', 'a mod 3 = 1', 'a mod 3 = 2']}),
#    ("ATP", {}),
#    ("SIMPLIFY", {}),
#    ("ATP", {}),
#    ("SIMPLIFY", {}),
#    ("ATP", {}),
#    ("SIMPLIFY", {}),
#    ("ATP", {})
#]

class Proof_Chat(driver.ProofChat):
    def __init__(self, initial_state_printing):
        pass

    def run(self, opr):
        for cmd, arg in ECHO:
            opr(cmd, arg)