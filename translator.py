#!/bin/env python

USAGE = """
translator.py <ADDRESS OF SERVER>
              <PATH TO THE DATABASE>
              <PATH TO TARGETS>

Evaluate an entire theory file.

PATH TO TARGETS is the path to a file listing the paths of all the targets to be translated.
    Such a list file can be generated by the following command.
        find ~+ -type f -name "*.thy"
    For a test usage, this list can be very long, you may use the following command to
    randomly select some of them.
        find ~+ -type f -name "*.thy" | shuf -n 100 > targets.lst

Example

./examples/eval_file.py 127.0.0.1:6666 $(isabelle getenv -b ISABELLE_HOME)/src/HOL/List.thy



"""

from IsaREPL import Client
from sqlitedict import SqliteDict
import msgpack as mp
import sys

if len(sys.argv) != 4:
    print(USAGE)
    exit(1)

addr = sys.argv[1]

targets = []
with open(sys.argv[3]) as file:
    targets = [line.rstrip() for line in file]

c = Client(addr, 'HOL')
c.set_register_thy (False)
c.set_trace (False)
c.load_theory(['Minilang_Translator.MS_Translator_Top'])
c.run_ML ("Minilang_Translator.MS_Translator_Top",
"""
ML_Translator_Top.init_translator (Path.explode "/tmp/xxx") (ML_Translator_Top.interactive_reporter());
REPL_Server.register_app "Minilang-Translator" ML_Translator_Top.REPL_App
""")

def encode_pos (pos):
    return f'{pos[3][1]}#{pos[0]}'

with SqliteDict(sys.argv[2]) as db:
    def interact():
        while True:
            match c.unpack.unpack ():
                case (0, pos):
                    pos = encode_pos(pos)
                    run = False
                    try:
                        run = not db[pos][0]
                    except KeyError:
                        run = True
                    mp.pack (run, c.cout)
                    c.cout.flush ()
                case (1, pos, err):
                    print(f"line {pos[0]} fails")
                    print(err)
                    pos = encode_pos (pos)
                    db[pos] = (False,err)
                    db.commit()
                case (2, pos, ret):
                    print(f"line {pos[0]} succeeds")
                    print(ret)
                    pos = encode_pos (pos)
                    db[pos] = (True, ret)
                    db.commit()
                case 3:
                    break
                case X:
                    print (X)
                    raise Exception ("BUG")

    for path in targets:
        c.run_app ("Minilang-Translator")
        print (f"translating {path}")
        mp.pack (path, c.cout)
        c.cout.flush ()
        interact ()

