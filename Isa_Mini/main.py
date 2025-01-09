#!/bin/env python
import argparse
from os import abort

import readline
import rich
from rich.console import Console

import IsaREPL
from Isa_Mini import Mini
import re
import json


parser = argparse.ArgumentParser(
    prog='isa-mini',
    description='The command line REPL of Isabelle/Minilang')
parser.add_argument('--addr', metavar='ADDRESS-OF-SERVER', type=str, help=
"""The address to the server of [Isabelle REPL](https://github.com/xqyww123/Isa-REPL).
Isa-mini will lunch the server it is not yet.
Format : IP-ADDRESS:PORT
Default: 127.0.0.1:6666""")
parser.add_argument('--restart-server', metavar='', type=bool, help=
"""force to restart the Isabelle REPL server.""")
parser.add_argument("file", metavar="FILE:LINE:OFFSET", type=str, help=
"""instruct Isabelle REPL to evaluate FILE until line number LINE, and lunch Minilang at the OFFSET of the LINE.
Example: $Isabelle_AFP/thys/TLA/Rules.thy:58:0""")

args = parser.parse_args()
try:
    file, line, offst = args.file.split(':')
except ValueError:
    print("Invalid format of FILE:LINE:OFFSET")
    abort()

repl = IsaREPL.Client(args.addr, 'HOL')
repl.set_trace(False)

initial_pos = (file, int(line), int(offst))

console = Console()

def CLI_print_state(ret):
    state = Mini.parse_prooftree(ret[2])
    new_items = Mini.parse_item(ret[0])
    rich.print_json(json.dumps(state, indent=2))
    if ret[1]:
        console.print('enter case ' + ret[1], style='bold grey66')
    if ret[0][0] or ret[0][1]:
        console.print('newly introduced: ' + json.dumps(new_items, indent=2), style='bold grey66')


with Mini(repl, initial_pos) as mini:
    CLI_print_state(mini.print()[0])

    while True:
        try:
            s = input('mini> ')
            match s:
                case '\conclude':
                    console.print(mini.conclude())
                    break
                case '\close':
                    mini.close()
                    break
                case str(x) if x.startswith('\move_to '):
                    m = re.match(r'^\\move_to\s+([^:\s]+):(\d+)(:(\d+))?$', x)
                    if m:
                        file = m[1]
                        line = int(m[2])
                        offset = int(m[4] or 0)
                        mini.move_to(file, line, offset)
                        CLI_print_state(mini.print()[0])
                    else:
                        console.print('Bad Syntax, \move_to <file>:<line>:[offset]', style='bold red')
                case _:
                    rets = mini.eval(s)
                    for ret in rets:
                        CLI_print_state(ret)
        except KeyboardInterrupt:
            break
        except EOFError:
            break
        #except Exception as e:
        #    console.print(e, style='bold red')
