
### Instructions to test and evaluate the agent

There are multiple methods.

#### Setup (Necessary before all the following methods)

```
# assume the current working directory is at the MLML directory.
./init.sh # if you haven't run it before
source envir.sh
cd contrib/Isa-REPL
python3 -m build
pip install dist/isarepl-<<THE LATEST VERSION>>-py3-none-any.whl --force-reinstall
```

#### Evaluating the agent over a single proof goal (Easies way)

1. Launch the Isabelle REPL server
```
# assume the current working directory is at the MLML directory.
source envir.sh
cd contrib/Isa-REPL
./repl_server.sh 0.0.0.0:6666 HOL-Library /tmp/repl_outputs -o threads=<<NUMBER OF CPU COREs>> -o document=false
```

2. Launch the Agent Server
Launch VS Code or Cursor, open the folder [./contrib/Isa-Mini](.).
Click `Run Python Debugger Using Launch Config`, then select `AoA Agent`.

For more information, see [../.vscode/launch.json](../.vscode/launch.json).

The entry point is [./debug_launcher.py](./debug_launcher.py) and [./IsaMini_AoA/toplevel.py](./IsaMini_AoA/toplevel.py).

3. Run the agent over a proof goal
```
# assume the current working directory is at the MLML directory.
./tools/agent_run.py <<File:line:column>>

# examples:
./tools/agent_run.py ./contrib/Isa-Mini/Agent/Test/Test001.thy:6:1
./tools/agent_run.py ./contrib/Isa-Mini/Agent/Test/Test_sqrt2.thy:6:1
```
You can see logs from the Agent Server's stdout.

### Notes

- HAMMER now has feedback
