# CLAUDE.md

## Rules

Never delete golden YAML in test cases. You may edit the YAML manually to update it if you are absolutely certain.

test_AoA.py produces large output! Always redirect output to a file!

The `line` argument of `@model_test(name, file, line)` MUST point to the `by aoa` line in the fixture `.thy` — NOT the `lemma` line. A wrong line leaves the REPL stopped before `by aoa`, so `run_app` hangs indefinitely (looks like `load_theory` is stuck). Run `test_AoA.py` with `python -u` so the "Running test" progress line isn't hidden by stdout buffering.
