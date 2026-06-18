# CLAUDE.md

## Rules

Never delete golden YAML in test cases. You may edit the YAML manually to update it if you are absolutely certain.

This is a shared working tree, so a commit may sweep in uncommitted changes other agents made to the same files. That is acceptable — but the commit message MUST clearly and fully describe any included work that is not part of your own change, so nothing rides along undocumented under a message that only mentions yours.

Whenever you modify any Isabelle/ML (`.ML`) source (e.g. `library/proof.ML`, `Agent/agent_server.ML`), you MUST ask the user to restart the REPL server to load the changes. A running session keeps the old compiled ML; editing the source alone does NOT reload it, so tests will run against stale ML until the server is restarted.

test_AoA.py produces large output! Always redirect output to a file!

The `line` argument of `@model_test(name, file, line)` MUST point to the `by aoa` line in the fixture `.thy` — NOT the `lemma` line. A wrong line leaves the REPL stopped before `by aoa`, so `run_app` hangs indefinitely (looks like `load_theory` is stuck). Run `test_AoA.py` with `python -u` so the "Running test" progress line isn't hidden by stdout buffering.
