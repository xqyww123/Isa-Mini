# IsaMini Agent AoA (All over Abstraction)

The Agent AoA (All over Abstraction) is a framework for using AI agents to construct Isabelle proofs interactively. It provides a structured approach where agents can fill in proof steps using various proof operations.

## Features

- **Interactive Proof Construction**: AI agents can incrementally build proofs by filling steps in a proof tree

## Usage

In Isabelle, use `by aoa` to invoke the agent.

### Configuration Options

- **`agent_aoa_driver`**: AI driver to use (default: `"ClaudeCode"`)
  ```isabelle
  declare [[agent_aoa_driver = "ClaudeCode"]]
  ```

- **`AoA_log_dir`**: Log directory path. Set to `""` to disable logging.
  - Default: `$ISABELLE_HOME_USER/log/AoA` (or `""` if `$ISABELLE_HOME_USER` is unset)
  - Environment variable `AoA_LOG_DIR` overrides this configuration
  ```isabelle
  declare [[AoA_log_dir = "/path/to/logs"]]
  ```

### Logging

The AoA system supports comprehensive logging of:
- **Model Interactions** (`interaction.yaml`): LM outputs, thinking, tool calls, responses, retries
- **Proof Tree Snapshots** (`proofs.yaml`): Snapshots of the proof tree after operations
- **Proof Operations** (`proof_oprs.yaml`): Detailed proof operation records, including errors

Logs are stored in `<AoA_log_dir>/<invocation_id>/`.

## Architecture

```
toplevel.py           - RPC entry point, session management
model.py              - Core data structures: Root, Node, Session
driver_claude_code.py - ClaudeCode driver implementation
prompts.py            - Prompt templates for LLM interaction
helper.py             - Utility functions
test.py               - Test framework
```
