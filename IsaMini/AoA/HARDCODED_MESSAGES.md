# AoA Hard-Coded Prompts & Error Messages

Comprehensive inventory of all hard-coded user-facing prompts, error messages,
and agent-facing text across the AoA system.

---

## 1. `prompts.py` — Tool Response Messages & Rejection Texts

### Edit Action Responses

| Line | Message |
|------|---------|
| 34 | `"{Verb} nothing."` |
| 36 | `"{Verb} step {id}."` |
| 37 | `"{Verb} step {first}-{last}."` |
| 49–53 | `"Note: {noun} {ids} {were} auto-introduced. You may delete {them} using {TOOL_DELETE} if unhelpful."` |
| 80 | `"All proof goals of {id} are completed."` |
| 82–84 | `"Warnings:\n  - {w}"` |
| 87 | `"Outline:"` |
| 94 | `"Congratulations! All goals are proven."` |
| 107 | `"Deleted {noun} {ids}."` |
| 113 | `"Outline:"` |

### Edit Action Errors

| Line | Message |
|------|---------|
| 131–135 | `"Invalid action: {action}. Must be one of: 'fill', 'insert_before', or 'amend'. Use the '{TOOL_DELETE}' tool to delete steps."` |

### Permission Control — Tool Rejections

| Line | Message |
|------|---------|
| 143 | `"Tool '{tool}' is not allowed."` |
| 148 | `" You should use the '{TOOL_EDIT}' tool to edit proof.yaml."` |
| 151–154 | `" You cannot modify any files except proof.yaml, and you must use the '{TOOL_EDIT}' tool to edit it."` |
| 156–159 | `" You cannot ask the user any questions. You must complete the theorem proof independently."` |
| 161–163 | `" You cannot run any Bash command; proof.yaml contains all the information you need."` |

### Path Access

| Line | Message |
|------|---------|
| 172–175 | `"{tool} operation can only access ./proof.yaml, access denied for: {target_path}"` |

---

## 2. `model.py` — Core Prompts, Errors, and YAML Output

### Session Prompts (system_prompt / initial_prompt / retry_prompt)

| Line | Message |
|------|---------|
| 7792–7808 | **System prompt:** `"You are a formal theorem proving agent.\nA proof goal and an incomplete proof are provided in './proof.yaml' under the current directory.\nAnalyze the proof goal, plan a proof, and complete it using the MCP proof tools.\nContinue until no errors remain.\nBe concise in text output.\n\n## Tools\n- {edit}: Fill, insert, or amend proof steps (your primary tool)\n- {delete}: Delete proof steps\n- {query}: Search for theorems, constants, types, and rules; help you understand unfamiliar terms\n- {recall}: Recall proof state from 'proof.yaml'. Use only when you have lost track."` |
| 7817–7820 | **Initial prompt (with system prompt):** `"Complete the following proof using the MCP proof tools.\n{proof_state}\n'proof.yaml' contains the full proof state, but read it only when you lose track of it."` |
| 7823–7831 | **Initial prompt (without system prompt):** `"An incomplete proof is provided as follows\n{proof_state}\nAnalyze the proof goal, plan a proof, and complete it using tools '{edit}' and '{delete}'.\nContinue building the proof until no error remains.\nExhaust all strategies before giving up. If you conclude the goal is a false statement, or no viable proof path remains, call '{TOOL_SURRENDER}'.\n'proof.yaml' contains the full proof state, but recall it only when you lose track of it."` |
| 7838–7844 | **Retry prompt:** `"Steps {ids} are incomplete. You must call the '{TOOL_EDIT}' tool to complete the steps. Continue building the proof until 'proof.yaml' contains no remaining errors."` or `"The proof is incomplete. ..."` |

### Constants & Hints

| Line | Message |
|------|---------|
| 20–23 | `LONG_GOAL_HINT`: `"note: resulting goal is unusually long, which is often a sign of a wrong direction.\n"` |
| 63–64 | `IsaTerm.__str__` TypeError: `"str() on IsaTerm is ambiguous — use .unicode (for display) or .ascii (for Isabelle RPC) explicitly"` |

### Proof Tree / YAML Output Messages

| Line | Message |
|------|---------|
| 305 | `"- Error: fact \"{name}\" not found"` |
| 307–308 | `"Attempting to pack an unfound fact \"{name}\". Unfound facts should be filtered out before packing."` |
| 460 | `LONG_GOAL_HINT` (see above) |
| 467 | `"Error: Unfinished Proof! Call command 'edit' with action 'fill' and target step '{step}' to replace it with a proof."` |
| 470 | `"Error: Unfinished Proof! Call command 'edit' with action 'fill' and target step '{step}' to provide the proof for the following goal."` |
| 473 | `"Error: Unfinished Proof! Call command 'edit' with action 'fill' and target step '{step}' to provide the proof."` |
| 477 | `"pending proof goal:"` |
| 2325 | `"goal: unknown, evaluation pending"` |
| 2609 | `"Error:"` (followed by evaluation error details) |
| 2615 | `"Error: the evaluation is cancelled due to failures in preceding nodes"` |
| 3749 | `"Error: Evaluation cancelled due to failures above"` |
| 3824 | `"Error: Evaluation pending"` |
| 3831 | `"Error: Unfinished Proof{hint}. Fill step '{step}'"` (shortened quickview form) |
| 3833 | `"Error: Unfinished Proof{hint}. Call command 'edit' with action 'fill' and target step '{step}'"` |
| 4100 | `"goal: unknown, evaluation pending"` |
| 5085 | `"- name: {name} (pending)"` |
| 5087 | `"- proposition: {prop} (pending)"` |
| 5089 | `"- description: {english} (pending)"` |
| 6344 | **Suffices notice:** `"notice: Need to show the provided statement implies the goal"` |
| 7265 | `"You can write global declarations by calling command 'edit' with action 'fill' and target step '{id}.{n+1}'"` |

### CannotEdit Errors

| Line | Message |
|------|---------|
| 548 | `"Cannot fill a node with id {step}"` / `"Cannot fill this step"` |
| 551 | `"Cannot insert before the node {step}"` / `"Cannot insert before this step"` |
| 554 | `"Cannot amend the node {step}"` / `"Cannot amend this step"` |
| 567–571 | `"The proof block is closed."` / `"The proof block is closed. You should edit node {closed_by} instead."` |
| 578 | `"The node is not found."` |
| 585–586 | `"The target already exists. Fill does not overwrite existing successful steps."` |
| 592 | `"It is the root node."` |
| 606–607 | `"You cannot claim the goal is obvious again. You must provide step-by-step proofs."` |

### Other OprError / ArgumentError Messages

| Line | Message |
|------|---------|
| 621 | `"No fact found for the following criteria: {criterions}"` |
| 625 | `"No fact found with name {name}"` |
| 634–635 | `"Syntax error in term '{term}'\n{reason}"` |
| 641 | `"Step with id {id} is not found"` |
| 648 | `"Invalid answer: {reason}"` |
| 660 | `"Cannot rename. The variable {name} is not found"` |
| 665 | `"Cannot rename. The fact {name} is not found"` |
| 673 | `"Cannot delete {id} because the node is not found"` |
| 676 | `"Cannot delete the root node"` |
| 683 | `"Bad Argument\n{reason}"` |
| 687–688 | `"Unknown proof operation {op}. Available operations: {list}"` |
| 703 | `"Operation '{operation}' requires {field(s)} {joined}"` |
| 707 | `"Syntax error in term '{term}'\n{reason}"` |
| 753 | `"{path}: expected an object, got {type}"` |
| 770 | `"{path}: expected an array, got {type}"` |
| 817 | `"Not yet evaluated"` |
| 1043 | `"BUG bad message kind: {data}"` |
| 1318 | `"Bad flat goal data: {data}"` |
| 1349 | `"The beginning state of the execution is not initialized!"` |
| 1365–1367 | `"Expected at most one Goals_Msg per operation, got {n} for {command}"` |

### Interaction Prompts — Interaction_RetrieveForProof

| Line | Message |
|------|---------|
| 2121 | `"You are looking for {title} establishing:"` |
| 2126 | `"Relevant constants in scope:"` |
| 2134 | `"Similar {title} from the library:"` |
| 2137 | `"If an entry above matches what you need, answer with its index."` |
| 2139 | `"Answer with the indices of all matching {title}."` |
| 2140–2143 | `"Otherwise, if none matches but the statement is trivially provable, formalize the statement into Isabelle propositions and answer with them as text. IMPORTANT: all numeric literals MUST be type-annotated, example: '(2::nat)' not '2'."` |
| 2145–2146 | `"If none of the above applies, answer empty to give up the search and prove the statement yourself later."` |
| 2148 | `"If none of the above applies, answer empty to see more candidates."` |
| 2167 | `"No accessible fact found with name '{name}'."` |
| 2080 | `"Please select exactly one entry."` |

### Interaction Prompts — Interaction_InstantiateSchematics

| Line | Message |
|------|---------|
| 2220–2223 | `"The {kind} rule '{name}' has {n} schematic variable(s) that must be instantiated before the rule can be applied."` |
| 2225–2226 | `"Consume premises (they become 'Prem<i>' subgoals, or are discharged by 'using' facts):"` |
| 2231 | `"Schematic variables to instantiate:"` |
| 2236–2238 | `"Answer with 'instantiations', a list of {variable, term} objects. Each term must be a type-correct Isabelle expression."` |
| 2244 | `"This interaction requires 'instantiations' for variables: {names}."` |
| 2250 | `"Variable '{v}' was instantiated twice."` |
| 2256 | `"Missing instantiations for: {names}."` |
| 2268–2269 | `"Unknown schematic {variable(s)}: {joined}. Expected one of: {names}."` |
| 2276 | `"Instantiation rejected by Isabelle:\n{err}"` |

### Interaction Prompts — Interaction_MapCase

| Line | Message |
|------|---------|
| 2316–2318 | `"The {kind} operation produced a case '{actual_case}' (as follows) that does not match any 'case_name' you supplied."` |
| 2325 | `"goal: unknown, evaluation pending"` |
| 2329 | `"Is any of your supplied proof intended for this case?"` |
| 2334–2335 | `"Answer with its index if so, or with empty 'indexes' to leave this case without a proof for now."` |
| 2339–2341 | `"Select one supplied case_name by 'indexes' (at most one), or answer with empty 'indexes' to drop."` |
| 2346 | `"Select at most one supplied case_name."` |

### Interaction Prompts — Interaction_ChooseDef (Unfold)

| Line | Message |
|------|---------|
| 5578 | `"Multiple definitions found for {constant}:"` |
| 5580 | `"Multiple definitions found for constants {names}:"` |
| 5585 | `"Select definitions to use in unfolding. Call '{TOOL_ANSWER}' with 'indexes', or the 'name' of a definition, or leave empty to skip."` |
| 5587 | `"Select this definition to use in unfolding. Call '{TOOL_ANSWER}' with 'indexes', or the 'name' of a definition, or leave empty to skip."` |
| 5604 | `"No accessible fact found with name '{name}'. Select by index."` |

### Interaction Prompts — Interaction_SelectRewriteTargets

| Line | Message |
|------|---------|
| 5847 | `"Rule '{name}' ({pretty}) would cause infinite rewriting."` |
| 5850 | `"To use this rule safely, select which specific subterm(s) to rewrite:"` |
| 5856 | `"No matching subterms found in rewrite targets."` |
| 5858 | `"Answer with the index(es) of the subterm(s) to rewrite, or leave empty to drop this rule."` |

### Interaction — Shared Helpers

| Line | Message |
|------|---------|
| 2065–2066 | `"Select candidate(s) by 'indexes'."` (reject fields hint) |
| 5591–5592 | `"Select a definition by 'indexes' or 'name'."` (reject fields hint) |
| 5863 | `"Select subterm(s) by 'indexes'."` (reject fields hint) |

---

## 3. `mcp_http_server.py` — Tool Logic Errors & Hints

### Permission Check

| Line | Message |
|------|---------|
| 195 | `"No pending interaction."` |
| 200 | `"Tool '{name}' is not allowed in this fork interaction."` |

### Edit Tool Logic

| Line | Message |
|------|---------|
| 229 | `"target_step must be a non-empty string"` |
| 233 | `"action must be a string"` |
| 237 | `"proof_operations must be a non-empty array of proof operations"` |
| 270 | `"Isabelle error: {errors}"` |

### Delete Tool Logic

| Line | Message |
|------|---------|
| 295 | `"target_steps must be a non-empty array"` |
| 303 | `"Error: {noun} {ids} not found."` |
| 311 | `"Warning: {noun} {ids} not found and skipped."` |
| 320 | `"Isabelle error: {errors}"` |

### Answer Tool Logic

| Line | Message |
|------|---------|
| 343 | `"No pending interaction to answer"` |

### Read (Recall) Tool Logic

| Line | Message |
|------|---------|
| 431 | `"proof.yaml path not configured."` |
| 435 | `"proof.yaml not found."` |
| 438–441 | `"The proof contains {n} lines. Provide 'step_id' or 'line number' to read a specific section."` |
| 453–455 | `"Step '{id}' has no line information (proof not yet printed). Read by line number instead."` |
| 466–470 | `"WARNING: Step '{id}' doesn't exist."` (followed by full file dump if small) |
| 473 | `"Step '{id}' doesn't exist. Read the proof by line number instead."` |
| 487 | `"proof.yaml not found."` |

### Surrender Tool Logic

| Line | Message |
|------|---------|
| 517–518 | `"Invalid reason: {reason}. Must be 'stuck' or 'false_statement'."` |
| 522–525 | `"You are a strong prover and you've been doing well. Don't surrender yet — take a step back, rethink your approach, and try again. You may be closer than you think."` |
| 528 | `"Proof attempt abandoned ({reason})."` |

### Tool Descriptions (registered in _TOOL_SCHEMAS)

| Line | Message |
|------|---------|
| 543 | `"Edit the proof.yaml file"` |
| 544 | `"Delete proof steps"` |
| 545 | `"Answer a pending question"` |
| 546–549 | `"Search for Isabelle entities by semantic similarity, patterns, or exact name/term. Use exact_name to look up definitions; use exact_term to unfold fancy syntax and retrieve semantic explanations; use long_description and filters for discovery."` |
| 551 | `"Recall proof state from 'proof.yaml'. Use only when you have lost track."` |
| 552–553 | `"Concede failure and abandon the proof. Use only after all strategies have been exhausted."` |

### Behavioral Hints

| Line | Message |
|------|---------|
| 561–563 | **Search hint:** `"Hint: You've spent a while searching. What you need might not be in the library. Consider shifting focus to writing the proof."` |
| 567 | **Batch cancel:** `"Cancelled: a prior edit/delete in this batch failed. Review the error before continuing."` |

### Fallback Errors

| Line | Message |
|------|---------|
| 621 | `"Unknown tool: {name}"` (ToolExecutor) |
| 696 | `"Unknown tool: {name}"` (MCP call_tool handler) |
| 807 | `"Session not found"` (HTTP 404) |

---

## 4. `driver_api.py` — Compaction & Fork Prompts

| Line | Message |
|------|---------|
| 910–932 | **`COMPACTION_PROMPT`:** `"You have written a partial proof for the initial proof goal.\nPlease summarize your idea and the progress into the following sections.\nThis summary will replace the conversation history above and serve as your only context for continuing the proof — anything not included will be lost.\n\nSummary template:\n## Proof Plan\nYour current proof strategy in detail — the overall approach and how the remaining subgoals fit into it.\n\n## Attempts\nApproaches tried so far: what succeeded, what failed and why. Explicitly note any dead ends that should not be retried.\n\n## Key Insights\nImportant observations about the proof structure, useful lemmas or facts discovered, type information, etc.\n\n## Next Steps\nWhat to do next based on current progress."` |
| 421 | `"OpenAI responses stream ended without response.completed event"` |
| 1151 | `"Compaction summary request failed, continuing without compaction"` |
| 1169 | `"\n\nPrevious progress:\n{summary}"` (appended to initial prompt after compaction) |
| 1213 | `"Let's consider a sub-task forked from the context:\n{prompt}"` |
| 1215 | `"Answer the question above by calling the answer tool."` |
| 1265 | `"Call the answer tool to submit your answer."` |

### Retry / Error Messages

| Line | Message |
|------|---------|
| 970 | `"Working directory {path} is not readable and writable."` |
| 984 | `"_make_fork must be called in a fresh context"` |
| 1029 | `"Quota exhausted, waiting 20min to retry"` |
| 1032 | `"API rate limit, waiting 2s to retry"` |

---

## 5. `driver_openai.py` — Fork Prompts

| Line | Message |
|------|---------|
| 67 | `"The working directory {path} is not readable and writable."` |
| 90–91 | `"_make_fork must be called in a fresh context (use loop.create_task with context=contextvars.copy_context())"` |
| 137 | `"Quota exhausted, waiting 20min to retry"` |
| 139 | `"API rate limit, waiting 2s to retry"` |
| 193 | `"Max turns exceeded in single run segment"` |
| 283–285 | `"Let's consider a sub-task forked from the context:\n{prompt}"` / `"Answer the question above by calling the answer tool."` |
| 318 | `"retrying: interaction not answered"` |
| 319–321 | `"It looks like you haven't submitted your answer. Call the answer tool to submit it."` |

---

## 6. `driver_claude_code.py` — Permission & Fork Messages

### Driver Errors

| Line | Message |
|------|---------|
| 85 | `"Driver 'ClaudeCode' does not accept arguments, but got '{argument}'"` |
| 104 | `"The working directory {path} is not readable and writable."` |
| 136 | `"_make_fork must be called in a fresh context (use loop.create_task with context=contextvars.copy_context())"` |
| 887 | `"Driver 'ClaudeCode_Interactive' does not accept arguments, but got '{argument}'"` |

### Permission Control Hook

| Line | Message |
|------|---------|
| 303 | `"No pending interaction. The answer tool can only be used when there is an active interaction."` |
| 353 | `"Cannot use {tool} on proof.yaml. Use the {TOOL_EDIT} tool instead."` |

### Fork Prompts

| Line | Message |
|------|---------|
| 787–789 | `"Let's consider a sub-task forked from the context:\n{prompt}"` / `"Answer the question above by calling the {answer} tool."` |
| 823–825 | `"It looks like you haven't submitted your answer. Call {TOOL_ANSWER} to submit it."` |

### Retry / Rate Limit

| Line | Message |
|------|---------|
| 215 | `"Usage limit reached, waiting 20min to retry"` |
| 218 | `"API rate limit, waiting 2s to retry"` |

---

## 7. `retrieval.py` — Search Result Messages

### Entity Display

| Line | Message |
|------|---------|
| 152 | `"associated with '{header}'"` (show-once deduplication) |
| 192 | `"[opaque]"` tag on theorem entities without roles |
| 216 | `"where '{lhs}' abbreviates '{rhs}'"` |
| 224 | `"Relevant definitions:"` |
| 249 | `"{names} are also relevant"` |
| 250 | `"{names} are relevant. No new entities found."` |
| 389 | `"No new relevant entities found."` / `"No relevant entities found."` |
| 421–424 | `"\n[opaque] — will not be used automatically unless supplied explicitly."` (show-once) |

### Interaction_RetrieveForSearch Prompt

| Line | Message |
|------|---------|
| 438–439 | `"You are looking for {title} establishing:"` / `"You are looking for {title} matching the search criteria."` |
| 445 | `"Select all relevant {title} from the following list:"` |
| 447–449 | `"You are encouraged to call the query tool to find more if none of the above is relevant."` / `"Answer with the indices of all relevant entries."` |

### Filtering Search

| Line | Message |
|------|---------|
| 482–485 | `"No relevant entities exist. Exhaustive search completed — you MUST consider alternative proof strategies."` (interactive recursive mode) / `"No relevant entities found."` (other modes) |
| 579 | `"No new matching entities found."` |

### Exact Name/Term Query

| Line | Message |
|------|---------|
| 615 | `"The {name} is undefined, but we find:"` |
| 619 | `"Undefined: \"{name}\". Try query."` |
| 644 | `"Failed to parse term: {reason}"` |
| 646 | `"Error: {errors}"` |
| 656 | `"Head {text}"` / `"Head {name}"` |

### Argument Normalization Errors

| Line | Message |
|------|---------|
| 674 | `"Missing required field: {field}"` |
| 679 | `"'{field}' must be a JSON array, got an unparseable string"` |
| 686 | `"'{field}' must be an array, got {type}"` |
| 693 | `"'{field}[{i}]' must be an object, got an unparseable string"` |
| 695 | `"'{field}[{i}]' must be an object, got {type}"` |
| 700 | `"'{field}' must be a non-empty array"` |

---

## 8. `toplevel.py` — Driver Loading Messages

| Line | Message |
|------|---------|
| 26 | `"Unknown driver: {driver}"` |
| 75 | `"Test Not Found on '{argument}'"` |
| 87–88 | `"Unknown retrieval_forking '{str}', falling back to 'with_ctxt'. Known: {sorted_map}"` |
| 94–96 | `"Unknown interactive_retrieval '{str}', falling back to 'no'. Known: {sorted_map}"` |

---

## 9. `web_terminal.py` — UI Text

| Line | Message |
|------|---------|
| 142 | **Read-only toast:** `"proof.yaml is read-only and can only be modified by the agent. If you want to guide the proof, interrupt Claude in the terminal on the left and type your instructions."` |
| 208 | `"[Connection closed]"` |
| 441–442 | `"Proof completed successfully"` / `"Proof incomplete"` |
| 553 | `"# proof.yaml not available yet"` |
| 599 | `"[tmux session '{name}' not found]"` |

---

## Summary

| File | Approx. Count | Categories |
|------|---------------|------------|
| `prompts.py` | ~15 | Tool responses, permission rejections, path access |
| `model.py` | ~75 | System/initial/retry prompts, YAML output, CannotEdit errors, ArgumentErrors, all Interaction prompts |
| `mcp_http_server.py` | ~25 | Tool logic errors, tool descriptions, search/surrender hints, batch cancel |
| `driver_api.py` | ~10 | Compaction prompt, fork prompts, runtime errors |
| `driver_openai.py` | ~8 | Fork prompts, retry messages |
| `driver_claude_code.py` | ~10 | Permission hook rejections, fork prompts, driver errors |
| `retrieval.py` | ~20 | Search result formatting, entity display, argument errors |
| `toplevel.py` | ~4 | Driver loading warnings |
| `web_terminal.py` | ~5 | UI toast, status text |
| **Total** | **~170** | |
