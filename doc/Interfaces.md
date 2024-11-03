
This shell is based on the standard Input and Output pipeline (`stdin, stdout`).
It uses text to communicate. A request (response) is a line and multiple requests (response) are separated by line break (any line break in terms, proposition expressions must be removed).

A request has the following format,
```
@chan COMMAND-NAME   COMMAND-ARGUMENTS   <linebreak, CR, LF, or CRLF>
```
where `@chan` denotes *Channel ID* which is a natural number.

A response is a single-line JSON.
```js
{
"CHANNEL": @chan
"RESPONSE": ... //ad-hoc for each command, given in the later tables
"ERR": "..." // a string. The RESPONSE is meaningful only when this error string is empty.
}
```

Commands and supported features are categorized and discussed as follows.

##### Notation
In any syntax definition presented in this document, variables are leaded by `@`. Any other word not leaded by `@` is a plan literal that must be included as it is in the requests sent to our shell.

For example, an instance of `@chan GOAL \<open> @expr \<close>` is `42 GOAL \<open> 1 + 1 = 2 \<close>`. The `\<open>` and `\<close>` are literals must be given in the request text.

#### Concurrency & Multiplex

The shell supports multiplex. Clients can open multiple concurrent channels while the processing in each channel is sequential (first requested, first served). 

| COMMAND & SYNTAX        | RESPONSE   | DESCRIPTION                                                                                 |
| ----------------------- | ---------- | ------------------------------------------------------------------------------------------- |
| `@chan NEW_CHANNEL`     | `{ID: ID}` | create a new channel, returning the ID of the new channel. Argument `@chan` is meaningless. |
| `@chan RELEASE_CHANNEL` | null       | Kill and release the channel `@chan`.                                                       |

Processing between channels is parallel. However, we cannot guarantee a channel to use only one thread. Some Isabelle tactic can use multiple threads. Luckily, Isabelle has its own thread scheduling. Thus, it is safe to open as many channels as your CPU cores.
#### Proof Goal Management

Many commands have a common response format, defined as follows
```js
GOAL ::=
{
	"conclusion": "@conclusion",
	"hypotheses": [{"@name1": "@hypothesis1"}, {"@name2": "@hypothesis2"}, ...],
	"variables": [
		{"name": @name1, "type": @type1},
		{"name": @name2, "type": @type2},
		...
	] //locally fixed variables
}
PROOF_STATE ::=
{
	"current_goal": GOAL or null, // the current subgoal to which tactics are applied
		// if the current subgoal is solved, @current_goal.@conclusion will be null
	"subgoals": [GOAL, ...] // all subgoals pending to handle
		// if a tactic splits @current_goal into several smaller subgoals [G1,G2,G3,...],
		// the first subgoal G1 will replace the @current_goal and the remaining
		// subgoals [G2,G3,...] will be prepended to @subgoals, resulting
		// [G2,G3,...] + @subgoals.
		// Thus, clients can trace the change of @subgoals to know what are the new generated
		// subgoals.
}
```

Essentially, each channel in this shell is a state machine, `PROOF_STATE` is the state of the state machine, and commands are its transition rules.

| COMMAND & SYNTAX                    | RESPONSE    | DESCRIPTION                                                                                                    |
| ----------------------------------- | ----------- | -------------------------------------------------------------------------------------------------------------- |
| `@chan GOAL \<open> @expr \<close>` | PROOF_STATE | Initiate a fresh proof environment, setting `@expr` as the goal. Any previous proof environments will be lost. |
| `@chan apply ( @tactic )`           | PROOF_STATE | apply a tactic. Any tactic is applied only to @the_current_subgoal                                             |
| `@chan NEXT`                        | PROOF_STATE | turn to the first subgoal in @subgoals, if the @current_goal is `null`                                         |
| `@chan PRINT_MODE @mode`            | null        | set how do we print term expressions, see $\S$ Print Mode.                                                     |
#### Print Mode

There are different ways to print a term expression into a string. `PRINT_MODE` affects all the output of terms in the channel.
- `@mode = 1` uses pretty printer, i.e., the output will be the same as what you can see in Isabelle's GUI
- `@mode = 2` prints s-expression with full names (every constant will be printed in long-identifier format, `Theory_Name.Constant_Name`). This allows one to overcome syntax overloading and reconstruct the internal terms. Lambda variable is represented by de-Bruijn index, in format `_123`, (the index number leaded by an underscore). Lambda expression $\lambda(x:\tau). t$ will be printed as (`\<lambda>` $\tau$ $t$). Lambda application $f\,a\,b\,c$ will be `(f a b c)`

Message me if you want more printing format.

### Proof Tactics that All you Need

Even when Isabelle provides tens of various tactics, the really useful tactics that an AI agent should use are very minimal. The following commands provide common combinations of these tactics.

--------

**COMMAND & SYNTAX:**   `@chan SIMP @rules` <br />
**RESPONSE:**  PROOF_STATE <br />
**DSCRIPTION:** Apply Isabelle tactic `auto` with a configurable simplification set to simplify the `@current_goal` with using all contextual hypotheses. It can split the goal into several smaller goals that are easier to handle. Basically, this command is the first thing one needs to apply.

This tactic is powerful and involves Presburger solver. The tactic can be non-terminating. Thus we set a configurable timeout (by default, 10 seconds). If it timeouts, we instead use a weaker tactic `clarsimp`. If it still timeouts, the command fails with error message "timeout". If the tactics cannot simplify the `@current_goal` even a bit, the commands fails with error message "fail".

`@rules` is an optional list of simplification rules should be additionally used.

-----------

**COMMAND & SYNTAX:**   `@chan have @name \<open> @expr \<close>` <br />
**RESPONSE:**  PROOF_STATE <br />
**DSCRIPTION:** Ask the shell to suspend the `@current_goal` (by pushing `@current_goal` into `@subgoals`), and turn to first prove a subgoal `@expr` within the hypothesis context of `@current_goal`. This subgoal `@expr` will be added as a hypothesis of later subgoals (that sharing the same hypothesis context).

Given proof state
```js
{
	"current_goal": {
		"conclusion": "@conclusion",
		"hypotheses": @hypotheses,
		"variables": @variables
	} // denote this as @G0,
	"subgoals": [@G1,@G2,...]
}
```
by applying this command, the shell transfers its state to
```js
{
	"current_goal": {
		"conclusion": "@expr",
		"hypotheses": @hypotheses,
		"variables": @variables
	},
	"subgoals": [
		@G0,
		@G1.hypotheses.prepend(@expr), // if G1.hypotheses = @G0.hypotheses and G1.variables = @G0.variables
		@G2.hypotheses.prepend(@expr), // if G2.hypotheses = @G0.hypotheses and G2.variables = @G0.variables
		...]
}
```
--------------------
**COMMAND & SYNTAX:**   `@chan obtain @varnames where @name : \<open> @condition \<close>` <br />
This `obtain` command has the same syntax with Isabelle's `obtain` commands, except attributes. <br />
**RESPONSE:**  PROOF_STATE <br />
**DESCRIPTION:** It has the same semantics with Isabelle's `obtain` command. In terms of the shell's state machine, it behaviors similarly to the `have` command, except that the `@expr`  in `have` is $\exists\texttt{varnames}.\;\texttt{condition}$.

Given proof state
```js
{
	"current_goal": {
		"conclusion": "@conclusion",
		"hypotheses": @hypotheses,
		"variables": @variables
	} // denote this as @G0,
	"subgoals": [@G1,@G2,...]
}
```
by applying this command, the shell transfers its state to
```js
{
	"current_goal": {
		"conclusion": "∃varnames. condition",
		"hypotheses": @hypotheses,
		"variables": @variables
	},
	"subgoals": [
		@G0,
		@G1{hypotheses.prepend(@condition), variables.prepend(@varnames)},
				// if G1.hypotheses = @G0.hypotheses and G1.variables = @G0.variables
		@G2{hypotheses.prepend(@condition), variables.prepend(@varnames)},
				// if G2.hypotheses = @G0.hypotheses and G2.variables = @G0.variables
		...]
}
```
------------
**COMMAND & SYNTAX:**   `@chan SLEDGEHAMMER @timeout` <br />
**RESPONSE:**  PROOF_STATE <br />
**DSCRIPTION:** If the AI agent believes the `@current_goal` is simple enough, call this command to invoke Sledgehammer to finalize the proof for this `@current_goal`. Sledgehammer terminates only when it successfully solves the goal. Thus `@timeout` is used to indicate when should the shell give up and respond with error message "timeout". Note, Sledgehammer is generally slow, the recommended timeout is 30 seconds.

----------------
**COMMAND & SYNTAX:**   `@chan fastforce @timeout` <br />
**RESPONSE:**  PROOF_STATE <br />
**DSCRIPTION:** Another finalizing tactic `fastforce` that terminates only when the `@current_goal` is solved. `fastforce` is powerless than Sledgehammer but faster. The recommended timeout is 3 seconds.

-----------------------
Above, we described all the commonly used automatic tactics. The tactics above should be enough for the most situations. However, sometimes, manual proof is still required. Here the shell provides three commands that cover all kinds of manual proofs --- applying introduction and elimination rules, in a resolution manner, and applying unfolding.

**COMMAND & SYNTAX:**   `@chan INTRO_RULE @rule` <br />
**RESPONSE:**  PROOF_STATE <br />
**DSCRIPTION:** Applying the introduction rule `@rule` to the `@current_goal`. Multiple new subgoals can be introduced as the consequence. The `@rule` is the name of the rule. To parse the name, we first check local context (the named hypotheses in the proof environment) and then the Isabelle system.

**COMMAND & SYNTAX:**   `@chan ELIM_RULE @rule` <br />
**RESPONSE:**  PROOF_STATE <br />
**DSCRIPTION:** Applying the elimination rule `@rule` to the `@current_goal`.

Note, introduction rules and elimination rules have the same format. Therefore, the shell cannot distinguish between them just from their propositions. Conventionally, the names of introduction rules in Isabelle are suffixed by `_intro`, while the names of elimination rules are by `_elim`.

**COMMAND & SYNTAX:**   `@chan UNFOLD @rule` <br />
**RESPONSE:**  PROOF_STATE <br />
**DSCRIPTION:** Apply the rewrite rule `@rule` to every occurrence of the redex of the rule. `@rule` must be an HOL equation. Otherwise, the shell responds with error message "bad rule: not an equation".

**Note.** Attributes are allowed in `@rule`, e.g., `exI[where x=1]`, though it is generally an advanced feature.

### Lemmas Retrieval

TODO.

I can implement interfaces for Isabelle's pattern-based theorem look-up mechanism, though I think the proper way to do this is semantic retrieval by some embedding model.
