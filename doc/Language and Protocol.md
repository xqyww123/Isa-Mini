Language and Protocol
=====

This document defines the language and the communication protocol of our Proof Shell.

## The Proof Shell Language: An Example

Take the proof for "the square root of two is irrational" given in [the Wikipedia page of Isabelle](https://en.wikipedia.org/wiki/Isabelle_(proof_assistant))
```isabelle
theorem sqrt2_not_rational:
  "sqrt 2 ∉ ℚ"
proof
  let ?x = "sqrt 2"
  assume "?x ∈ ℚ"
  then obtain m n :: nat where
    sqrt_rat: "¦?x¦ = m / n" and lowest_terms: "coprime m n"
    by (rule Rats_abs_nat_div_natE)
  hence "m^2 = ?x^2 * n^2" by (auto simp add: power2_eq_square)
  hence eq: "m^2 = 2 * n^2" using of_nat_eq_iff power2_eq_square by fastforce
  hence "2 dvd m^2" by simp
  hence "2 dvd m" by simp
  have "2 dvd n" proof -
    from ‹2 dvd m› obtain k where "m = 2 * k" ..
    with eq have "2 * n^2 = 2^2 * k^2" by simp
    hence "2 dvd n^2" by simp
    thus "2 dvd n" by simp
  qed
  with ‹2 dvd m› have "2 dvd gcd m n" by (rule gcd_greatest)
  with lowest_terms have "2 dvd 1" by simp
  thus False using odd_one by blast
qed
```
This proof is translated into our language as follows
```
GOAL "sqrt 2 ∉ ℚ"
    CRUSH
    LET ?x = "sqrt 2"
    OBTAIN m n :: nat where "¦?x¦ = m / n" and "coprime m n"; END
    HAVE "m^2 = ?x^2 * n^2"; END
    HAVE "m^2 = 2 * n^2"; END
    HAVE "2 dvd m^2"; END
    HAVE "2 dvd m"; END
    HAVE "2 dvd n"
        OBTAIN k where "m = 2 * k"; END
        HAVE "2 * n^2 = 2^2 * k^2"; END
    END
    HAVE "2 dvd gcd m n"; END
    HAVE "2 dvd 1"; END
    HAVE "False"; END
END
```
Our language is much conciser because we use Sledgehammer to automatically generate every small proof script used in the original code. The idea is to let AI agent focus on the macroscopic proof route planing, and leave all the trivial small stuffs to existing proof automation mechanisms like Sledgehammer. 

Clients just need to start up our shell, send the above text through the standard input pipeline (`stdin`), and that is all required to prove lemmas using our shell. If the proof works, our shell shall return an Isabelle script allowing anyone to reproduce the proof.
## Communication Protocol

The communication is based on text, over the standard Input and Output pipeline (`stdin, stdout`). A request / response is written in a line and multiple requests / responses are separated by line breaks or semicolon symbol `;`. Also note, any term / type expression is not allowed to include line breaks.

A request has the following format,
```
@chan COMMAND-NAME   COMMAND-ARGUMENTS   <linebreak, CR, LF, or CRLF>
```
where `@chan` denotes *Channel ID* which is a natural number. `@chan` is optional and has a default value `0`, denoting the initial channel created when the shell starts up.

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

For example, an instance of `@chan GOAL "@expr"` is `42 GOAL "1 + 1 = 2"`. The double quote symbol `"` is a literal must be presented in the request text.

### Concurrency & Multiplex

The shell supports multiplex. Clients can open multiple concurrent channels while the processing in each channel is sequential (first requested, first served). 

| COMMAND & SYNTAX        | RESPONSE   | DESCRIPTION                                                                                 |
| ----------------------- | ---------- | ------------------------------------------------------------------------------------------- |
| `@chan NEW_CHANNEL`     | `{ID: ID}` | create a new channel, returning the ID of the new channel. Argument `@chan` is meaningless. |
| `@chan RELEASE_CHANNEL` | null       | Kill and release the channel `@chan`.                                                       |

If a request calls a non-existing or released channel, the shell responds with error message `bad channel`.  The shell continues running even when all channels are released.

Processes in different channels are parallel. However, we cannot guarantee a channel to use exactly one thread. Some Isabelle tactic can use multiple threads. Luckily, Isabelle has its own thread scheduling. Thus, it is safe to open as many channels as your CPU cores.

## Proof Model

Focusing on one channel, the proof process is essentially manipulating a state machine. The state of this state machine is defined as follows and the commands in our shell are transition rules of this state machine.

$$\begin{gather*}
\begin{aligned}
\text{Context} &\triangleq \text{Variable}\ \text{list} \times \text{Hypothesis}\ \text{list}& &\text{A context consists of fixed variables and hypotheses}\\
\text{Proposition} &\triangleq \text{Context} \times \text{Term}& &\text{A proposition is a target conclusion under a context}\\
\text{Goal} &\triangleq \text{Proposition} + \text{Bundle}& &\text{A goal is either a proposition or a bundle of subgoals}\\
\text{Bundle} &\triangleq \text{Context} \times \text{Goal}\ \text{list} & &\text{A bundle collects subgoals under a common context}\\
\text{Proof State} &\triangleq \text{Goal}& &\text{The state of our state machine}\\
\text{Variable} &\triangleq \text{Name} \times \text{Type}& &\text{A variable consists of its name and its type}\\
\text{Hypothesis} &\triangleq \text{Name} \times \text{Term}& &\text{A hypothesis consists of its name and its term}
\end{aligned}\\
\text{A term is an Isabelle/HOL term. A type is an Isabelle/HOL type}
\end{gather*}$$

A bundle $(ctxt,gs)$ collects several subgoals $gs$ and specifies their common context $ctxt$. Since the subgoals $gs$ can also be bundles, a bundle forms a tree where a leaf is a proposition, a node and its subtree form a bundle, and the children of the node is given by the subgoals of the bundle. The state of our state machine, called *proof state*, is a tree as described above.

A tree is *valid* iff each variable and hypothesis in the tree has a unique name within its own category. A tree is *normal* iff (1) it is valid, (2) no node has no child, (3) no node has one child. The conditions (1), (2) are invariants maintained by our commands. The condition (3) is maintained by applying the following reduction exhaustively for every subtree and instantly after every command application.

$$(ctxt,[(ctxt',goal)]) \leadsto (ctxt + ctxt', goal)$$

where $ctxt + ctxt' \triangleq (vs + vs', hs + hs')$ if $ctxt = (vs,hs)$ and $ctxt' = (vs',hs')$. The operator $(+)$ between two lists denotes list concatenation.

The children of a node, in other words, the subgoals of a bundle, are written from left to right. The first subgoal in the list is the left-most child. In our text, we use *current bundle* (`@current_bundle`) to denote the bundle corresponding to the left-most node, and *current goal* (`@current_goal`) to denote the proposition corresponding to the left-most leaf. `@current_goal` must be the first subgoal of `@current_bundle`. `@current_goal` means the goal that one needs first prove. Most of tactics in our shell are applied to `@current_goal`.
### Syntax in Responses
Since the proof state will be printed in the responses of many command applications, we define its JSON embedding in this section.
```js
Context     ::= {"vars": [Variable], "hyps": [Hypothesis]} // [Variable] denotes a list of Variables
Proposition ::= {"ctxt": Context, "goal": Term}
Goal   ::= Proposition | Bundle
Bundle ::= {"ctxt": Context, "goal": [Goal]} 
Proof State ::= Bundle
Variable    ::= {"name": Name, "type": Type}
Hypothesis  ::= {"name": Name, "expr": Term}
Term ::= string
Type ::= string
Name ::= string
```
#### Print Mode

There are different ways to print a term / type expression into a string. Command `PRINT_MODE` allows clients to indicate the format of all the output in a channel.

**COMMAND SYNTAX:**   `@chan PRINT_MODE @mode` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** 
- `@mode = 1` uses pretty printer, i.e., the output will be the same as what you can see in Isabelle's GUI
- `@mode = 2` prints s-expression with full names (every constant will be printed in long-identifier format, `Theory_Name.Constant_Name`). This allows one to overcome syntax overloading and reconstruct the internal terms. Lambda variables are represented by de-Bruijn indexes, in format `_123`, (the index number leaded by an underscore). Lambda expression $\lambda(x:\tau). t$ will be printed as (`\<lambda>` $\tau$ $t$). Lambda application $f\ a\ b\ \cdots\ c$ will be `(f a b ... c)`

### Semantics

Every proof state $\phi$ is interpreted to a boolean expression $\langle\phi\rangle$.

$$\langle(([v_1,\cdots,v_m],[h_1,\cdots,h_r]),[g_1,\cdots,g_n])\rangle\triangleq \forall \langle v_1\rangle \cdots\langle v_m\rangle.\ \langle h_1\rangle \rightarrow \cdots\rightarrow \langle h_r\rangle \rightarrow \langle g_1\rangle \land \cdots\land \langle g_n\rangle$$

It means the actual context of a proposition is the concatenation of the contexts of all its ancestors.
## Proof Commands
### Proof Management

**COMMAND SYNTAX:**  `@chan GOAL "@expr"` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** Initiate a fresh proof environment, setting `@expr` as the goal. Any previous proof environments will be discarded.

The initial proof state is `(([],[]), @expr)`.


**COMMAND SYNTAX:**  `@chan END` <br />
**COMMAND SYNTAX:**  `@chan NEXT` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** When `@current_goal` is proven, the shell will not turn to the next subgoal automatically. Instead, we require an explicit command `END` to be applied.

Basically any `GOAL`, `HAVE`, `OBTAIN` (introduced later) should be ended by an `END`.

If the `@current_goal` is not in a form clearly demonstrating it is proved (e.g., `True`), `HAMMER` command will be applied to try to prove the goal first. Thus, command sequence (`HAMMER`; `END`)  can be simply written as `END`.

Given a proof state whose current bundle is $(ctxt, [g]+gs)$, this command replaces the current bundle with $(ctxt, gs)$, if $g$ is trivially true or provable by `HAMMER`.

Specially, if the proof state is a leaf $(ctxt, g)$, this command checks if $g$ is the boolean literal $\texttt{True}$. If not, it applies `HAMMER` to prove $g$.

Command `NEXT` is an abbreviation of `END`. We introduce this abbreviation because some commands (e.g., `auto`) and tactics (e.g., `CRUSH`) can introduce subgoals whose number is unknown until the runtime. `END` has a structural meaning suggesting its number should equal the number of commands opening some context, e.g., `HAVE ...; END; OBTAIN ...; END`. However, if `CRUSH` introduces 3 subgoals, `CURSH; END; END; END` looks weird. Thus we use the abbreviation to write it as `CRUSH; NEXT; NEXT; END` which looks better.
### Proof Tactics that All you Need

Even when Isabelle provides tens of various tactics, the really useful tactics that an AI agent needs are very little. The following commands provide common combinations of these tactics.

--------

**COMMAND SYNTAX:**   `@chan CRUSH @rules` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** Apply Isabelle simplifier to simplify the `@current_goal`, with a configurable simplification set, all contextual hypotheses, solvers like Presburger solver, and default heuristics. It aims to eliminate most trivial or simple subgoals and to reduce the goal into forms ready for agents to intervene. It can split the goal into several smaller goals that are easier to handle. Basically, this command is the first thing one needs to apply.

Given a proof state whose current goal (i.e., the left-most node) is $(ctxt, g)$, assuming the tactic simplifies and splits $g$ into a list $gs'$ of subgoals, this command replaces the current goal with $(ctxt, gs')$.

The command first attempts the `auto` tactic which can be non-terminating. Thus we set a configurable timeout (by default, 10 seconds). If it timeouts, we instead use a weaker tactic `(clarsimp; rule conj+)`. If it still timeouts, the command fails with error message "timeout". If the tactics cannot simplify the `@current_goal` even a bit, the commands fails with error message "fail".

`@rules` is an optional list of simplification rules should be additionally used.

-----------

**COMMAND SYNTAX:**   `@chan HAVE @name "@expr"` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** Ask the shell to suspend the `@current_goal`, and turn to first prove a subgoal `@expr` within the hypothesis context of `@current_goal`. The proof of `@expr` will be later added as a hypothesis into the context.
This is similar with Isabelle's `have` command.

The `@name` is optional. If not given, the shell generates a random name.

Given a proof state whose current goal is $(ctxt,g)$, this command replaces the current goal with $(ctxt, [\ (([],[]),expr)\ ,\ (([],[expr]),g)\ ])$.

Example:
```
// (ctxt, g)
HAVE "1 + 1 = 2"
// (ctxt, [ (([],[]),"1+1=2"), (([],["1+1=2"]),g) ])
END
// (ctxt, [ (([],["1+1=2"]),g) ])
// Here, a node has only one child, violating the normalization condition
// The shell thus applies the reduction rewritting the tree as
// ( ([],["1+1=2"]) + ctxt , g )
```
Another example:
```
// (ctxt, gs)
HAVE "A"
// (ctxt, [ (([],[]),"A"), (([],["A"]),g) ])
HAVE "B"
// (ctxt, [ (([],[]), [(([],[]),"B"), (([],["B"]),"A")] ), (([],["A"]),g) ])
END
// (ctxt, [ (([],["B"]),"A"), (([],["A"]),g) ])
// lemma B is available in proving A
END
// ( ([],["A"]) + ctxt , g )
// lemma B is NOT available in proving g
```

--------------------
**COMMAND SYNTAX:**   `@chan OBTAIN @varnames where @name : \<open> @condition \<close>` <br />
This `OBTAIN` command has the same syntax with Isabelle's `obtain` commands, except the attributes of `@name`. <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** It has the same semantics with Isabelle's `obtain` command. In terms of the shell's state machine, it behaviors similarly to the `HAVE` command, except that the subgoal expression `@expr` is $\exists\texttt{varnames}.\;\texttt{condition}$.

The `@name` is optional. If not given, the shell generates a random name.

Given a proof state whose current goal is $(ctxt,g)$, this command replaces the current goal with $(ctxt, [\ (([],[]),\exists varnames.\ expr)\ ,\ (([],[\exists varnames.\ expr]),g)\ ])$.

------------
**COMMAND SYNTAX:**   `@chan HAMMER @timeout` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** If the AI agent believes the `@current_goal` is straightforward enough, call this command to invoke Sledgehammer to finalize the proof for this `@current_goal`. Sledgehammer terminates only when it successfully solves the goal. Thus `@timeout` is used to indicate when should the shell give up and respond with error message "timeout". Note, Sledgehammer is generally slow, the recommended timeout is 30 seconds.

Given a proof state whose current goal is $g$, this command replace the goal with $\texttt{True}$ if the proof search succeeds.

This command uses a smart strategy. Before applying Sledgehammer, it first applies `CRUSH` to simplify and split the goal into several smaller subgoals. For each such subgoal, the command first applies `blast` within a timeout (1 second). If fails, try `fastforce` within 2 seconds. If still fails, finally the command tries the Sledgehammer.

-----------------------
Above, we described all the commonly used automatic tactics. The tactics above should be enough for the most situations. However, sometimes, manual proof is still required. Here the shell provides three commands that cover all kinds of manual proofs --- applying introduction and elimination rules, in a resolution manner, and applying unfolding.

**COMMAND SYNTAX:**   `@chan RULE @rule` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** Applying the introduction / elimination rule `@rule` to the `@current_goal`. Multiple new subgoals can be introduced as the consequence. The `@rule` is the name of the rule. To parse the name, we first check local context (the named hypotheses in the proof environment) and then the Isabelle system.

Given a proof state whose current goal is $(ctxt, g)$, this command applies the introduction resolution if the given `@rule` is an introduction rule, or the elimination resolution if `@rule` is an elimination rule.
Assuming the resolution returns a list $gs'$ of subgoals, the command replaces the current goal with $(ctxt, gs')$.
We refer readers to our Appendix for the introduction / elimination resolution, and also Isabelle's `implementation` document about tactic `resolve_tac` and `eresolve_tac`.

Attributes are allowed in `@rule`, e.g., `exI[where x=1]`, though it is generally an advanced feature.

**COMMAND SYNTAX:**   `@chan UNFOLD @rule` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** Apply the rewrite rule `@rule` to every occurrence of the redex of the rule. `@rule` must be an HOL equation. Otherwise, the shell responds with error message "bad rule: not an equation".

Given a proof state whose current goal is $g$, 

This command uses Isabelle's `unfold` tactic.

Attributes are allowed in `@rule`, e.g., `exI[where x=1]`, though it is generally an advanced feature.

----------

Finally, readers may expect Isabelle's `apply` command for applying an arbitrary tactic. Though this command is really unnecessary when the above commands are presents, we still decide to support it in our shell.

**COMMAND SYNTAX:**   `@chan APPLY @tactic` <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** Apply the `@tactic` to the current goal.

Given a proof state whose current goal is $(ctxt,g)$, this command applies `@tactic` to the goal. Assuming the application returns subgoals $gs'$, the command replaces the current goal with $(ctxt,gs')$.

Similarly to `CRUSH`, if `@tactic` returns multiple subgoals, clients are expected to use `NEXT` (or `END`) to close every subgoal.

### Lemmas Retrieval

TODO.

I can implement interfaces for Isabelle's pattern-based theorem look-up mechanism, though I think the proper way to do this is semantic retrieval by some embedding model.

### Other Helper Commands

**COMMAND SYNTAX:**   `@chan LET ?@x = @term` <br />
The argument has the same syntax with Isabelle's `let` command <br />
**RESPONSE:**  Proof State <br />
**DESCRIPTION:** It has the same semantics with Isabelle's `let` command. It is used to introduce term abbreviations. It has no effect on the proof state. The returned proof state is simply unchanged.


# Appendix

## Introduction and Elimination Resolution

I found existing Isabelle documentation does not properly explain the notion of introduction & elimination resolution (or I didn't find the proper document). I briefly explain them here.

**Notation** We use $\Theta; \Gamma \vdash G$ to denote a proof goal having target conclusion $G$, variable context $\Theta$, and hypothesis context $\Gamma$. $\Theta, \Gamma$ are sets.

**Introduction Resolution**. Given a proof goal $\Theta; \Gamma \vdash G$ and a rule

$$\begin{align*}
&(\bigwedge v_1.\ H_1^1 \Longrightarrow\cdots\Longrightarrow H_1^{n_1} \Longrightarrow A_1)\newline
\Longrightarrow\ &(\bigwedge v_2.\ H_2^1 \Longrightarrow\cdots\Longrightarrow H_2^{n_2} \Longrightarrow A_2)\newline
\Longrightarrow\ &\cdots\newline
\Longrightarrow\ &(\bigwedge v_m.\ H_m^1 \Longrightarrow\cdots\Longrightarrow H_m^{n_m} \Longrightarrow A_m)\newline
\Longrightarrow\ &G
\end{align*}$$
the introduction resolution reduces the goal into subgoals
$$\begin{align*}
&v_1\cup\Theta; \lbrace H_1^1,\cdots,H_1^{n_1}\rbrace\cup\Gamma\vdash A_1\newline
&v_2\cup\Theta; \lbrace H_2^1,\cdots,H_2^{n_2}\rbrace\cup\Gamma\vdash A_2\newline
&\qquad\cdots\newline
&v_m\cup\Theta; \lbrace H_m^1,\cdots,H_m^{n_m}\rbrace\cup\Gamma\vdash A_m
\end{align*}$$

**Elimination Resolution**. Given  a proof goal $\Theta; \lbrace A\rbrace\cup\Gamma \vdash C$ and a rule

$$\begin{align*}
&A\newline
\Longrightarrow\ &(\bigwedge v_1.\ H_1^1 \Longrightarrow\cdots\Longrightarrow H_1^{n_1} \Longrightarrow C)\newline
\Longrightarrow\ &(\bigwedge v_2.\ H_2^1 \Longrightarrow\cdots\Longrightarrow H_2^{n_2} \Longrightarrow C)\newline
\Longrightarrow\ &\cdots\newline
\Longrightarrow\ &(\bigwedge v_m.\ H_m^1 \Longrightarrow\cdots\Longrightarrow H_m^{n_m} \Longrightarrow C)\newline
\Longrightarrow\ & C
\end{align*}$$
assuming $A \notin \Gamma$, the elimination resolution reduces the goal into subgoals 
$$\begin{align*}
&v_1\cup\Theta; \lbrace H_1^1,\cdots,H_1^{n_1}\rbrace\cup\Gamma\vdash C\newline
&v_2\cup\Theta; \lbrace H_2^1,\cdots,H_2^{n_2}\rbrace\cup\Gamma\vdash C\newline
&\qquad\cdots\newline
&v_m\cup\Theta; \lbrace H_m^1,\cdots,H_m^{n_m}\rbrace\cup\Gamma\vdash C
\end{align*}$$