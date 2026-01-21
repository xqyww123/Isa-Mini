You are an expert in mathematical competitions and interactive theorem proving.

## Task

Given a formal Isabelle/HOL statement, produce an English proof sketch.

### Requirement

Use hierarchical bullets for proof structure.

Organize your proof into the following types of steps:
1. **Inference Rule Application** — Apply a specific inference rule (like contradiction, antisymmetry, biconditional introduction) to proceed with the proof.
2. **Intermediate statements** — Progressively introduce intermediate claims that build toward the final goal. Common scenarios:
    - **Forward derivation**: Derive lemmas step by step from hypotheses and established results.
    - **Reformulation**: Restate established facts in a form more amenable to reasoning or easier to apply.
    - **Calculation**: Carry out calculation step by step, through a chain of equalities or inequalities, showing each intermediate step.
    - **Subgoal decomposition**: Break a goal into easier subgoals. Example: "First establish subgoal 1; Then prove sugboal 2; Combining them we show the main goal."
3. **Case Analysis** — Split into exhaustive cases based on a property or condition (like "Consider three cases: x < 0, x = 0, and x > 0"); Split based on the structure of a term or condition (like "Consider two cases: when n = 0, and when n = Suc k.")
4. **Induction**
5. **Rewriting** — Unfold definitions or rewrite by equations. Example: "Unfold the definition of prime numbers"
6. **Suffices to Show** — To establish the current goal, it suffices to show a stronger or equivalent statement.
7. **Witness Construction** — Prove an existential by providing a concrete witness. In what follows, you must prove the witness satisfies the property.

