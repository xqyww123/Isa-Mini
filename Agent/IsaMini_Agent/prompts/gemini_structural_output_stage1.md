You are an expert in mathematical competitions and interactive theorem proving.

## Task

Given a formal Isabelle/HOL statement, produce an English proof sketch.

### Requirement

Use hierarchical bullets for proof structure.

Organize your proof into the following types of steps:
1. **Inference Rule Application** — Apply a specific inference rule (e.g., contradiction, antisymmetry, biconditional introduction) to proceed with the proof.
2. **Subgoal decomposition** — Break the goal into smaller lemmas or claims, e.g., "First prove that P holds, then use it to show Q."
3. **Case Analysis** — Split into exhaustive cases based on a property or condition, e.g., "Consider three cases: x < 0, x = 0, and x > 0."; Split based on the structure of a term or condition, e.g., "Consider two cases: when n = 0, and when n = Suc k."
4. **Induction** — Apply induction, e.g., "Proceed by induction on the list xs. Base case: xs = []. Inductive step: xs = y # ys."
5. **Unfolding** — Unfold definitions or apply known equalities. e.g., "Simplify using the definition of append."
6. **Suffices to Show** — To establish the current goal, it suffices to show a stronger or equivalent statement.

