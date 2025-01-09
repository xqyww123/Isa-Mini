### DONE

#### Elaboration

- distinguish for each subgoal the tactics and proofs applied to it.
- normalize all `induct` to `induction`, distinguishing IH and usual hyps

#### Simplification

- unifying various ways of expressing the same thing.
    - unifying `including` and `include`
    - using aaa unfolding bbb -> apply (unfold bbb) using aaa[unfolded bbb]
- simpler (outter) syntax
    - Isar state machine has 3 modes.
- simplify logic
    - When most of other mainstream PAs have only one layer in their logic,
      Isabelle has 2 levels.
      Isabelle is a logic framework, introducing 2 layers in the logic,
      the Meta level that resembles a first-order Pure Type System (PTS);
      and the Object level where the Higher Order Logic is encoded.
    - When other PAs have 2 layers in their proof mode.
      Worse, proof states involve 3 levels.
        Object level, PTS-meta level, PA-meta level (Proof Assistant level)
      An assumption can be represented in either of the 3 levels each of which
      needs quite different ways to handle in the use of the proof assistant.

#### 

### TODO

#### Clarification

- goal-directed step-wise calculation
- abductive rearranging lemmas.

#### Elaboration

- parse the explicit rule used in case analysis and induction.

### Nice Examples

- `MS_Test_Sublist.subseq_append`

