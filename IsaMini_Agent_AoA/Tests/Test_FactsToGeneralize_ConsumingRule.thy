theory Test_FactsToGeneralize_ConsumingRule
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.FactsToGeneralize_ConsumingRule"]]

text \<open>
  End-to-end test combining two features:

    1. Induction with a consumes >= 1 rule (`int_le_induct`). The
       consume premise has a schematic variable (`?k`) that is not
       bound by the induction target, so the agent is prompted via
       `Interaction_InstantiateSchematics`. Once `?k` is instantiated,
       the consume premise still cannot be discharged (the agent
       never supplies a `using` fact — intentionally no `using`
       channel on the agent API) and surfaces as a `Prem0` subgoal
       under `consumes_policy = "subgoals"`.

    2. `facts_to_generalize`: a local fact mentioning the induction
       target is carried through induction via the TAG+conj insertion
       channel, and must be restored under its original name in the
       induction case's context.

  The two features interact via the shared `dirty_frees` +
  `Method.insert_tac` independent-channel path in
  `library/proof.ML:INDUCT'`. This test ensures the wrapped TAG
  conjunction is NOT eaten by `Rule_Cases.consume` when
  `consumes >= 1` (the pre-existing bug fixed by routing `wrapped`
  through `Method.insert_tac` outside `induction_tac`'s facts
  parameter).
\<close>

lemma
  fixes i k :: int and Q :: "int \<Rightarrow> bool"
  shows "True"
  by aoa

end
