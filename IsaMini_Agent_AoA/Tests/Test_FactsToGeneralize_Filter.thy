theory Test_FactsToGeneralize_Filter
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.FactsToGeneralize_Filter"]]

text \<open>
  Cover the four partitioning paths of the `facts_to_generalize` field
  on the Induction tool in one proof run:

    - local fact that mentions the induction target's free var
      (kept, routed to insertion, strengthens the IH)
    - local fact that does NOT mention any generalized variable
      (dropped with a warning about irrelevance)
    - global theorem name
      (dropped with a warning about non-locality)
    - unknown / unfound name
      (dropped with a warning about unresolved name)

  The set-up is small on purpose: one outer `fixes p :: nat`, a
  `Have` to introduce an unrelated local fact, and a `Have`-sub-proof
  whose auto-Intro gives a `premise0` that does mention the induction
  target.
\<close>

lemma
  fixes p :: nat
  shows "True"
  by aoa

end
