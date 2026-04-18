theory Test_Induction_SingleCase
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_SingleCase"]]

text \<open>
  Regression / reproducer for the single-case Induction bug:
  SubgoalMaker._should_open_proof_block checks `len(top_goals) > 1`,
  so when an induction / case-split rule leaves exactly one remaining
  goal (the case with its hypothesis, e.g. `less_induct`'s single
  `case less`), no child GoalNode is created — the framework asks for
  a next SIBLING step instead of a CHILD step under the Induction,
  and the induction hypothesis floats as a premise on the parent's
  continuation rather than belonging to a dedicated case block.
\<close>

lemma \<open>P (n::nat)\<close>
  by aoa

end
