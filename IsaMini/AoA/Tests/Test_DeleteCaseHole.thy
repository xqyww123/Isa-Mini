theory Test_DeleteCaseHole
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.DeleteCaseHole"]]

lemma t1: "(0::nat) = 0 \<and> (P::nat\<Rightarrow>bool) 0"
  by  aoa

end
