theory Test_Induction_InteractiveVars
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_InteractiveVars"]]

lemma "P (n::nat)"
  by aoa

end
