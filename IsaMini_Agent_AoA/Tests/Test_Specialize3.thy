theory Test_Specialize3
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Specialize3"]]

lemma specialize_test3:
  assumes h1: "P (0::nat)"
  shows "P (0::nat)"
  by  aoa

end
