theory Test_HaveStructured
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HaveStructured"]]

lemma "(3::nat) + 1 > 3"
  by aoa

end
