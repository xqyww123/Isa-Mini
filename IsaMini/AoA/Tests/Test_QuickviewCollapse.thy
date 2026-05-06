theory Test_QuickviewCollapse
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.QuickviewCollapse"]]

lemma "(10::nat) > 0"
  by  aoa

end
