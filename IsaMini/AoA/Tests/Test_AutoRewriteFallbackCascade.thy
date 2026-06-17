theory Test_AutoRewriteFallbackCascade
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.AutoRewriteFallbackCascade"]]

lemma "{x::nat. P x} = {x. Q x}"
  by aoa

end
