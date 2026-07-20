theory Test_AutoRewriteFallback
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AutoRewriteFallback"]]

lemma "{x::nat. P x} = {x. Q x}"
  by aoa

end
