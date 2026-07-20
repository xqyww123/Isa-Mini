theory Test_AutoRewriteFallbackCascade
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AutoRewriteFallbackCascade"]]

lemma "{x::nat. P x} = {x. Q x}"
  by aoa

end
