theory Test_AutoRewriteFallbackCascade
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AutoRewriteFallbackCascade"]]

lemma "{x::nat. P x} = {x. Q x}"
  by aoa

end
