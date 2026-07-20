theory Test_AutoRewriteFallback
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AutoRewriteFallback"]]

lemma "{x::nat. P x} = {x. Q x}"
  by aoa

end
