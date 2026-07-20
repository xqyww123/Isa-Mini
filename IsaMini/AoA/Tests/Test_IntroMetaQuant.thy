theory Test_IntroMetaQuant
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.IntroMetaQuant"]]

lemma intro_meta_quant: "\<forall>(n::int). n * n \<ge> 0"
  by aoa

end
