theory Test_Obvious_DenseIffFact imports
  "HOL-Analysis.Harmonic_Numbers" Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Obvious_DenseIffFact"]]

lemma
  "filterlim harm at_top sequentially =
     (\<forall>Z::real. eventually (\<lambda>t. Z < harm t) sequentially)"
  by aoa

end
