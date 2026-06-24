theory Test_Obvious_DenseIffFact imports
  "HOL-Analysis.Harmonic_Numbers" Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Obvious_DenseIffFact"]]

lemma
  "filterlim harm at_top sequentially =
     (\<forall>Z::real. eventually (\<lambda>t. Z < harm t) sequentially)"
  by aoa

end
