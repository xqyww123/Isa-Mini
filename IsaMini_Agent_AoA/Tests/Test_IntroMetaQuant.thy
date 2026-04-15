theory Test_IntroMetaQuant
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroMetaQuant"]]

lemma intro_meta_quant: "\<forall>(n::int). n * n \<ge> 0"
  by aoa

end
