theory Test_IntroOverSpec
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.IntroOverSpec"]]

lemma t_over: "\<forall>(a::nat) b. a + b \<ge> 0"
  by aoa

end
