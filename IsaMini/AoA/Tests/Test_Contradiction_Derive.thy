theory Test_Contradiction_Derive
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Contradiction_Derive"]]

lemma contradiction_derive_test:
  assumes h0: "\<forall>n::nat. f n = (\<Sum>k | k dvd n. (1::real)) / real n"
      and h1: "\<forall>p::nat. p \<noteq> n \<longrightarrow> f p < f n"
  shows "n = (2520::nat)"
  by aoa

end
