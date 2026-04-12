theory Test_Specialize4
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Specialize4"]]

lemma specialize_test4:
  assumes h1: "P (0::nat)"
      and h2: "\<forall>x::nat. P x \<longrightarrow> Q x"
  shows "Q (1 - (1::nat))"
  by   aoa

end
