theory Test_Specialize1
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Specialize1"]]

lemma specialize_test1:
  assumes h1: "P (0::nat)"
      and h2: "\<forall>x::nat. P x \<longrightarrow> Q x"
  shows "Q (0::nat)"
  by  aoa

end
