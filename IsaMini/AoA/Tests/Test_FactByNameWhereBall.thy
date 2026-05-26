theory Test_FactByNameWhereBall
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.FactByNameWhereBall"]]

lemma factbyname_where_ball_test:
  assumes hmem: "(0::nat) \<in> A"
      and h: "\<forall>x\<in>A. P x"
  shows "P (0::nat)"
  by aoa

end
