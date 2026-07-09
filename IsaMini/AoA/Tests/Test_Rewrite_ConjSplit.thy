theory Test_Rewrite_ConjSplit imports Complex_Main
  Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_ConjSplit"]]

definition "mypred (x::real) \<equiv> (0 < x \<and> x < 1)"

lemma rewrite_conj_split_test:
  assumes h: "mypred t"
  shows "t < 1"
  by aoa

end
