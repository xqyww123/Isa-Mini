theory Test_SetupRewriting
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SetupRewriting"]]

definition myg :: "nat \<Rightarrow> nat" where "myg n = n + 5"

lemma setup_rewriting_test: "myg 3 = 8"
  by   aoa

end
