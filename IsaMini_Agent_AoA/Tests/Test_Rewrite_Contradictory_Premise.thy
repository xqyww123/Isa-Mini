theory Test_Rewrite_Contradictory_Premise imports
  Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_Contradictory_Premise"]]

definition "MyConst1 \<equiv> (2::nat)"
definition "MyConst2 \<equiv> (3::nat)"

lemma contradictory_premise_test:
  assumes eq: "MyConst1 = MyConst2"
  shows "P"
  by   aoa

end
