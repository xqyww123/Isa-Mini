theory Test_Chaining
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Chaining"]]

(* Test: Chain two named facts via a mixed = / <= transitivity *)
lemma chaining_test:
  fixes a b c :: nat
  assumes ab: "a = b" and bc: "b \<le> c"
  shows "a \<le> c"
  by  aoa

end
