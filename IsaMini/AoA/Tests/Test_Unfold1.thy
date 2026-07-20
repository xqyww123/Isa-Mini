theory Test_Unfold1
  imports Minilang_AoA.Minilang_AoA
begin
  
declare [[AoA_driver="test.Unfold1"]]

definition XXX where "XXX (a::int) b = (a + b)"

lemma XXX_alt: "XXX a b = b + a"
  unfolding XXX_def
  by auto

(* Test 1: Simple existential - prove there exists an x equal to 5 *)
lemma witness_test1: "XXX 1 2 = 3"
  by   aoa

end