theory Test_Query_BundleBareName
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Query_BundleBareName"]]
declare [[AoA_use_proof_cache=false]]

(* A 2-member multi-fact bundle. Its real reference names are
   demo_bundle(1) = conjI and demo_bundle(2) = disjI1; the BARE name
   `demo_bundle` denotes the whole list and has no single universal key. *)
lemmas demo_bundle = conjI disjI1

lemma "(x::int) * x \<ge> 0"
  by aoa

end
