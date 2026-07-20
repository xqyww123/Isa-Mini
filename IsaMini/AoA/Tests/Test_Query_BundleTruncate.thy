theory Test_Query_BundleTruncate
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Query_BundleTruncate"]]
declare [[AoA_use_proof_cache=false]]

(* A 21-member fact: exercises the >20 truncation path (cap = 20 + a note). *)
lemmas big_bundle = refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl

lemma "(x::int) * x \<ge> 0"
  by aoa

end
