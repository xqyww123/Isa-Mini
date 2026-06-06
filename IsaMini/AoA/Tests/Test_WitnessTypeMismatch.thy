theory Test_WitnessTypeMismatch
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.WitnessTypeMismatch"]]

(* Reproduces the THM 1 (RSN: no unifiers) crash from a Witness whose type
   does not match the existentially quantified variable. The goal binds g of
   type `real \<times> real \<Rightarrow> real` (a function on a pair), but
   the witness is supplied curried as `\<lambda> x y. ...`, i.e. of type
   `real \<Rightarrow> real \<Rightarrow> real`. *)
lemma witness_type_mismatch:
  "\<exists>(g :: real \<times> real \<Rightarrow> real). g (0, 0) = (0::real)"
  by aoa

end
