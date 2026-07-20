theory Test_Define_Nullary
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_Nullary"]]

(* Reproduces the nullary-constant limitation of the Define operation.
   AoA's Define always routes the equations through Minilang.FUN'' (the
   function/fun package), whose left-hand side must apply the defined
   head to at least one argument. A genuine nullary constant such as
   `P = 5` is therefore rejected by the function package with
   "Function has no arguments", surfaced to the agent as the
   FailureReason "Failed to define the function: ...". *)

lemma define_nullary_test: "\<exists>P::nat. P = 5"
  by  aoa

end
