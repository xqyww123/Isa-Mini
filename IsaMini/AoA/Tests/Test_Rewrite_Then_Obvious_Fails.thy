theory Test_Rewrite_Then_Obvious_Fails
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RewriteThenObviousFails"]]

(* Regression: after a successful Rewrite as the last child of a block,
   filling the next step with a failing Obvious must produce a graceful
   failure_reason. The bug was that Minilang_State.execute() set
   assign_to.prooftree = None on IsabelleError, clobbering the block's
   shared _state_before_ending_ (which also backed the previous successful
   Rewrite's resulting_state). Refreshing the predecessor then raised
   InternalError("Prooftree is not initialized"). *)
lemma rewrite_then_obvious_fails:
  fixes x y :: nat and P :: "nat \<Rightarrow> bool"
  assumes h: "x = y"
  shows "P x"
  by  aoa

end
