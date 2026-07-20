theory Test_BoundCaptureConst
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.BoundCaptureConst"]]

(* Constant short-name collision: the summation binder `fact` collides with the
   constant `Factorial.fact`, which is used un-shadowed as `fact n` on the RHS.
   deconflict_bound_names now seeds its avoidance context with constant base
   names, so the bound index is alpha-renamed (fact -> fact1) for display,
   keeping it distinguishable from the constant `fact n`. (The body uses
   `fact + fact` rather than a bare `fact` so the lambda does not eta-contract
   away the binder.) *)
lemma bound_capture_const:
  fixes n :: nat
  shows "(\<Sum>fact = 0..n. real (fact + fact)) = real (fact n)"
  by aoa

end
