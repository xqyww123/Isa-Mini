theory Test_RewriteBoundCapture
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RewriteBoundCapture"]]

(* Reproduces the Rewrite/Derive bound-variable display collision reported for
   `sum_distrib_left` (`?r * sum ?f ?A = (\<Sum>n\<in>?A. ?r * ?f n)`, whose RHS binder
   is literally named `n`).

   The induction-style free variable `n` occurs in the summation RANGE `{0..n}`.
   After distributing the scalar `c` into the sum, the bound summation index
   inherits the lemma binder name `n` and now sits next to the free `n` of the
   range, so the goal displays as `\<Sum>n = 0..n. c * g n` -- the binder `n`
   collides with the free `n`.  A reader (LLM agent) cannot tell the two apart.

   Crucially the scalar `c` and summand `g k` are free of `n`, so the colliding
   free `n` appears ONLY in a sibling subterm (the range), never inside the
   binder body.  That is exactly the case `deconflict_bound_names` misses: it
   seeds its name context with schematic-variable names but NOT with the term's
   free variables, and only renames a binder against names found *inside its own
   body*, so a sibling-only free `n` never triggers a rename. *)
lemma rewrite_bound_capture:
  fixes n :: nat and c :: real and g :: "nat \<Rightarrow> real"
  shows "c * (\<Sum>k = 0..n. g k) = 0"
  by aoa

end
