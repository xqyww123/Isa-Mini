theory Test_UnfoldLocalEqNaming
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.UnfoldLocalEqNaming"]]

(* Finding #1 reproduction (real-time audit of PutnamBench putnam_1962_a2).

   Two local equality premises of identical shape `name = (\<lambda>...)`:
     - hfinf_def : hfinf = (\<lambda>g. g 0)
     - f_form    : f     = (\<lambda>x. x + 1)
   Both are local Free heads defined by a \<lambda>-equation hypothesis. Yet Unfold's
   definition discovery (Minilang.potential_defs_of_const) finds a *local*
   equation ONLY when its fact name is <head> + a hard-coded suffix
   (_def, _alt, .simps, ...): for a local Free head, Sign.the_const_type fails
   so the Find_Theorems search path is skipped, leaving only the suffix lookup.
   Hence `hfinf_def` (matches the `_def` suffix) unfolds, while the
   identically-shaped `f_form` (no matching suffix) is invisible to Unfold. *)
lemma unfold_local_eq_naming:
  assumes hfinf_def: "hfinf = (\<lambda>g::(int \<Rightarrow> int). g 0)"
      and f_form:    "f = (\<lambda>x::int. x + 1)"
  shows "hfinf f = f 0"
  by aoa

end
