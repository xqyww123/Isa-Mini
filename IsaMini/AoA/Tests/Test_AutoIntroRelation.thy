theory Test_AutoIntroRelation
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AutoIntroRelation"]]

(* docs/AUTO_INTRO_DECISION.md section 7: the motivating need, end to end. The
   exemption keeps the termination goal as `termination` opens it, so `relation`
   applies at step 1; the recursive-call subgoal it derives still gets its
   automatic Intro, the `wf` subgoal has no binder and gets none. The
   interpretation is test data. *)
declare [[AoA_tactics add: relation \<open>prove termination by a well-founded relation on the arguments\<close> shown_in: prompt]]
declare [[aoa_no_auto_intro whole_prop "Wellfounded.accp _ _"]]

function sum_upto :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_upto i N = (if N < i then 0 else i + sum_upto (Suc i) N)"
  by pat_completeness auto

termination sum_upto
  by aoa

end
