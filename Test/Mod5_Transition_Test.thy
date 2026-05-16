theory Mod5_Transition_Test
  imports Main
begin
declare [[ML_debugger, ML_print_depth = 1000]]
text \<open>
  Reproduces the goal that the AoA agent's Obvious tactic could not discharge:
  given that @{term "(t, p)"} belongs to a 12-element set S of residue pairs mod 5,
  show that the linear recurrence transition maps it back into S.

  The recurrence comes from @{term "T(n+1) = 2*P(n) + 9*T(n)"} and
  @{term "P(n+1) = 9*P(n) + 16*T(n)"}, reduced mod 5 (where 9 \<equiv> 4
  and 16 \<equiv> 1).
\<close>

definition S :: "(nat \<times> nat) set" where
  "S \<equiv> {(1,1), (1,0), (4,1), (3,3), (3,0), (2,3),
        (4,4), (4,0), (1,4), (2,2), (2,0), (3,2)}"

(* declare [[simp_trace, simp_trace_depth_limit=5]] *)

lemma "\<not> ((2 * (1::nat) + 4 * 1) mod 5 = 1 \<and> ((4::nat) * 1 + 1) mod 5 = 0) \<Longrightarrow> False"
  by simp
(* ML \<open>val _ = (Classical.trace := true)\<close> *)

(*
declare disjCI [rule del] insertCI[rule del]
declare disjCI [intro] insertCI[intro]
*)

ML \<open>
(* Mimics safe_tac exactly: REPEAT_DETERM1 (FIRSTGOAL (safe_steps_tac)) *)
fun debug_safe_tac ctxt limit st =
  let
    fun step n st =
      let val ngoals = Thm.nprems_of st in
      if n >= limit then
        (tracing ("=== STOPPED at step " ^ string_of_int n ^ " ===");
         tracing ("Subgoals: " ^ string_of_int ngoals); st)
      else if ngoals = 0 then (tracing ("DONE at step " ^ string_of_int n); st)
      else case Seq.pull (FIRSTGOAL (Classical.safe_steps_tac ctxt) st) of
        NONE =>
          (tracing ("safe_steps_tac NONE at step " ^ string_of_int n ^
                    ", " ^ string_of_int ngoals ^ " subgoals left"); st)
      | SOME (st', _) =>
          let val ngoals' = Thm.nprems_of st'
              val _ = tracing ("step " ^ string_of_int n ^ ": " ^
                               string_of_int ngoals ^ " -> " ^
                               string_of_int ngoals' ^ " subgoals")
          in step (n+1) st' end
      end
  in step 0 st end
\<close>

lemma
  " (t::nat) = 1 \<Longrightarrow>
  p = 1 \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 1 \<and> (4 * p + t) mod 5 = 1) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 1 \<and> (4 * p + t) mod 5 = 0) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 4 \<and> (4 * p + t) mod 5 = 1) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 3 \<and> (4 * p + t) mod 5 = 3) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 3 \<and> (4 * p + t) mod 5 = 0) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 2 \<and> (4 * p + t) mod 5 = 3) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 4 \<and> (4 * p + t) mod 5 = 4) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 4 \<and> (4 * p + t) mod 5 = 0) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 1 \<and> (4 * p + t) mod 5 = 4) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 2 \<and> (4 * p + t) mod 5 = 2) \<Longrightarrow>
  \<not> ((2 * p + 4 * t) mod 5 = 2 \<and> (4 * p + t) mod 5 = 0) \<Longrightarrow>
  ((2 * p + 4 * t) mod 5, (4 * p + t) mod 5) \<notin> {} \<Longrightarrow> (2 * p + 4 * t) mod 5 = 3 \<and> (4 * p + t) mod 5 = 2"
  apply (simp; fastforce) .

thm swap

ML \<open>
(* Bounded version of Classical.safe_tac.
   Fails (Seq.empty) if zero safe steps possible, matching REPEAT_DETERM1 semantics.
   Returns current state when limit hit or no more safe steps. *)
fun bounded_safe_tac ctxt limit st =
  let
    fun continue n st =
      if n >= limit then Seq.single st
      else if Thm.nprems_of st = 0 then Seq.single st
      else case Seq.pull (FIRSTGOAL (Classical.safe_steps_tac ctxt) st) of
        NONE => Seq.single st
      | SOME (st', _) => continue (n + 1) st'
  in
    case Seq.pull (FIRSTGOAL (Classical.safe_steps_tac ctxt) st) of
      NONE => Seq.empty
    | SOME (st', _) => continue 1 st'
  end

(* Replaces fast_force_tac but with bounded safe phase.
   Uses a global step counter so DEPTH_SOLVE can't reset the bound. *)
fun our_fastforce_tac ctxt =
  let val ctxt' = Clasimp.addss ctxt
      val safe_count = Unsynchronized.ref 0
      fun bounded_step st =
        let val n = !safe_count
        in if n > 50 then Seq.empty
           else case Seq.pull (FIRSTGOAL (Classical.safe_steps_tac ctxt') st) of
             NONE => Seq.empty
           | SOME (st', _) => (safe_count := n + 1; Seq.single st')
        end
  in
    Object_Logic.atomize_prems_tac ctxt THEN'
    SELECT_GOAL (DEPTH_SOLVE (
      bounded_step
      ORELSE
      (fn st => Classical.appWrappers ctxt'
        (Classical.inst_step_tac ctxt' ORELSE' Classical.unsafe_step_tac ctxt') 1 st)
    ))
  end
\<close>

(* Reproduce step_tac hang on residual goal *)
lemma step_tac_test:
  "((2 * p + 4 * t) mod 5, (4 * p + t) mod 5) \<notin> {} \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 1 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 1 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 4 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 3 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 3 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 2 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 4 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 4 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 1 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 2 \<Longrightarrow>
   (2 * p + 4 * t) mod 5 \<noteq> 2 \<Longrightarrow>
   ((2::nat) * p + 4 * t) mod 5 = 3"
  for t p :: nat
  apply (tactic \<open>Classical.step_tac (Clasimp.addss @{context}) 1\<close>)

(* Test *)
lemma mod5_transition_v1:
  assumes "(t, p) \<in> S"
  shows "((2 * p + 4 * t) mod 5, (4 * p + t) mod 5) \<in> S"
  using assms unfolding S_def
  apply (tactic \<open>HEADGOAL  (our_fastforce_tac @{context})\<close>)
  done

(* Original working workaround for reference *)
lemma mod5_transition:
  assumes "(t, p) \<in> S"
  shows "((2 * p + 4 * t) mod 5, (4 * p + t) mod 5) \<in> S"
  using assms unfolding S_def
  apply (fastforce del: disjCI insertCI intro: disjCI insertCI) .






lemma "(6::nat) mod 5 = 1" by simp

text \<open>
  The version below is closer to what the agent actually faced: the set is
  written inline (no named definition), and the hypothesis uses
  @{term "t mod 5"} / @{term "p mod 5"} wrappers rather than assuming
  the values are already small.
\<close>

lemma mod5_transition_inline:
  assumes "(t, p) \<in> {((1::nat),(1::nat)), ((1::nat),(0::nat)),
                      ((4::nat),(1::nat)), ((3::nat),(3::nat)),
                      ((3::nat),(0::nat)), ((2::nat),(3::nat)),
                      ((4::nat),(4::nat)), ((4::nat),(0::nat)),
                      ((1::nat),(4::nat)), ((2::nat),(2::nat)),
                      ((2::nat),(0::nat)), ((3::nat),(2::nat))}"
  shows "(((2::nat) * p + (4::nat) * t) mod (5::nat),
          ((4::nat) * p + t) mod (5::nat))
         \<in> {((1::nat),(1::nat)), ((1::nat),(0::nat)),
             ((4::nat),(1::nat)), ((3::nat),(3::nat)),
             ((3::nat),(0::nat)), ((2::nat),(3::nat)),
             ((4::nat),(4::nat)), ((4::nat),(0::nat)),
             ((1::nat),(4::nat)), ((2::nat),(2::nat)),
             ((2::nat),(0::nat)), ((3::nat),(2::nat))}"
  using assms by auto

text \<open>
  Hardest variant: the hypothesis talks about @{term "t mod 5"} and
  @{term "p mod 5"} belonging to S, and the conclusion has
  @{term "(2 * (p mod 5) + 4 * (t mod 5)) mod 5"}.
  This is what the agent actually needed to close.
\<close>

lemma mod5_transition_modular:
  assumes "(t mod 5, p mod 5)
           \<in> {((1::nat),(1::nat)), ((1::nat),(0::nat)),
               ((4::nat),(1::nat)), ((3::nat),(3::nat)),
               ((3::nat),(0::nat)), ((2::nat),(3::nat)),
               ((4::nat),(4::nat)), ((4::nat),(0::nat)),
               ((1::nat),(4::nat)), ((2::nat),(2::nat)),
               ((2::nat),(0::nat)), ((3::nat),(2::nat))}"
  shows "(((2::nat) * (p mod 5) + (4::nat) * (t mod 5)) mod (5::nat),
          ((4::nat) * (p mod 5) + t mod 5) mod (5::nat))
         \<in> {((1::nat),(1::nat)), ((1::nat),(0::nat)),
             ((4::nat),(1::nat)), ((3::nat),(3::nat)),
             ((3::nat),(0::nat)), ((2::nat),(3::nat)),
             ((4::nat),(4::nat)), ((4::nat),(0::nat)),
             ((1::nat),(4::nat)), ((2::nat),(2::nat)),
             ((2::nat),(0::nat)), ((3::nat),(2::nat))}"
  using assms by auto

text \<open>Also check that 0 never appears as the first component.\<close>

lemma S_fst_nonzero:
  assumes "(t, p) \<in> S"
  shows "t \<noteq> 0"
  using assms unfolding S_def by auto

end
