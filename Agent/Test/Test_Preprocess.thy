theory Test_Preprocess
  imports Minilang_AoA.Minilang_AoA
begin

ML \<open>
local
  fun mk_free_conj n =
    let val Ps = map (fn i =>
          Free ("P" ^ string_of_int i, \<^typ>\<open>bool\<close>)) (1 upto n)
    in foldr1 HOLogic.mk_conj Ps end

  fun mk_true_conj n =
    foldr1 HOLogic.mk_conj (replicate n @{term True})

  fun init_goal ctxt t =
    Goal.init (Thm.cterm_of ctxt (HOLogic.mk_Trueprop t))

  fun apply_split ctxt t =
    SINGLE (Goal_Preprocess.custom_split_tac ctxt 1) (init_goal ctxt t)

  fun apply_preprocess ctxt t =
    Seq.pull (Goal_Preprocess.preprocess_split_tac ctxt (init_goal ctxt t))
    |> Option.map fst

  fun assert msg b = if b then () else error ("Test failed: " ^ msg)

  val ctxt = \<^context>
in

(* Test 1: 100-atom conjunction \<rightarrow> splits into 76 subgoals
   (25 atoms remain in an unsplit chunk because their combined size < 50) *)
val _ =
  let val SOME r = apply_split ctxt (mk_free_conj 100)
      val n = Thm.nprems_of r
  in assert ("expected 76, got " ^ string_of_int n) (n = 76);
     writeln ("Test 1 passed: 100-atom conj \<rightarrow> " ^ string_of_int n ^ " subgoals")
  end

(* Test 2: 10-atom conjunction (size < split_skip_size) \<rightarrow> no split *)
val _ =
  let val t = mk_free_conj 10
      val _ = assert "size should be < split_skip_size"
                (Infra_Filter.smart_size_of_term t
                  < Goal_Preprocess.split_skip_size)
      val SOME r = apply_split ctxt t
  in assert "should remain 1 subgoal" (Thm.nprems_of r = 1);
     writeln "Test 2 passed: small conjunction (size < split_skip_size) left unsplit"
  end

(* Test 3: Implication (big \<longrightarrow> big) \<rightarrow> impI then split conclusion *)
val _ =
  let val big = mk_free_conj 100
      val SOME r = apply_split ctxt (HOLogic.mk_imp (big, big))
      val n = Thm.nprems_of r
  in assert ("expected 76, got " ^ string_of_int n) (n = 76);
     writeln ("Test 3 passed: implication \<rightarrow> " ^ string_of_int n ^ " subgoals")
  end

(* Test 4: Universal (\<forall>x::nat. big) \<rightarrow> allI then split *)
val _ =
  let val big = mk_free_conj 100
      val SOME r = apply_split ctxt
            (HOLogic.mk_all ("x", \<^typ>\<open>nat\<close>, big))
      val n = Thm.nprems_of r
  in assert ("expected 76, got " ^ string_of_int n) (n = 76);
     writeln ("Test 4 passed: universal \<rightarrow> " ^ string_of_int n ^ " subgoals")
  end

(* Test 5: Mixed nested: \<forall>x. (big \<longrightarrow> big) \<and> big \<rightarrow> allI, then impI+split on left,
   split on right *)
val _ =
  let val big = mk_free_conj 100
      val body = HOLogic.mk_conj (HOLogic.mk_imp (big, big), big)
      val SOME r = apply_split ctxt
            (HOLogic.mk_all ("x", \<^typ>\<open>nat\<close>, body))
      val n = Thm.nprems_of r
  in assert ("expected > 1, got " ^ string_of_int n) (n > 1);
     writeln ("Test 5 passed: mixed nested \<rightarrow> " ^ string_of_int n ^ " subgoals")
  end

(* Test 6: Disjunction (100 atoms) \<rightarrow> not split *)
val _ =
  let val Ps = map (fn i =>
          Free ("P" ^ string_of_int i, \<^typ>\<open>bool\<close>)) (1 upto 100)
      val big_disj = foldr1 HOLogic.mk_disj Ps
      val SOME r = apply_split ctxt big_disj
  in assert "disjunction should remain 1 subgoal" (Thm.nprems_of r = 1);
     writeln "Test 6 passed: disjunction left unsplit"
  end

(* Test 7: preprocess_split_tac on small goal \<rightarrow> passthrough (below threshold) *)
val _ =
  let val SOME r = apply_preprocess ctxt (mk_free_conj 100)
  in assert "small goal should remain 1 subgoal" (Thm.nprems_of r = 1);
     writeln "Test 7 passed: small goal passes through preprocess"
  end

(* Test 8: preprocess_split_tac on large provable goal (True conj) \<rightarrow> auto solves it *)
val _ =
  let val big_true = mk_true_conj 600
      val prem_size = Infra_Filter.smart_size_of_term
            (HOLogic.mk_Trueprop big_true)
      val threshold = Goal_Preprocess.preprocess_size_threshold
      val _ = assert ("size should be > " ^ string_of_int threshold ^
                      ", got " ^ string_of_int prem_size)
                (prem_size > threshold)
      val SOME r = apply_preprocess ctxt big_true
  in assert "auto should solve all subgoals" (Thm.nprems_of r = 0);
     writeln "Test 8 passed: auto solves large provable goal"
  end

(* Test 9: preprocess_split_tac on large unprovable goal \<rightarrow>
   auto still succeeds by splitting the conjunction (conjI is a safe intro rule),
   producing one subgoal per atom *)
val _ =
  let val big = mk_free_conj 600
      val prem_size = Infra_Filter.smart_size_of_term
            (HOLogic.mk_Trueprop big)
      val threshold = Goal_Preprocess.preprocess_size_threshold
      val _ = assert ("size should be > " ^ string_of_int threshold ^
                      ", got " ^ string_of_int prem_size)
                (prem_size > threshold)
      val SOME r = apply_preprocess ctxt big
      val n = Thm.nprems_of r
  in assert ("expected 600, got " ^ string_of_int n) (n = 600);
     writeln ("Test 9 passed: auto splits large conj \<rightarrow> " ^ string_of_int n ^ " subgoals")
  end

end
\<close>

end
