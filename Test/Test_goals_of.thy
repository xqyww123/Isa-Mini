theory Test_goals_of
  imports Minilang.Minilang
begin

text \<open>
  Empirically test @{ML "Minilang.goals_of'"} behavior on Minilang
  proof states in the protected (HOL.GOAL-nested) form.

  Key question: does goals_of' correctly extract N goal terms from
  a state where protect_goals has wrapped successive subgoals in
  nested HOL.GOAL?
\<close>

ML \<open>
local
  val ctxt0 = \<^context>
  val SOT = Syntax.string_of_term ctxt0
  val log = Unsynchronized.ref ([] : string list)
  fun L s = (log := s :: !log; tracing s)

  fun test_thm name st =
    let val prop = Thm.prop_of st
        val _ = L ("[" ^ name ^ "] prop_of = " ^ SOT prop)
        val _ = L ("[" ^ name ^ "] Thm.nprems_of = " ^ Int.toString (Thm.nprems_of st))
     in (\<^try>\<open>
           let val goals = Minilang.goals_of' st
            in L ("[" ^ name ^ "] goals_of' count = " ^ Int.toString (length goals));
               app (fn (i,g) =>
                 L ("[" ^ name ^ "]   goal[" ^ Int.toString i ^ "] = " ^ SOT g))
                 (map_index I goals)
           end
         catch exn =>
           L ("[" ^ name ^ "] goals_of' RAISED: " ^ Runtime.exn_message exn)\<close>)
    end

  fun test_state name s =
    let val _ = L ("[" ^ name ^ "] num_goals = " ^ Int.toString (Minilang.num_goals s))
     in test_thm name (Minilang.leading_proof_sequent_of s)
    end

  fun mk_state s =
    Syntax.read_prop ctxt0 s
    |> Thm.cterm_of ctxt0
    |> Goal.init
    |> Minilang.INIT ctxt0

  val _ = Minilang.set_reporter (K ())

  (* ===== Test 1: Single goal after INIT ===== *)
  val s1 = mk_state "P \<and> Q \<and> R"
  val _ = test_state "T1_single(P\<and>Q\<and>R)" s1

  (* ===== Test 2: After SPLIT_CONJS ===== *)
  val s2 = Minilang.SPLIT_CONJS s1
  val _ = test_state "T2_split(P\<and>Q\<and>R)" s2

  (* ===== Test 3: Single non-conj goal ===== *)
  val s3 = mk_state "P (b::bool)"
  val _ = test_state "T3_single(P b)" s3

  (* ===== Test 4: Goal with quantifiers after INTRO ===== *)
  val s4 = mk_state "\<forall>x::nat. P x"
  val (_, s4') = Minilang.INTRO Minilang.SINGLE_GOAL NONE NONE NONE s4
  val _ = test_state "T4_after_intro(forall)" s4'

  (* ===== Test 5: Goal with implication after INTRO ===== *)
  val s5 = mk_state "A \<longrightarrow> B"
  val (_, s5') = Minilang.INTRO Minilang.SINGLE_GOAL NONE NONE NONE s5
  val _ = test_state "T5_after_intro(imp)" s5'

  (* ===== Test 6: 4-conj split ===== *)
  val s6 = mk_state "A \<and> B \<and> C \<and> D"
  val s6' = Minilang.SPLIT_CONJS s6
  val _ = test_state "T6_split_4conj" s6'

in
  val _ = L "=== All goals_of' tests completed ==="
  val _ = File.write (Path.explode "/tmp/goals_of_test.log")
            (String.concatWith "\n" (rev (!log)) ^ "\n")
end
\<close>

end
