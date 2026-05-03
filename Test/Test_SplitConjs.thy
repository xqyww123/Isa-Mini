theory Test_SplitConjs
  imports Minilang.Minilang
begin

text \<open>Test 1: Basic 2-way conjunction\<close>
lemma \<open>True \<and> True\<close>
  apply (min_script \<open>
  SPLIT_CONJS
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>Test 2: 3-way conjunction solved by simp\<close>
lemma \<open>True \<and> True \<and> True\<close>
  apply (min_script \<open>
  SPLIT_CONJS
  SIMP
  NEXT
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>Test 3: Conjunction after INTRO with implication, solved by simp\<close>
lemma "True \<longrightarrow> True \<longrightarrow> True \<and> True"
  apply (min_script \<open>
  INTRO
  SPLIT_CONJS
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>Test 4: ML-level test\<close>
ML \<open>
local
  val ctxt0 = \<^context>
  val log = Unsynchronized.ref ([] : string list)
  fun L s = (log := s :: !log; tracing s)
  val _ = Minilang.set_reporter (K ())

  fun mk_state s =
    Syntax.read_prop ctxt0 s
    |> Thm.cterm_of ctxt0
    |> Goal.init
    |> Minilang.INIT ctxt0

  val s1 = mk_state "P \<and> Q \<and> R"
  val s2 = Minilang.SPLIT_CONJS s1
  val n = Minilang.num_goals s2
  val _ = L ("After SPLIT_CONJS on P\<and>Q\<and>R: " ^ Int.toString n ^ " goals")
  val _ = \<^assert> (n = 3)

  val s3 = mk_state "A \<and> B"
  val s4 = Minilang.SPLIT_CONJS s3
  val _ = \<^assert> (Minilang.num_goals s4 = 2)

  val s5 = mk_state "P (b::bool)"
  val _ = (\<^try>\<open>
    let val _ = Minilang.SPLIT_CONJS s5
     in L "ERROR: should have raised OPR_FAIL" end
    catch Minilang.OPR_FAIL (Minilang.INVALID_OPR, _) =>
      L "Correctly rejected non-conjunction goal"
  \<close>)

in
  val _ = L "=== SPLIT_CONJS ML tests completed ==="
end
\<close>

end
