theory Test_DiagnoseRuleVsGoal
  imports Main Minilang.Minilang
begin

text \<open>Test @{ML Unify_Diagnostic.diagnose_rule_vs_goal} — the new function
that diagnoses why a rule's conclusion fails to unify with a proof goal.\<close>

ML \<open>
local
  val ctxt = @{context}

  fun goal_of s = Syntax.read_prop ctxt s
  fun thm_of s = Proof_Context.get_thm ctxt s

  fun test_diag label rules goal_str =
    let val goal = goal_of goal_str
        val result = Unify_Diagnostic.diagnose_rule_vs_goal ctxt rules goal
    in writeln ("=== " ^ label ^ " ===");
       writeln ("  goal: " ^ Syntax.string_of_term ctxt goal);
       (case result of
          SOME msg => writeln ("  diagnostic: " ^ msg)
        | NONE => writeln "  diagnostic: NONE")
    end

  (* --- Test 1: Head symbol clash (intro rule) --- *)
  val _ = test_diag "Head clash: conjI vs disjunction goal"
    [(false, thm_of "conjI")]
    "P \<or> Q"

  (* --- Test 2: Head clash (rule conclusion is iff = eq, not \<le>) --- *)
  val _ = test_diag "Head clash: Suc_le_mono vs int goal"
    [(false, thm_of "Suc_le_mono")]
    "(a::int) \<le> (b::int)"

  (* --- Test 3: Successful match should return NONE --- *)
  val _ = test_diag "Successful match: conjI vs conjunction goal"
    [(false, thm_of "conjI")]
    "P \<and> Q"

  (* --- Test 4: Elim rule head clash --- *)
  val _ = test_diag "Elim rule: conjE vs disjunction goal"
    [(true, thm_of "conjE")]
    "P \<or> Q"

  (* --- Test 5: Empty rules list --- *)
  val _ = test_diag "Empty rules list"
    []
    "P \<and> Q"

  (* --- Test 6: exI vs universally quantified goal --- *)
  val _ = test_diag "Head clash: exI vs universal goal"
    [(false, thm_of "exI")]
    "\<forall>x. P x"

  (* --- Test 7: Multiple rules, all fail --- *)
  val _ = test_diag "Multiple rules: conjI then disjI1, vs implication"
    [(false, thm_of "conjI"), (false, thm_of "disjI1")]
    "P \<longrightarrow> Q"

  (* --- Test 8: Goal under quantifiers (common in real proofs) --- *)
  val _ = test_diag "Quantified goal: conjI vs quantified disjunction"
    [(false, thm_of "conjI")]
    "\<And>x. P x \<or> Q x"

  (* --- Test 9: Type clash with nat-specific rule vs int goal --- *)
  val _ = test_diag "Type clash: Suc_lessD vs int less"
    [(false, thm_of "Suc_lessD")]
    "(a::int) < (b::int)"

in val _ = () end
\<close>

end
