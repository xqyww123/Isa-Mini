theory Test_Interactive_Cases
  imports Main Minilang.Minilang
begin

text \<open>
  Test the interactive MAGIC mechanism for CaseSplit/Induction.
  With @{ML "Minilang.interactive_cases"} enabled, CASES' pauses at an
  interactive MAGIC frame instead of auto-processing the first case.
  The OPEN_CASE command then selects a case and provides variable names.
\<close>

declare [[working_mode = STRICT]]

ML \<open>
local
  val ctxt0 = \<^context>
    |> Variable.add_fixes ["n"]
    |> #2
    |> Proof_Context.augment (Syntax.read_prop \<^context> "P (n::nat)")
    |> Config.put Minilang.interactive_cases true
    |> Config.put Minilang.deconflict_case_fixes true
  fun init ctxt = Minilang.INIT ctxt
    (Goal.init (Thm.cterm_of ctxt (Syntax.read_prop ctxt "P (n::nat)")))
  fun cmd s c = Minilang.parse_cmds (Minilang.lex_cmds c) s

  val _ = tracing "=== Test 1: fresh state has no interaction ==="
  val s0 = init ctxt0
  val _ = if Minilang.has_pending_interaction s0
          then error "FAIL: fresh state has interaction"
          else tracing "PASS"

  val _ = tracing "=== Test 2: CASE_SPLIT pauses with interaction ==="
  val s1 = cmd s0 "CASE_SPLIT n"
  val _ = if Minilang.has_pending_interaction s1
          then tracing "PASS: interaction pending"
          else error "FAIL: expected pending interaction"

  val _ = tracing "=== Test 3: OPEN_CASE resolves interaction ==="
  val s2 = cmd s1 "OPEN_CASE 0"
  val _ = if not (Minilang.has_pending_interaction s2)
          then tracing "PASS: resolved"
          else error "FAIL: still pending"
  val _ = tracing ("num_goals = " ^ Int.toString (Minilang.num_goals s2))

  val _ = tracing "=== Test 4: OPEN_CASE with variable names ==="
  val s3 = cmd s0 "CASE_SPLIT n"
            |> (fn s => cmd s "OPEN_CASE 0")
            |> (fn s => cmd s "SORRY_ONLY")
            |> (fn s => cmd s "NEXT")
  val _ = if Minilang.has_pending_interaction s3
          then tracing "PASS: second case also pauses"
          else error "FAIL: expected interaction for second case"
  val s4 = cmd s3 "OPEN_CASE Suc k"
  val _ = tracing ("num_goals after OPEN_CASE Suc k = " ^ Int.toString (Minilang.num_goals s4))
  val _ = if not (Minilang.has_pending_interaction s4)
          then tracing "PASS: second case opened"
          else error "FAIL: interaction still pending"
  val (vars4, _) = case Minilang.leading_goal_data s4
                      of (SOME (items, _), _) => items | _ => error "no goal"
  val var_names4 = map #1 vars4
  val _ = tracing ("vars after OPEN_CASE Suc k = " ^ String.concatWith ", " var_names4)
  val _ = if member (op =) var_names4 "k"
          then tracing "PASS: variable 'k' in context"
          else error ("FAIL: expected 'k' in vars: " ^ String.concatWith ", " var_names4)

  val _ = tracing "=== Test 5: bad case name errors ==="
  val ok5 = \<^try>\<open>
    let val _ = cmd s1 "OPEN_CASE Nonexistent"
     in false
    end
    catch Minilang.OPR_FAIL _ => true
        | ERROR _ => true
  \<close>
  val _ = if ok5 then tracing "PASS: bad case name raises error"
          else error "FAIL"

  val _ = tracing "=== Test 6: non-interactive mode ==="
  val ctxt_ni = Config.put Minilang.interactive_cases false ctxt0
  val s6 = cmd (init ctxt_ni) "CASE_SPLIT n"
  val _ = if not (Minilang.has_pending_interaction s6)
          then tracing "PASS: no interaction when disabled"
          else error "FAIL"
  val _ = tracing ("num_goals = " ^ Int.toString (Minilang.num_goals s6))

  val _ = tracing "=== Test 7: INDUCT pauses ==="
  val s7 = cmd s0 "INDUCT n"
  val _ = if Minilang.has_pending_interaction s7
          then tracing "PASS: INDUCT pauses"
          else error "FAIL"

  val _ = tracing "=== Test 8: OPEN_CASE on INDUCT ==="
  val s8 = cmd s7 "OPEN_CASE 0"
  val _ = if not (Minilang.has_pending_interaction s8)
          then tracing "PASS: INDUCT case opened"
          else error "FAIL"
  val _ = tracing ("num_goals = " ^ Int.toString (Minilang.num_goals s8))

  val _ = tracing "=== Test 9: (removed, merged into 10-11) ==="
  val _ = tracing "PASS"

  val _ = tracing "=== Test 10: NEXT VARS resolves interaction ==="
  val s10_pre = cmd s0 "CASE_SPLIT n"
                |> (fn s => cmd s "OPEN_CASE 0")
                |> (fn s => cmd s "SORRY_ONLY")
                |> (fn s => cmd s "NEXT VARS k")
  val _ = if not (Minilang.has_pending_interaction s10_pre)
          then tracing "PASS: NEXT VARS resolved interaction"
          else error "FAIL: interaction should be resolved by NEXT VARS"
  val (vars10, _) = case Minilang.leading_goal_data s10_pre
                       of (SOME (items, _), _) => items | _ => error "no goal"
  val _ = if member (op =) (map #1 vars10) "k"
          then tracing "PASS: variable 'k' in context via NEXT VARS"
          else error ("FAIL: expected 'k' in vars: " ^ String.concatWith ", " (map #1 vars10))

  val _ = tracing "=== Test 11: NEXT without VARS preserves interaction ==="
  val s11 = cmd s0 "CASE_SPLIT n"
             |> (fn s => cmd s "OPEN_CASE 0")
             |> (fn s => cmd s "SORRY_ONLY")
             |> (fn s => cmd s "NEXT")
  val _ = if Minilang.has_pending_interaction s11
          then tracing "PASS: NEXT without VARS preserves interaction"
          else error "FAIL"

  val _ = tracing "=== Test 12: SORRY (END_or_NXT) VARS resolves interaction ==="
  val s12_sorry = cmd s0 "CASE_SPLIT n"
                  |> (fn s => cmd s "OPEN_CASE 0")
                  |> (fn s => cmd s "SORRY VARS k")
  val _ = if not (Minilang.has_pending_interaction s12_sorry)
          then tracing "PASS: SORRY VARS resolved interaction"
          else error "FAIL: SORRY VARS should resolve interaction"
  val (vars12, _) = case Minilang.leading_goal_data s12_sorry
                       of (SOME (items, _), _) => items | _ => error "no goal"
  val _ = if member (op =) (map #1 vars12) "k"
          then tracing "PASS: variable 'k' via SORRY VARS"
          else error ("FAIL: expected 'k': " ^ String.concatWith ", " (map #1 vars12))

  val _ = tracing "=== Test 13: out-of-order case selection ==="
  val s13a = cmd s0 "CASE_SPLIT n"
  val s13b = cmd s13a "OPEN_CASE Suc"
  val _ = tracing ("num_goals after OPEN_CASE Suc = " ^ Int.toString (Minilang.num_goals s13b))
  val _ = if not (Minilang.has_pending_interaction s13b)
          then tracing "PASS: Suc case opened first"
          else error "FAIL"

  val _ = tracing "=== All tests passed ==="
in end
\<close>

end
