theory User_Operation_Interpret_Test
  imports User_Operation_Test_Base
begin

text \<open>
  The \<open>USER\<close> branch of \<open>interpret_i\<close> (docs/USER_OPERATIONS.md, sections 1,
  2 and 4.1), with operations registered inline: the operation runs and the
  agent is sent exactly one \<open>Goals\<close>, the one of the derived subgoals; a
  schematic variable left in two subgoals refuses the step with the approved
  text, whether the stack kept its depth or grew; an unregistered name is
  refused where it is executed; and the failures of the reader of method
  text, each exactly one of the four approved texts.
\<close>

consts PP :: "nat \<Rightarrow> bool"

ML \<open>
local
open MiniLang_Agent_Plugin User_Operation_Test

fun apply_method text s =
  Minilang.APPLY'' NONE [] (MiniLang_Agent.read_method_text (Minilang.context_of s) text) s
fun string_op name run : string user_operation =
  {name = name, default = true,
   unpack_arg = MessagePackBinIO.Unpack.unpackString, pack_arg = MessagePackBinIO.Pack.packString,
   run = run, pack_message = K NONE, callbacks = K []}
fun unit_op name run : unit user_operation =
  {name = name, default = true,
   unpack_arg = MessagePackBinIO.Unpack.unpackUnit, pack_arg = MessagePackBinIO.Pack.packUnit,
   run = run, pack_message = K NONE, callbacks = K []}

val thy = \<^theory>
  (*the running example of the spec: apply a proof method given as text*)
  |> register_user_operation {python_packages = []} (string_op "Apply" (fn _ => apply_method))
  (*composing a built-in command: HAVE opens a block for the statement*)
  |> register_user_operation {python_packages = []} (string_op "HaveText" (fn config => fn text =>
       MiniLang_Agent.interpret config (MiniLang_Agent.HAVE ("h", [], [], text, false))))
  (*closing the block END closes*)
  |> register_user_operation {python_packages = []} (unit_op "EndBlock" (fn config => fn () =>
       MiniLang_Agent.interpret config (MiniLang_Agent.END [])))
  (*two steps, each reporting its own Goals: the agent gets one, of the final subgoals*)
  |> register_user_operation {python_packages = []} (unit_op "TwoSteps" (fn _ => fn () =>
       apply_method "(rule conjI)" #> apply_method "(rule conjI)"))
  (*a named two-case BRANCH, as the sample's Consider composes it*)
  |> register_user_operation {python_packages = []} (unit_op "Cases" (fn config => fn () =>
       MiniLang_Agent.interpret config
         (MiniLang_Agent.BRANCH [(SOME "zero", "(2::nat) = 0"), (SOME "pos", "(2::nat) \<noteq> 0")])))
val ctxt = Named_Target.theory_init thy   (*a local theory, as a lemma's context is*)

fun text_arg name text = argument thy name (MessagePackBinIO.Pack.packString text)
fun unit_arg name = argument thy name (MessagePackBinIO.Pack.packUnit ())

val config : MiniLang_Agent.config =
  (fst MiniLang_Agent.default_cfg, snd MiniLang_Agent.default_cfg,
   {prem_counter = Synchronized.var "User_Operation_Interpret_Test" 0}, MiniLang_Agent.LIVE)

fun run cmd s = Minilang.record_reporter (MiniLang_Agent.interpret_i config cmd) s
fun apply text = run (MiniLang_Agent.USER ("Apply", text_arg "Apply" text))
fun goals_messages msgs = map_filter (fn Minilang.Goals gs => SOME gs | _ => NONE) msgs
fun refused text f =
  (case Exn.result f () of
      Exn.Exn (Minilang.OPR_FAIL (_, msg)) =>
        assert ("expected " ^ quote text ^ ", got " ^ quote msg) (msg = text)
    | Exn.Exn exn => error ("expected OPR_FAIL, got " ^ Runtime.exn_message exn)
    | Exn.Res _ => error ("expected the refusal " ^ quote text))
fun shared_variable_text operation vars =
  operation ^ " left the schematic variable" ^ (if length vars > 1 then "s " else " ") ^
  commas vars ^ " in more than one of the subgoals it produced. A schematic variable may \
  \be left in at most one subgoal, so this step is rejected."
val marker = Inner_Syntax_Error.marker
val ellipsis = "\226\128\166"   (*the window's ellipsis, UTF-8*)
fun syntax_error text f = fails_exactly ("Outer syntax error: " ^ text) f
fun leftover text f = fails_exactly ("Unexpected text after the tactic: " ^ text) f
in

(*1: two derived subgoals, one Goals message carrying exactly them*)
val (s1, msgs1) = apply "(rule conjI)" (state_of ctxt "A \<and> B")
val _ = assert "two subgoals" (Minilang.num_goals s1 = 2)
val _ = (case goals_messages msgs1 of
           [[a, b]] => assert "the Goals are the derived subgoals"
                         (a aconv \<^prop>\<open>A\<close> andalso b aconv \<^prop>\<open>B\<close>)
         | gs => error ("expected one Goals of two, got " ^ string_of_int (length gs) ^ " Goals messages"))

(*2: one subgoal, still exactly one Goals*)
val (_, msgs2) = apply "(rule impI)" (state_of ctxt "A \<longrightarrow> B")
val _ = assert "one Goals for one subgoal" (length (goals_messages msgs2) = 1)

(*3: a schematic variable shared by two subgoals is refused, with the approved text*)
val _ = refused (shared_variable_text "Apply" ["?x"])
          (fn () => apply "(rule exI, rule conjI)" (state_of ctxt "\<exists>x::nat. P x \<and> Q x"))
(*the inner exI's variable is renamed apart to ?y2; the names come in string order*)
val _ = refused (shared_variable_text "Apply" ["?x", "?y2"])
          (fn () => apply "(rule exI, rule exI, rule conjI)"
                      (state_of ctxt "\<exists>x y::nat. P x y \<and> Q x y"))

(*4: a variable in one subgoal only passes*)
val (_, msgs4) = apply "(rule exI)" (state_of ctxt "\<exists>x::nat. P x")
val _ = assert "one subgoal with its own variable" (length (goals_messages msgs4) = 1)

(*5: a name no imported theory registers, reached at execution (only a hand-built
  command can reach it: the codec refuses the name before any step runs)*)
val _ = fails_with "User operation \"Aply\": no imported theory registers it"
          (fn () => run (MiniLang_Agent.USER ("Aply", text_arg "Apply" "(rule conjI)")) (state_of ctxt "A \<and> B"))

(*6: an operation that opens a block, reporting no Goals of its own (HAVE): the
  derived subgoals are the new frame's, and the agent still gets one Goals*)
val s6 = state_of ctxt "(1::nat) + 1 = 2 \<and> B"
val (s6', msgs6) = run (MiniLang_Agent.USER ("HaveText", text_arg "HaveText" "(1::nat) + 1 = 2")) s6
val _ = (case goals_messages msgs6 of
           [[g]] => assert "the Goals of the opened block" (g aconv \<^prop>\<open>(1::nat) + 1 = 2\<close>)
         | gs => error ("expected one Goals of one, got " ^ string_of_int (length gs) ^ " Goals messages"))

(*7: solving the block's goal (the depth is unchanged, no goal is left): one
  empty Goals*)
val (s7, msgs7) = apply "(simp)" s6'
val _ = assert "the block's goal is solved" (Minilang.num_goals s7 = 0)
val _ = assert "one empty Goals after solving" (goals_messages msgs7 = [[]])

(*8: closing the block (the stack shrinks): no derived subgoal, one empty
  Goals, the main goal back*)
val (s8, msgs8) = run (MiniLang_Agent.USER ("EndBlock", unit_arg "EndBlock")) s7
val _ = assert "the main goal is back" (Minilang.num_goals s8 = 1)
val _ = assert "one empty Goals after closing" (goals_messages msgs8 = [[]])

(*9: two steps inside one run, each reporting Goals: the agent gets exactly one,
  of the subgoals the whole run derived.  conjI twice on (A \<and> B) \<and> C: the
  first step's Goals is [A \<and> B, C], the second's [A, B], the run's derived
  subgoals [A, B, C], which neither step reported on its own*)
val (s9, msgs9) = run (MiniLang_Agent.USER ("TwoSteps", unit_arg "TwoSteps")) (state_of ctxt "(A \<and> B) \<and> C")
val _ = assert "three subgoals" (Minilang.num_goals s9 = 3)
val _ = (case goals_messages msgs9 of
           [[a, b, c]] => assert "the one Goals is of the whole run"
                            (a aconv \<^prop>\<open>A\<close> andalso b aconv \<^prop>\<open>B\<close> andalso c aconv \<^prop>\<open>C\<close>)
         | gs => error ("expected one Goals of three, got " ^ commas (map (string_of_int o length) gs)))

(*10: an operation that opens a block of several cases (a named BRANCH): the
  stack grows, the leading frame holds the exhaustiveness goal, and the one
  Goals holds every case, as the opener reported them*)
val (s10, msgs10) = run (MiniLang_Agent.USER ("Cases", unit_arg "Cases")) (state_of ctxt "(2::nat) = 2")
val _ = (case Minilang.goals_of' (Minilang.leading_proof_sequent_of s10) of
           [g] => assert "the exhaustiveness goal leads" (g aconv \<^prop>\<open>(2::nat) = 0 \<or> (2::nat) \<noteq> 0\<close>)
         | gs => error ("expected the one exhaustiveness goal in the leading frame, got " ^ string_of_int (length gs)))
val _ = (case goals_messages msgs10 of
           [gs] => assert ("every case in the one Goals, got " ^ string_of_int (length gs)) (length gs = 3)
         | gs => error ("expected one Goals, got " ^ string_of_int (length gs) ^ " Goals messages"))
(*the same opener on a goal with a schematic variable: every case keeps it,
  so the step is refused, on the path where the stack grows*)
val _ = refused (shared_variable_text "Cases" ["?x"])
          (fn () => run (MiniLang_Agent.USER ("Cases", unit_arg "Cases")) (state_of ctxt "PP ?x"))

(*11: the reader of method text: each failure is exactly one of the four
  approved texts, the marker the one read_term's failures use*)
val _ = syntax_error ("(simp, " ^ marker ^ ")") (fn () => apply "(simp, )" (state_of ctxt "A \<and> B"))
val _ = syntax_error ("(simp add: foo" ^ marker) (fn () => apply "(simp add: foo" (state_of ctxt "A \<and> B"))
val _ = leftover ("simp" ^ marker ^ ")") (fn () => apply "simp)" (state_of ctxt "A \<and> B"))
val _ = fails_exactly "The tactic text is empty." (fn () => apply "" (state_of ctxt "A \<and> B"))
val _ = fails_exactly "Undefined tactic: \"simps\"" (fn () => apply "(simps)" (state_of ctxt "A \<and> B"))
(*a name that begins real method names: the name the agent wrote, quoted, and nothing more*)
val _ = fails_exactly "Undefined tactic: \"aut\"" (fn () => apply "(aut)" (state_of ctxt "A \<and> B"))
(*a text that does not even tokenize: the unclosed string, marked at its quote*)
val _ = syntax_error ("(simp add: " ^ marker ^ "\"foo") (fn () => apply "(simp add: \"foo" (state_of ctxt "A \<and> B"))
(*a text whose own symbols (chr 5, chr 6) break the YXML of the error message:
  the text unmarked, still the approved shape*)
val _ = syntax_error "\005\006x" (fn () => apply "\005\006x" (state_of ctxt "A \<and> B"))
(*long texts show a window around the spot, cut by an ellipsis on each side
  that is far from the spot; the windows below follow mark_window's rule by hand*)
val run_of = "aa bb cc dd ee ff gg hh ii jj kk ll mm nn"
(*a failure near the end: cut on the left only*)
val _ = syntax_error (ellipsis ^ "gg hh ii jj kk ll mm nn, " ^ marker ^ ")")
          (fn () => apply ("(simp add: " ^ run_of ^ ", )") (state_of ctxt "A \<and> B"))
(*a failure at the end of the text: the window ends in the marker*)
val _ = syntax_error (ellipsis ^ "ff gg hh ii jj kk ll mm nn" ^ marker)
          (fn () => apply ("(simp add: " ^ run_of) (state_of ctxt "A \<and> B"))
(*a failure in the middle, on the syntax-error path: cut on both sides*)
val _ = syntax_error (ellipsis ^ "kk ll mm nn, " ^ marker ^ ") aa bb cc dd ee" ^ ellipsis)
          (fn () => apply ("(simp add: " ^ run_of ^ ", ) " ^ run_of) (state_of ctxt "A \<and> B"))
(*a failure in the middle, on the leftover path: the leftover token's own offset*)
val _ = leftover (ellipsis ^ "kk ll mm nn) " ^ marker ^ ") aa bb cc dd ee" ^ ellipsis)
          (fn () => apply ("(simp add: " ^ run_of ^ ") ) " ^ run_of) (state_of ctxt "A \<and> B"))

val _ = writeln "ALL PASS: User_Operation_Interpret_Test"
end
\<close>

end
