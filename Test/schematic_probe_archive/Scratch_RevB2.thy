theory Scratch_RevB2
  imports Minilang.Minilang
begin

(* ROUND-2 review probe (READ-ONLY, no edits to proof.ML):
   verify the Python reviewer's C-F1 claim that after CASE_SPLIT only case 1
   is materialized on the stack, so a prerun that reads the FINAL state cannot
   count cases; and measure what the reporter's Goals message carries at the
   intermediate point (the proposed recording-reporter fix).

   D1: CASE_SPLIT on a 2-case goal carrying ?x. Record ALL reporter messages
       in order; then read the final state's goals_of' count.
   D2: SPLIT_CONJS then SPLIT_CONJS2 on goal 1 with a sibling goal present:
       what does the final state show (their "SplitConjs unaffected" side
       claim), and what Goals messages fire at the Minilang layer? *)

axiomatization PP :: "nat \<Rightarrow> bool" and QQ :: "nat \<Rightarrow> bool"
           and RR :: "nat \<Rightarrow> bool"

ML \<open>
val base_ctxt = Named_Target.theory_init \<^theory>

fun schematic_ctxt ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt

(* U8-repaired harness: declare the read prop so fixed frees keep their
   real types (the old Scratch_SchematicProbe harness lacked this and its
   CASE_SPLIT cells false-failed even in the control group). *)
fun mk_state' fixes prop_str =
  let val ctxt0 = #2 (Variable.add_fixes fixes base_ctxt)
      val t  = Syntax.read_prop (schematic_ctxt ctxt0) prop_str
      val ctxt = Variable.declare_term t ctxt0
      val ct = Thm.cterm_of ctxt t
   in Minilang.INIT ctxt (Goal.init ct) end

fun run script s = Minilang.parse_cmds (Minilang.lex_cmds script) s

fun term_str ctxt t = Syntax.string_of_term ctxt t
fun vars_of t = Term.add_vars t [] |> map (fn (xi, T) =>
      Term.string_of_vname xi ^ "::" ^ Syntax.string_of_typ base_ctxt T)

fun msg_str ctxt (Minilang.Goals ts) =
      "Goals[" ^ string_of_int (length ts) ^ "]:\n" ^
      cat_lines (map_index (fn (i, t) =>
        "    #" ^ string_of_int (i+1) ^ " " ^ term_str ctxt t ^
        "   Vars={" ^ commas (vars_of t) ^ "}") ts)
  | msg_str _ (Minilang.New_Items _) = "New_Items"
  | msg_str _ (Minilang.Consider_Case (n, _)) = "Consider_Case " ^ n
  | msg_str _ (Minilang.Newly_Fixed _) = "Newly_Fixed"
  | msg_str _ (Minilang.Internal _) = "Internal"

fun goals_str s =
  let val ctxt = Minilang.context_of s
   in (case try Minilang.leading_proof_sequent_of s of
         NONE => "  <no sequent>"
       | SOME st =>
           (case Minilang.goals_of' st of
              [] => "  <0 subgoals>"
            | gs => cat_lines (map_index (fn (i, g) =>
                      "  goal " ^ string_of_int (i+1) ^ ". " ^
                      term_str ctxt g ^ "   Vars={" ^ commas (vars_of g) ^ "}") gs)))
  end

(* Run `script` with a RECORDING reporter; print the recorded messages in
   order, then the final state's goals. *)
fun probe_rec label prop_str fixes script =
  let val msgs = Unsynchronized.ref ([] : Minilang.message list)
      val _ = Minilang.set_reporter (fn m => msgs := m :: !msgs)
      val res = Exn.capture (fn () => run script (mk_state' fixes prop_str)) ()
      (* default_reporter is NOT exported from Minilang; K () is its body *)
      val _ = Minilang.set_reporter (K ())
   in case res of
        Exn.Res s =>
          let val ctxt = Minilang.context_of s
           in writeln (label ^ "  [OK] goal=" ^ prop_str ^ "  script=" ^ script);
              writeln ("  --- recorded messages, in order ---");
              List.app (fn m => writeln ("  " ^ msg_str ctxt m)) (rev (!msgs));
              writeln ("  --- final state ---");
              writeln (goals_str s)
          end
      | Exn.Exn exn =>
          if Exn.is_interrupt exn then Exn.reraise exn
          else writeln (label ^ "  [EXN] " ^ Runtime.exn_message exn)
  end
\<close>

ML \<open>writeln "======== RevB2 D1: CASE_SPLIT, 2 cases, ?x in every case ========"\<close>

ML \<open>
probe_rec "D1 CASE_SPLIT ys" "rev (rev (ys::nat list)) = ys \<and> QQ ?x" ["ys"]
  "CASE_SPLIT ys";
\<close>

ML \<open>writeln "======== RevB2 D1b: control, no schematic ========"\<close>

ML \<open>
probe_rec "D1b CASE_SPLIT ys (control)" "rev (rev (ys::nat list)) = ys" ["ys"]
  "CASE_SPLIT ys";
\<close>

ML \<open>writeln "======== RevB2 D2: SPLIT_CONJS then SPLIT_CONJS2 with a sibling present ========"\<close>

ML \<open>
probe_rec "D2 SPLIT_CONJS; then SPLIT_CONJS2 on goal 1"
  "((QQ ?x \<and> PP ?x) \<and> RR 3)" []
  "SPLIT_CONJS SPLIT_CONJS2";
\<close>

end
