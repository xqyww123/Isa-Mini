theory Scratch_SchematicProbe_DI
  imports Minilang.Minilang
begin

(* Probe: does Define (DEFINE''/FUN'') or Interpret_Locale (OPEN_MODULE'')
   disturb schematic variables of the MAIN goal?  Companion of
   Scratch_SchematicProbe.thy (same harness shape). *)

axiomatization PP :: "nat \<Rightarrow> bool" and QQ :: "nat \<Rightarrow> bool" where
  probe_rule_2: "PP n \<Longrightarrow> QQ n"

locale mylocale = fixes a :: nat assumes ax1: "a > 0" and ax2: "a < 10"
begin
  lemma loc_fact: "a \<noteq> 0" using ax1 by simp
end

locale polyloc = fixes g :: "'a \<Rightarrow> 'a" assumes gid: "g (g z) = z"

locale emptyloc = fixes b :: nat
begin
  lemma emp_fact: "b = b" by simp
end

ML \<open>
val base_ctxt = Named_Target.theory_init \<^theory>

fun fix_ctxt fixes ctxt = #2 (Variable.add_fixes fixes ctxt)
fun schematic_ctxt ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt

fun mk_state' fixes prop_str =
  let val ctxt  = fix_ctxt fixes base_ctxt
      val t  = Syntax.read_prop (schematic_ctxt ctxt) prop_str
      val ct = Thm.cterm_of ctxt t
   in Minilang.INIT ctxt (Goal.init ct) end

fun mk_state prop_str = mk_state' [] prop_str
fun run script s = Minilang.parse_cmds (Minilang.lex_cmds script) s

fun vars_str s =
  let val (vs, tvs) = Minilang.schematic_vars_of_goal true s
      val ctxt = Minilang.context_of s
      val vstr = map (fn (xi, T) =>
                    Term.string_of_vname xi ^ " :: " ^ Syntax.string_of_typ ctxt T) vs
      val tstr = map (fn (xi, _) => "?'" ^ #1 xi) tvs
   in "TVars=[" ^ commas tstr ^ "]  Vars=[" ^ commas vstr ^ "]" end

fun goals_str s =
  let val ctxt = Minilang.context_of s
   in (case try Minilang.leading_proof_sequent_of s of
         NONE => "  <no sequent>"
       | SOME st =>
           (case Minilang.goals_of' st of
              [] => "  <0 subgoals>"
            | gs => cat_lines (map_index (fn (i, g) =>
                      "  goal " ^ string_of_int (i+1) ^ ". " ^
                      Syntax.string_of_term ctxt g) gs)))
  end

fun sequent_str s =
  let val ctxt = Minilang.context_of s
   in (case try Minilang.leading_proof_sequent_of s of
         NONE => "  SEQUENT: <none>"
       | SOME st => "  SEQUENT: " ^ Syntax.string_of_term ctxt (Thm.prop_of st))
  end

fun show label s =
  writeln (label ^ "\n  " ^ vars_str s ^ "\n" ^ goals_str s ^ "\n" ^ sequent_str s)

fun exn_str exn =
  case exn of Minilang.OPR_FAIL (_, m) => "[OPR_FAIL] " ^ m
            | _ => "[EXN] " ^ Runtime.exn_message exn

fun catching label f =
  case Exn.capture f () of
    Exn.Res r => SOME r
  | Exn.Exn exn =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else (writeln (label ^ "  " ^ exn_str exn); NONE)

fun probe_ml label prop_str fixes (opr : Minilang.state -> Minilang.state) =
  case catching label (fn () => opr (mk_state' fixes prop_str))
    of SOME s => (show (label ^ "  [OK] goal=" ^ prop_str) s; SOME s)
     | NONE => NONE

fun probe' label s0 script =
  case catching label (fn () => run script s0)
    of SOME s => (show (label ^ "  [OK] script=" ^ script) s; SOME s)
     | NONE => NONE

fun probe_ml' label s0 (opr : Minilang.state -> Minilang.state) =
  case catching label (fn () => opr s0)
    of SOME s => (show (label ^ "  [OK]") s; SOME s)
     | NONE => NONE

(* Build a locale expression exactly the way Agent/agent.ML INTERPRET does. *)
fun mk_expr ctxt qualifier locale insts =
  let val where_clause =
        if null insts then ""
        else " where " ^ space_implode " and "
               (map (fn (n, v) => n ^ " = " ^ Symbol.open_ ^ v ^ Symbol.close) insts)
      val src = qualifier ^ ": " ^ locale ^ where_clause
   in Token.explode (Thy_Header.get_keywords' ctxt) Position.none src
      |> filter Token.is_proper
      |> Scan.error (Scan.finite Token.stopper
           (Parse.!!! (Parse_Spec.locale_expression --| Scan.ahead Parse.eof)))
      |> #1
  end

fun INTERPRET qualifier locale insts s =
  Minilang.OPEN_MODULE'' {auto_unfold_locale=true}
    (mk_expr (Minilang.context_of s) qualifier locale insts) s
\<close>

ML \<open>writeln "======== I: Interpret_Locale on a schematic main goal ========"\<close>

ML \<open>
(* I1: 2 obligations, main goal carries ?x *)
val i1 = probe_ml "I1 INTERPRET mylocale a=5" "QQ (?x::nat)" []
           (INTERPRET "ml5" "mylocale" [("a", "5::nat")]);
\<close>

ML \<open>
(* I1b: close both obligations, then look at the restored main goal *)
val i1b = case i1 of SOME s => probe' "I1b END the obligations" s "END" | NONE => NONE;
\<close>

ML \<open>
(* I1c: same, but discharge the obligations by SORRY (the sibling-skip path) *)
val i1c = case i1 of SOME s => probe' "I1c SORRY_END_ALL" s "SORRY_END_ALL" | NONE => NONE;
\<close>

ML \<open>
(* I1d: after restoring, is the main goal still usable / instantiable? *)
val _ = case i1c of SOME s => (probe' "I1d INST_VAR after interpret" s "INST_VAR ?x = \"7::nat\""; ())
                  | NONE => ();
\<close>

ML \<open>
(* I2: assumption-free locale -> `wrapped = false` path (no obligation at all) *)
val i2 = probe_ml "I2 INTERPRET emptyloc b=3" "QQ (?x::nat)" []
           (INTERPRET "eb" "emptyloc" [("b", "3::nat")]);
val _ = case i2 of SOME s => (probe' "I2b END" s "END"; ()) | NONE => ();
\<close>

ML \<open>
(* I3: can the agent smuggle the main goal's ?x into the instantiation? *)
val i3 = probe_ml "I3 INTERPRET mylocale a=?x (schematic inst)" "QQ (?x::nat)" []
           (INTERPRET "mlx" "mylocale" [("a", "?x::nat")]);
\<close>

ML \<open>
(* I4: schematic TYPE variable in the main goal *)
val i4 = probe_ml "I4 INTERPRET with ?'a in main goal" "(?f :: ?'a \<Rightarrow> ?'a) x = ?f x" []
           (INTERPRET "mlt" "mylocale" [("a", "5::nat")]);
val _ = case i4 of SOME s => (probe' "I4b SORRY_END_ALL" s "SORRY_END_ALL"; ()) | NONE => ();
\<close>

ML \<open>
(* I5: NO instantiation supplied at all -- can the locale parameter survive as a
   schematic Var in the obligation?  (agent's `instantiations` field is optional) *)
val i5 = probe_ml "I5 INTERPRET mylocale, no instantiation" "QQ (?x::nat)" []
           (INTERPRET "mln" "mylocale" []);
\<close>

ML \<open>
(* I6: polymorphic locale, no instantiation -- can a TVar leak into the obligation? *)
val i6 = probe_ml "I6 INTERPRET polyloc, no instantiation" "QQ (?x::nat)" []
           (INTERPRET "plq" "polyloc" []);
\<close>

ML \<open>writeln "======== D: Define on a schematic main goal ========"\<close>

ML \<open>
(* D1: nullary path -> Minilang.DEFINE'' (plain Isar define) *)
val d1 = probe_ml "D1 DEFINE'' nullary" "QQ (?x::nat)" []
  (Minilang.DEFINE'' [(Binding.name "cc0", NONE, NoSyn)]
     [(Binding.empty_atts, [("cc0 = (5::nat)", [])])] []);
val _ = case d1 of SOME s => (probe' "D1b INST_VAR after define" s "INST_VAR ?x = \"7::nat\""; ()) | NONE => ();
\<close>

ML \<open>
(* D2: function path, auto-proved (no deferred block) *)
val d2 = probe_ml "D2 FUN'' auto-proved" "QQ (?x::nat)" []
  (Minilang.FUN'' [(Binding.name "ff2", SOME "nat \<Rightarrow> nat", NoSyn)]
     [((Binding.empty_atts, "ff2 n = n + 2"), [], [])]
     {metric = [], open_on_fail = true});
\<close>

ML \<open>
(* D3: forced deferred pat-completeness block (debug config), main goal has ?x *)
val d3 =
  let val s0 = mk_state "QQ (?x::nat)"
      val s0' = Minilang.map_context
                  (Config.put Minilang.fun_fake_pat_completeness_failure true) s0
  in probe_ml' "D3 FUN'' with forced pat-completeness failure" s0'
       (Minilang.FUN'' [(Binding.name "ff3", SOME "nat \<Rightarrow> nat", NoSyn)]
          [((Binding.empty_atts, "ff3 n = n + 3"), [], [])]
          {metric = [], open_on_fail = true})
  end;
\<close>

ML \<open>
val _ = case d3 of SOME s => (probe' "D3b SORRY_END_ALL then main goal" s "SORRY_END_ALL"; ())
                 | NONE => ();
\<close>

ML \<open>
(* D4: schematic ?x inside the defining equation *)
val d4 = probe_ml "D4 FUN'' equation mentions ?x" "QQ (?x::nat)" []
  (Minilang.FUN'' [(Binding.name "ff4", SOME "nat \<Rightarrow> nat", NoSyn)]
     [((Binding.empty_atts, "ff4 n = n + ?x"), [], [])]
     {metric = [], open_on_fail = true});
\<close>

ML \<open>
(* D5: nullary define whose body mentions ?x *)
val d5 = probe_ml "D5 DEFINE'' body mentions ?x" "QQ (?x::nat)" []
  (Minilang.DEFINE'' [(Binding.name "cc5", NONE, NoSyn)]
     [(Binding.empty_atts, [("cc5 = (?x::nat)", [])])] []);
\<close>

ML \<open>
(* D6: schematic TYPE variable in the main goal, function defined alongside *)
val d6 = probe_ml "D6 FUN'' with ?'a in main goal" "(?f :: ?'a \<Rightarrow> ?'a) x = ?f x" []
  (Minilang.FUN'' [(Binding.name "ff6", SOME "nat \<Rightarrow> nat", NoSyn)]
     [((Binding.empty_atts, "ff6 n = n + 6"), [], [])]
     {metric = [], open_on_fail = true});
\<close>

ML \<open>writeln "======== C: controls for the D3b sorry failure ========"\<close>

ML \<open>
(* D7: CONTROL. Same forced pat-completeness deferral, but a goal with NO
   schematic variable at all.  If SORRY_END_ALL fails here too, the D3b
   failure is a pre-existing FUN-deferred-block defect, not schematic-related. *)
val d7 =
  let val s0 = mk_state' ["m"] "QQ (m::nat)"
      val s0' = Minilang.map_context
                  (Config.put Minilang.fun_fake_pat_completeness_failure true) s0
  in probe_ml' "D7 CONTROL FUN'' forced deferral, no schematic" s0'
       (Minilang.FUN'' [(Binding.name "ff7", SOME "nat \<Rightarrow> nat", NoSyn)]
          [((Binding.empty_atts, "ff7 n = n + 7"), [], [])]
          {metric = [], open_on_fail = true})
  end;
val _ = case d7 of SOME s => (probe' "D7b CONTROL SORRY_END_ALL" s "SORRY_END_ALL"; ())
                 | NONE => ();
\<close>

ML \<open>
(* D8: genuinely DISCHARGE the deferred obligations on a schematic main goal,
   then look at the restored main goal.  This is the close path that matters. *)
val d8 =
  let val s0 = mk_state "QQ (?x::nat)"
      val s0' = Minilang.map_context
                  (Config.put Minilang.fun_fake_pat_completeness_failure true) s0
  in probe_ml' "D8 FUN'' forced deferral on schematic goal" s0'
       (Minilang.FUN'' [(Binding.name "ff8", SOME "nat \<Rightarrow> nat", NoSyn)]
          [((Binding.empty_atts, "ff8 n = n + 8"), [], [])]
          {metric = [], open_on_fail = true})
  end;
val _ = case d8 of SOME s => (probe' "D8b END (really discharge)" s "END"; ()) | NONE => ();
\<close>

end
