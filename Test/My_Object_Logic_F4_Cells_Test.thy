theory My_Object_Logic_F4_Cells_Test
  imports Minilang.Minilang
begin

(* MY_OBJECT_LOGIC_PLAN.md section 8-7, the three F4 matrix cells: paths that
   push a deferred block whose PROTECTED conclusion carries meta connectives.
   The old hardcoded iso conversion was all_conv on a `&&&' head; the ported
   rule-driven one embeds it (pure_conj_embed under Trueprop), and
   finalize_goal must restore the `&&&' before Conjunction.elim_balanced /
   elim_conjunctions splits.  These paths postdate every isoport prototype
   measurement (commit 530281e), hence the dedicated cells.

   Cell 2 (FUN interactive termination) is exercised by RT_Fun_In_Proof_Test
   in the section 8-4 regression (FUN_DEBUG + BY_METRIC blocks); cells 1 and 3
   live here. *)

section \<open>Cell 1: FUN with BOTH obligation phases deferred (merged block)\<close>

(* The fixture of Test_Define_BothPhasesDeferred, driven through min_script
   directly: stripping the datatype's structural rules leaves phase 1
   (pattern completeness/compatibility) residuals; the swapped recursive call
   defeats the default termination prover; `size a` is a real but partial
   metric, so phase 2 leaves one decrease residual.  Expected: ONE block of
   6 + 1 = 7 subgoals; its callback splits the protected `&&&' conclusion. *)

datatype rbz = ZA nat | ZB rbz | ZC rbz
declare rbz.inject[simp del, iff del]
declare rbz.distinct[simp del, iff del]

lemma "(2::nat) = 2"
  by (min_script \<open>
  FUN_DEBUG rsw :: "rbz \<Rightarrow> rbz \<Rightarrow> nat"
    where "rsw (ZA n) y = n"
        | "rsw (ZB x) y = rsw y x"
        | "rsw (ZC x) y = rsw x y"
    BY_METRIC "\<lambda>(a::rbz, b::rbz). size a"
  PRINT
  SORRY SORRY SORRY SORRY SORRY SORRY SORRY
  PRINT
  END
\<close>)

section \<open>Cell 3: INTERPRET (locale interpretation blocks)\<close>

locale withobs = fixes a :: nat assumes obs1: "a > 0" and obs2: "a < 10"
locale emptyloc = fixes b :: nat

ML \<open>
val base_ctxt = Named_Target.theory_init \<^theory>;

fun mk_state prop_str =
  let val t = Syntax.read_prop base_ctxt prop_str
   in Minilang.INIT base_ctxt (Goal.init (Thm.cterm_of base_ctxt t)) end;

fun run script s = Minilang.parse_cmds (Minilang.lex_cmds script) s;

(* build the locale expression exactly the way Agent/agent.ML INTERPRET does *)
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
  end;

fun INTERPRET qualifier locale insts s =
  Minilang.OPEN_MODULE'' {auto_unfold_locale = true}
    (mk_expr (Minilang.context_of s) qualifier locale insts) s;

fun must label f =
  (f (); writeln ("F4-CELL3 " ^ label ^ ": OK"))
  handle Minilang.OPR_FAIL (_, m) => error ("F4-CELL3 " ^ label ^ ": OPR_FAIL " ^ m);

(* with obligations: the block wraps, its conclusion goes through the ported
   iso conversion, and END must restore and register the interpretation *)
val _ = must "withobs SORRY_END_ALL" (fn () =>
  mk_state "(1::nat) = 1"
  |> INTERPRET "wo" "withobs" [("a", "5::nat")]
  |> run "SORRY_END_ALL"
  |> run "HAMMER END");

(* obligation-free locale: the EMPTY goal state `#(\<And>dummy. PROP dummy \<Longrightarrow>
   PROP dummy)` must stay on the unwrapped path (no_subgoal' gate) *)
val _ = must "emptyloc END" (fn () =>
  mk_state "(1::nat) = 1"
  |> INTERPRET "eb" "emptyloc" [("b", "3::nat")]
  |> run "END"
  |> run "HAMMER END");
\<close>

end
