theory Consumes_Validation_Test
  imports Main Minilang.Minilang
begin

text \<open>
  Tests for the Minilang-level INDUCT / CASE_SPLIT consumes validation
  and the `analyze_induct` / `analyze_case_split` analysis interface
  added in `library/proof.ML`.

  Covers:
    A. `Minilang.analyze_induct` on rules with varying `consumes` counts
       (nat.induct = 0, int_le_induct = 1, list_induct2 = 1), and the
       names the analysis reports (MINILANG_SUBGOALS_WITHOUT_CASE_PLAN.md, test 18).
    B. `Minilang.analyze_case_split` on nat.exhaust, list auto-pick, and a consuming rule.
    C. INDUCT via `min_script` — success with correct rule+facts.
    D. INDUCT under `require` — error when no fact fills the consuming premise.
    E. The policy config and its decisions.
    F. Edge cases.
\<close>

ML \<open>
structure CVT =
struct
(*a Minilang state on a goal whose variables are fixed as in a lemma's proof*)
fun state ctxt prop =
  let
    val read_ctxt = ctxt |> String.isSubstring "?" prop ?
                      Proof_Context.set_mode Proof_Context.mode_schematic
    val t = Syntax.read_prop read_ctxt prop
    val frees = rev (Term.add_frees t [])
    val (xs, ctxt') = ctxt |> Variable.set_body true
      |> Proof_Context.add_fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) frees)
    val t' = subst_free (map Free frees ~~ map2 (fn x => fn (_, T) => Free (x, T)) xs frees) t
  in (ctxt', Minilang.INIT ctxt' (Goal.init (Thm.cterm_of ctxt' t'))) end
fun str ctxt t = Print_Mode.setmp [] (Syntax.string_of_term ctxt) t
fun expect label b msg = if b then writeln ("  " ^ label ^ ": OK") else error (label ^ ": " ^ msg)
(*rule name, consumes, consume premises, the schematic variables in them*)
fun summary ctxt NONE = ("NONE", ~1, [], [])
  | summary ctxt (SOME ({rule_name, consumes, consume_premises, ...} : Minilang.induct_analysis)) =
      (the_default "<anon>" rule_name, consumes, map (str ctxt) consume_premises,
       fold Term.add_vars consume_premises [] |> rev
       |> map (fn (xi, T) => Term.string_of_vname xi ^ " :: " ^
                              Print_Mode.setmp [] (Syntax.string_of_typ ctxt) T))
fun show (name, c, prems, vars) =
  name ^ ", consumes " ^ string_of_int c ^ ", [" ^ commas prems ^ "], [" ^ commas vars ^ "]"
end
\<close>

section \<open>A. analyze_induct --- rule discovery + consumes reporting\<close>

ML \<open>
local
  fun induct label prop target rule expected =
    let val (ctxt, s) = CVT.state \<^context> prop
        val got = CVT.summary ctxt (Minilang.analyze_induct s (Syntax.read_term ctxt target) rule)
     in CVT.expect label (got = expected) (CVT.show got) end
in
  val _ = induct "A1 nat.induct" "P (n::nat)" "n" (SOME @{thms nat.induct})
            ("Nat.nat.induct", 0, [], [])
  val _ = induct "A2 int_le_induct" "P (i::int)" "i" (SOME @{thms int_le_induct})
            ("Int.int_le_induct", 1, ["i \<le> ?k"], ["?k :: int"])
  val _ = induct "A3 list_induct2" "P (xs::'a list) (ys::'b list)" "xs" (SOME @{thms list_induct2})
            (*the method also unifies the rule with the goal: no variable is left*)
            ("List.list_induct2", 1, ["length ys = length xs"], [])
  val _ = induct "A4 auto-pick nat" "P (n::nat)" "n" NONE ("Nat.nat_induct", 0, [], [])
  (*renaming the parameters after the target drops the name, in Isabelle as in the mirror*)
  val _ = induct "A5 auto-pick list" "P (xs::'a list)" "xs" NONE ("<anon>", 0, [], [])
  (*the reported names are the rule's: the method takes the rule on a goal of maxidx ~1*)
  val _ = induct "A6 target i + j" "P (i + j::int)" "i + j" (SOME @{thms int_le_induct})
            ("Int.int_le_induct", 1, ["i + j \<le> ?k"], ["?k :: int"])
  val _ = induct "A7 a goal with j" "P (i::int) (j::int)" "i" (SOME @{thms int_le_induct})
            ("Int.int_le_induct", 1, ["i \<le> ?k"], ["?k :: int"])
  val _ = induct "A8 a schematic goal" "P (i::int) ?w" "i" (SOME @{thms int_le_induct})
            ("Int.int_le_induct", 1, ["i \<le> ?k"], ["?k :: int"])
end
\<close>

section \<open>B. analyze_case_split\<close>

lemma lt_cases [consumes 2]: "(x::nat) < y \<Longrightarrow> y < z \<Longrightarrow> (x < z \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

ML \<open>
local
  fun cases label prop target rule expected =
    let val (ctxt, s) = CVT.state \<^context> prop
        val got = CVT.summary ctxt (Minilang.analyze_case_split s (Syntax.read_term ctxt target) rule)
     in CVT.expect label (got = expected) (CVT.show got) end
in
  val _ = cases "B1 nat.exhaust" "P (n::nat)" "n" (SOME @{thm nat.exhaust})
            ("Nat.nat.exhaust", 0, [], [])
  val _ = cases "B2 auto-pick cases on list" "P (xs::'a list)" "xs" NONE
            ("<anon>", 0, [], [])
  (*a consuming rule: the analysis runs the rule given*)
  val _ = cases "B3 consuming rule" "P (x::nat)" "x" (SOME @{thm lt_cases})
            ("Consumes_Validation_Test.lt_cases", 2, ["x < ?y", "?y < ?z"],
             ["?y :: nat", "?z :: nat"])
end
\<close>

section \<open>C. INDUCT success via min_script\<close>

text \<open>Sanity checks that the refactored INDUCT still works with simple
      auto-pick rules (consumes = 0, no `using` facts needed).\<close>

lemma rev_rev: "rev (rev l) = l"
  by (min_script \<open>INDUCT l NEXT END\<close>)

lemma append_Nil: "xs @ [] = xs"
  by (min_script \<open>INDUCT xs NEXT SIMP END\<close>)

text \<open>Explicit rule with consumes = 1 + a \<open>WITH\<close> clause. Verifies the
      consumes validation does NOT reject a correct call.
      Note: Minilang's INDUCT reads `using` facts from its own \<open>WITH\<close>
      clause, NOT from the Isar \<open>using\<close> prelude, so \<open>le\<close> must be passed
      via \<open>WITH le\<close>.\<close>

lemma int_le_demo:
  fixes i k :: int
  assumes le: "i \<le> k"
  shows "(i::int) + k \<ge> 2 * i"
  by (min_script \<open>INDUCT i rule: int_le_induct WITH le NEXT NEXT END\<close>)

declare [[consumes_policy = "subgoals"]]

lemma int_le_demox:
  fixes i k :: int
  assumes le: "i \<le> k"
  shows "(i::int) + k \<ge> 2 * i"
thm int_le_induct[where ?k = \<open>k\<close>]
  by (min_script \<open>INDUCT i rule: int_le_induct[where ?k = \<open>k\<close>] PRINT NEXT NEXT PRINT END\<close>)
thm int_le_induct


section \<open>D. INDUCT under require --- no fact for the consuming premise\<close>

ML \<open>
local
  fun outcome policy cmd =
    let val (ctxt, s) = CVT.state (Config.put Minilang.consumes_policy policy \<^context>) "P (i::int)"
     in (Minilang.parse_cmds (Minilang.lex_cmds cmd) s; "proceed")
        handle Minilang.OPR_FAIL (_, msg) => msg
    end
in
  val _ = writeln "### D1: int_le_induct with no fact"
  val _ = CVT.expect "D1"
            (outcome "require" "INDUCT i rule: int_le_induct[where k = 5]" =
             "Induction rule `<auto-picked rule>` has 1 consuming premise, but no fact was given \
             \after `WITH`.")
            (outcome "require" "INDUCT i rule: int_le_induct[where k = 5]")

end
\<close>


section \<open>E. Policy \<open>consumes_policy\<close> --- string-valued config\<close>

text \<open>Verify \<open>consumes_policy\<close> is accessible and the theory-level
      default is \<open>"require"\<close>. The AoA agent applies
      \<open>"subgoals"\<close> per-session in \<open>agent_server.ML\<close> via \<open>Config.put\<close>, not
      as a theory-wide \<open>declare\<close>, so theories that merely import
      \<open>Minilang_AoA\<close> still see the stock default here.\<close>

ML \<open>
local
  (*section C declares "subgoals" for this theory: the default is read in Minilang's*)
  val default_val =
    Config.get (Proof_Context.init_global \<^theory>\<open>Minilang\<close>) Minilang.consumes_policy
in
  val _ = writeln "### E1: consumes_policy default"
  val _ = CVT.expect "E1" (default_val = "require") default_val
end
\<close>

section \<open>E2. Policy \<open>subgoals\<close> vs \<open>require\<close> vs \<open>strict\<close> --- same call, different outcomes\<close>

ML \<open>
local
  fun outcome policy cmd =
    let val (ctxt, s) = CVT.state (Config.put Minilang.consumes_policy policy \<^context>) "P (i::int)"
     in (Minilang.parse_cmds (Minilang.lex_cmds cmd) s; "proceed")
        handle Minilang.OPR_FAIL (_, msg) => msg
    end
  val cmd = "INDUCT i rule: int_le_induct[where k = 5]"
in
  val _ = writeln "### E2: decisions with no fact for int_le_induct (consumes 1)"
  val _ = CVT.expect "E2 require" (outcome "require" cmd <> "proceed") (outcome "require" cmd)
  val _ = CVT.expect "E2 subgoals" (outcome "subgoals" cmd = "proceed") (outcome "subgoals" cmd)
  val _ = CVT.expect "E2 strict" (outcome "strict" cmd <> "proceed") (outcome "strict" cmd)
end
\<close>


section \<open>F. Edge case --- no rule found\<close>

ML \<open>
local
  val (ctxt, s) = CVT.state \<^context> "P (b::bool)"
  val result = Minilang.analyze_induct s (Syntax.read_term ctxt "b") NONE
in
  val _ = writeln "### F1: analyze_induct on a bool target"
  val _ = writeln ("  F1: " ^ CVT.show (CVT.summary ctxt result))
end
\<close>

end
