theory Subgoals_Without_Case_Test
  imports Minilang.Minilang
begin

text \<open>
  CASE_SPLIT and INDUCT with subgoals no case describes
  (ai-artifacts/MINILANG_SUBGOALS_WITHOUT_CASE_PLAN.md, section 7), on stock Isabelle.
  Each check that fails is collected; the last ML block fails with all of them.
\<close>

declare [[quick_and_dirty]]

ML \<open>
structure SWC =
struct

fun str ctxt t = Print_Mode.setmp [] (Syntax.string_of_term ctxt) t

type block = {name: string, fixes: string list, facts: (string * string) list, goal: string}

(*a goal as in a lemma's proof: its variables fixed (internal names), the assumptions named
  facts; schematic variables in the goal stay*)
fun setup ctxt policy prop assms =
  let
    val ctxt0 = Config.put Minilang.consumes_policy policy ctxt
    (*schematic mode only for a goal with ?-variables: it leaves implicit types schematic*)
    val read_ctxt = ctxt0 |> String.isSubstring "?" prop ?
                      Proof_Context.set_mode Proof_Context.mode_schematic
    val ts = Syntax.read_props read_ctxt (prop :: map #2 assms)
    val frees = rev (fold Term.add_frees ts [])
    val (xs, ctxt1) = ctxt0 |> Variable.set_body true
      |> Proof_Context.add_fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) frees)
    val ren = subst_free (map Free frees ~~ map2 (fn x => fn (_, T) => Free (x, T)) xs frees)
    val (goal, hyps) = (case map ren ts of t :: ts' => (t, ts') | [] => raise Match)
    val (ths, ctxt2) = Assumption.add_assumes (map (Thm.cterm_of ctxt1) hyps) ctxt1
    val ctxt3 = fold2 (fn (name, _) => fn th =>
                  Proof_Context.note_thms "" ((Binding.name name, []), [([th], [])]) #> #2)
                  assms ths ctxt2
  in (ctxt3, Goal.init (Thm.cterm_of ctxt3 goal)) end

(*every block the commands open: its name, fixes, facts (name, text), goal; and the last state.
  Commands after the proof is finished are skipped.*)
fun run (ctxt, st) cmds =
  fold (fn cmd => fn (s, acc) => if Minilang.is_finished s then (s, acc) else
    let val (s', msgs) = Minilang.record_reporter
                           (Minilang.parse_cmds (Minilang.lex_cmds cmd)) s
        val ctxt' = Minilang.context_of s'
        val goal = (case Minilang.leading_goal_data s' of
                      (SOME (_, g), _) => str ctxt' g | _ => "<none>")
        val opened = map_filter (fn Minilang.Consider_Case (n, (fixes, facts)) =>
                       SOME ({name = n, fixes = map #1 fixes,
                              facts = map (fn (a, t) => (a, str ctxt' t)) facts, goal = goal}
                             : block)
                     | _ => NONE) msgs
     in (s', acc @ opened) end) cmds (Minilang.INIT ctxt st, [])
  |> swap

(*the new subgoals a command reports (its Goals message), as text*)
fun reported_goals (ctxt, st) cmd =
  let val (s, msgs) = Minilang.record_reporter (Minilang.parse_cmds (Minilang.lex_cmds cmd))
                        (Minilang.INIT ctxt st)
   in (case get_first (fn Minilang.Goals gs => SOME gs | _ => NONE) msgs of
         SOME gs => map (str (Minilang.context_of s)) gs
       | NONE => [])
  end

val failures = Unsynchronized.ref ([] : string list)
fun fail label msg = failures := (label ^ ": " ^ msg) :: ! failures
fun check label b msg = if b then () else fail label msg

fun blocks label su cmds =
  (case Exn.capture (run su) cmds of
    Exn.Res (bs, _) => SOME bs
  | Exn.Exn exn => (fail label ("raised " ^ Runtime.exn_message exn); NONE))

fun show_blocks bs =
  space_implode " | " (map (fn {name, facts, goal, ...} =>
    name ^ " [" ^ commas (map #1 facts) ^ "] " ^ goal) bs)

(*the names of the blocks, in order*)
fun expect_names label su cmds names =
  (case blocks label su cmds of
    SOME bs => check label (map #name bs = names) ("got " ^ show_blocks bs)
  | NONE => ())

(*the names and goals of the blocks*)
fun expect_goals label su cmds expected =
  (case blocks label su cmds of
    SOME bs => check label (map (fn b => (#name b, #goal b)) bs = expected)
                 ("got " ^ show_blocks bs)
  | NONE => ())

fun expect_error label su cmds msg =
  (case Exn.capture (run su) cmds of
    Exn.Res (bs, _) => fail label ("no failure; blocks " ^ show_blocks bs)
  | Exn.Exn (Minilang.OPR_FAIL (_, m)) => check label (m = msg) ("message: " ^ m)
  | Exn.Exn exn => fail label ("raised " ^ Runtime.exn_message exn))

(*a Minilang failure whose message starts with the given text*)
fun expect_error_prefix label su cmds msg =
  (case Exn.capture (run su) cmds of
    Exn.Res (bs, _) => fail label ("no failure; blocks " ^ show_blocks bs)
  | Exn.Exn (Minilang.OPR_FAIL (_, m)) => check label (String.isPrefix msg m) ("message: " ^ m)
  | Exn.Exn exn => fail label ("raised " ^ Runtime.exn_message exn))

(*a failure Isabelle itself raises*)
fun expect_raise label su cmds msg =
  (case Exn.capture (run su) cmds of
    Exn.Res (bs, _) => fail label ("no failure; blocks " ^ show_blocks bs)
  | Exn.Exn exn => check label (String.isSubstring msg (Runtime.exn_message exn))
                     ("raised " ^ Runtime.exn_message exn))

(*the case names and fixes Isar's own method gives, by a context tactic on the same goal*)
fun isar_cases (ctxt, st) tac =
  (case Seq.pull (tac (ctxt, st)) of
    SOME (Seq.Result (ctxt', _), _) =>
      Proof_Context.dest_cases (SOME ctxt) ctxt'
      |> map (fn (n, Rule_Cases.Case {fixes, ...}) => (n, map (Binding.name_of o #1) fixes))
  | _ => error "Isar's method failed")

fun isar label su tac =
  (case Exn.capture (isar_cases su) tac of
    Exn.Res cs => SOME cs
  | Exn.Exn exn => (fail label ("Isar: " ^ Runtime.exn_message exn); NONE))

fun read ctxt s = Syntax.read_term ctxt s

fun report () =
  if null (! failures) then writeln "Subgoals_Without_Case_Test: all checks passed"
  else error (cat_lines ("Subgoals_Without_Case_Test failures:" :: rev (! failures)))

end
\<close>

section \<open>Fixtures\<close>

consts p :: "nat \<Rightarrow> bool" q :: bool s :: bool s2 :: bool r :: "nat \<Rightarrow> bool"
  q2 :: "nat \<Rightarrow> bool" p2 :: "nat \<Rightarrow> nat \<Rightarrow> bool" r2 :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  f :: "nat \<Rightarrow> nat" A :: bool B :: bool C :: "nat \<Rightarrow> bool"

inductive ev :: "nat \<Rightarrow> bool" where
  zero: "ev 0"
| step: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma two_prems [consumes 2, case_names a b]:
  "(x::nat) < y \<Longrightarrow> y < z \<Longrightarrow> (x < z \<Longrightarrow> P) \<Longrightarrow> (z \<noteq> x \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma param_prem [consumes 1, case_names c]:
  "(\<And>x::nat. C x \<Longrightarrow> p x) \<Longrightarrow> ((\<forall>x. C x \<longrightarrow> p x) \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma c8e [consumes 1, case_names a]: "p x \<Longrightarrow> (q \<Longrightarrow> r x) \<Longrightarrow> r x" sorry
lemma c8e' [consumes 1, case_names a]: "p2 y x \<Longrightarrow> (q \<Longrightarrow> r x) \<Longrightarrow> r x" sorry
lemma c8f [consumes 1, case_names a]: "p x \<Longrightarrow> (q2 x \<Longrightarrow> r x) \<Longrightarrow> r x" sorry
lemma c8f' [consumes 1, case_names a]: "p2 y x \<Longrightarrow> (q2 x \<Longrightarrow> r x) \<Longrightarrow> r x" sorry
lemma c8g [case_names a b]: "p x \<Longrightarrow> r (f x) \<Longrightarrow> r x" sorry
lemma i8h [case_names a]: "(q2 x \<Longrightarrow> r x) \<Longrightarrow> r x" sorry
lemma c8i [case_names a]: "(s \<Longrightarrow> R) \<Longrightarrow> (q2 y \<Longrightarrow> R) \<Longrightarrow> R" sorry
lemma c8i2 [consumes 1, case_names a]:
  "p x \<Longrightarrow> (q \<Longrightarrow> r x) \<Longrightarrow> (q2 y \<Longrightarrow> r x) \<Longrightarrow> r x" sorry
lemma c8i3 [consumes 1, case_names a b]:
  "p x \<Longrightarrow> (q \<Longrightarrow> r x) \<Longrightarrow> (q2 y \<Longrightarrow> r x) \<Longrightarrow> r x" sorry
lemma c8j [consumes 1, case_names a]: "p x \<Longrightarrow> (q \<Longrightarrow> r2 x y) \<Longrightarrow> r2 x y" sorry
lemma c8k: "(s \<Longrightarrow> P) \<Longrightarrow> P" sorry
lemma c8l [case_names a]: "(s \<Longrightarrow> P) \<Longrightarrow> (\<not> s \<Longrightarrow> P) \<Longrightarrow> P" by blast
lemma c8m [consumes 1, case_names a]: "p k \<Longrightarrow> (q \<Longrightarrow> r m) \<Longrightarrow> r m" sorry
lemma hv_fact: "q2 z \<Longrightarrow> ev 4" sorry
lemma c8n [case_names a, constraints 1]:
  "(y = Suc 0 \<Longrightarrow> r x) \<Longrightarrow> (y = 0 \<Longrightarrow> r x) \<Longrightarrow> (y = Suc 0 \<Longrightarrow> r (f x)) \<Longrightarrow> r x"
  sorry

inductive fp :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "fp id"
lemma r13 [consumes 1]: "p x \<Longrightarrow> (q \<Longrightarrow> P) \<Longrightarrow> (s \<Longrightarrow> P) \<Longrightarrow> P" sorry
lemma two_cons2 [consumes 2, case_names a]: "p x \<Longrightarrow> q2 x \<Longrightarrow> (q \<Longrightarrow> P) \<Longrightarrow> P" sorry
lemma three_cons [consumes 3, case_names a]: "p x \<Longrightarrow> q2 x \<Longrightarrow> s \<Longrightarrow> (q \<Longrightarrow> P) \<Longrightarrow> P" sorry


section \<open>1--3: unfilled consuming premises open leading Prem blocks\<close>

ML \<open>
val su = SWC.setup \<^context> "subgoals" "Q (i::int)" []
val _ = SWC.expect_goals "1 int_le_induct[where k = 5]" su
          ["INDUCT i rule: int_le_induct[where k = 5]", "SORRY", "SORRY", "SORRY"]
          [("Prem0", "i \<le> 5"), ("base", "Q 5"), ("step", "Q (i - 1)")]
val _ = (case SWC.blocks "1 step facts" su
                ["INDUCT i rule: int_le_induct[where k = 5]", "SORRY", "SORRY"] of
           SOME [_, _, b] => SWC.check "1 step facts" (map #1 (#facts b) = ["step.hyps", "step.IH"])
                               (commas (map #1 (#facts b)))
         | _ => SWC.fail "1 step facts" "wrong blocks")
val _ = SWC.expect_error "1 uninstantiated" su ["INDUCT i rule: int_le_induct"]
          "Schematic variable ?k must be instantiated."

val su = SWC.setup \<^context> "subgoals" "R (x::'a) (y::'a)" []
val _ = SWC.expect_names "2 rtranclE" su
          ["CASE_SPLIT rule: rtranclE[where a = x and b = y and r = S]", "SORRY", "SORRY", "SORRY"]
          ["Prem0", "base", "step"]
val _ = SWC.expect_error "2 uninstantiated" su ["CASE_SPLIT rule: rtranclE"]
          "Schematic variables ?a, ?b, ?r, ?'a must be instantiated."

val su = SWC.setup \<^context> "subgoals" "R (x::nat) y z" [("h", "y < (z::nat)")]
val _ = SWC.expect_goals "3 two consuming premises" su
          ["CASE_SPLIT rule: two_prems[where x = x and y = y and z = z]", "SORRY", "SORRY", "SORRY",
           "SORRY"]
          [("Prem0", "x < y"), ("Prem1", "y < z"), ("a", "R x y z"), ("b", "R x y z")]
val _ = SWC.expect_goals "3 WITH _ h" su
          ["CASE_SPLIT rule: two_prems[where x = x] WITH _ h", "SORRY", "SORRY", "SORRY"]
          [("Prem0", "x < y"), ("a", "R x y z"), ("b", "R x y z")]
\<close>


section \<open>4--5: premises of given facts, premises with parameters\<close>

ML \<open>
fun t4 policy =
  let val su = SWC.setup \<^context> policy "Q (n::nat)" [("h", "A \<Longrightarrow> ev n")]
      val label = "4 (" ^ policy ^ ") "
   in SWC.expect_names (label ^ "CASE_SPLIT") su
        ["CASE_SPLIT n rule: ev.cases WITH h", "SORRY", "SORRY", "SORRY"] ["Prem0", "zero", "step"];
      SWC.expect_goals (label ^ "INDUCT") su ["INDUCT n WITH h", "SORRY", "SORRY", "SORRY"]
        [("Prem0", "A"), ("zero", "Q 0"), ("step", "Q (Suc (Suc n))")];
      (case SWC.blocks (label ^ "INDUCT facts") su ["INDUCT n WITH h", "SORRY", "SORRY"] of
        SOME [_, _, b] => SWC.check (label ^ "INDUCT facts")
                            (map #1 (#facts b) = ["step.hyps", "step.IH"]) (commas (map #1 (#facts b)))
      | _ => SWC.fail (label ^ "INDUCT facts") "wrong blocks")
  end
val _ = t4 "subgoals"
val _ = t4 "require"

val su = SWC.setup \<^context> "subgoals" "Q (n::nat)" []
val _ = (case SWC.blocks "5 parameter premise" su ["CASE_SPLIT rule: param_prem", "SORRY", "SORRY"] of
          SOME [b0, b1] => SWC.check "5 parameter premise"
              (#name b0 = "Prem0" andalso length (#fixes b0) = 1 andalso length (#facts b0) = 1
               andalso #name b1 = "c")
              (SWC.show_blocks [b0, b1])
        | SOME bs => SWC.fail "5 parameter premise" (SWC.show_blocks bs)
        | NONE => ())
\<close>


section \<open>6--7: targets that are not variables, arbitrary, earlier steps\<close>

ML \<open>
val su = SWC.setup \<^context> "subgoals" "Q (i + j::int)" []
val _ = SWC.expect_names "6 non-variable target" su
          ["INDUCT \"i + j\" rule: int_le_induct[where k = 5]", "SORRY", "SORRY", "SORRY"]
          ["Prem0", "base", "step"]
val _ = SWC.expect_error "6 uninstantiated" su ["INDUCT \"i + j\" rule: int_le_induct"]
          "Schematic variable ?k must be instantiated."

val su = SWC.setup \<^context> "subgoals" "Q (i::int) (x::nat)" []
val _ = SWC.expect_goals "7 arbitrary" su
          ["INDUCT i arbitrary: x rule: int_le_induct[where k = 5]", "SORRY", "SORRY", "SORRY"]
          [("Prem0", "i \<le> 5"), ("base", "Q 5 x"), ("step", "Q (i - 1) x")]
val _ = (case SWC.blocks "7 arbitrary: generalized" su
                ["INDUCT i arbitrary: x rule: int_le_induct[where k = 5]", "SORRY", "SORRY", "SORRY"] of
          SOME [b0, _, b2] =>
            SWC.check "7 arbitrary: generalized"
              (null (#fixes b0) andalso member (op =) (#fixes b2) "x" andalso
               AList.lookup (op =) (#facts b2) "step.IH" = SOME "Q i ?x")
              (SWC.show_blocks [b0, b2])
        | SOME bs => SWC.fail "7 arbitrary: generalized" (SWC.show_blocks bs)
        | NONE => ())
val _ = SWC.expect_error "7 arbitrary uninstantiated" su
          ["INDUCT i arbitrary: x rule: int_le_induct"]
          "Schematic variable ?k must be instantiated."
val su = SWC.setup \<^context> "subgoals" "(q \<longrightarrow> R (i::int)) \<and> s" []
val _ = SWC.expect_error "7 after RULE" su
          ["RULE conjI", "INDUCT i rule: int_le_induct"]
          "Schematic variable ?k must be instantiated."
\<close>


section \<open>8: rejected at command time, and accepted\<close>

ML \<open>
val su = SWC.setup \<^context> "subgoals" "Q (n::nat)" [("h", "ev n")]
val msg1 = "`_` cannot be the first fact after `WITH` unless you indicate the rule by the \
           \`rule:` clause."
val _ = SWC.expect_error "8 _ first, CASE_SPLIT" su ["CASE_SPLIT n WITH _"] msg1
val _ = SWC.expect_error "8 _ first, INDUCT" su ["INDUCT n WITH _ h"] msg1
fun msg2 policy = "`_` is not allowed under `consumes_policy = " ^ policy ^ "`; give the fact, \
                  \or set `consumes_policy` to `subgoals`."
val _ = SWC.expect_error "8 _ under require" (SWC.setup \<^context> "require" "Q (n::nat)" [])
          ["CASE_SPLIT n rule: ev.cases WITH _"] (msg2 "require")
val _ = SWC.expect_error "8 _ under strict" (SWC.setup \<^context> "strict" "Q (n::nat)" [])
          ["INDUCT n rule: ev.induct WITH _"] (msg2 "strict")
(*_ beyond the consuming premises: dropped*)
val with_h = SWC.blocks "8 _ beyond c (reference)" su ["CASE_SPLIT n WITH h", "SORRY", "SORRY"]
val with_h_ = SWC.blocks "8 _ beyond c" su ["CASE_SPLIT n WITH h _", "SORRY", "SORRY"]
val _ = SWC.check "8 _ beyond c" (with_h = with_h_ andalso is_some with_h)
          (case with_h_ of SOME bs => SWC.show_blocks bs | NONE => "")
val with_h_i = SWC.blocks "8 _ beyond c, INDUCT" su ["INDUCT n WITH h _", "SORRY", "SORRY"]
val with_h_i' = SWC.blocks "8 _ beyond c, INDUCT (reference)" su ["INDUCT n WITH h", "SORRY", "SORRY"]
val _ = SWC.check "8 _ beyond c, INDUCT" (with_h_i = with_h_i' andalso is_some with_h_i)
          (case with_h_i of SOME bs => SWC.show_blocks bs | NONE => "")
(*nothing of the dropped _ reaches the new subgoals*)
fun same_goals label cmd cmd' =
  (case (Exn.capture (SWC.reported_goals su) cmd, Exn.capture (SWC.reported_goals su) cmd') of
    (Exn.Res gs, Exn.Res gs') =>
      SWC.check label (gs = gs' andalso not (null gs) andalso
                       not (exists (String.isSubstring "?psi") gs'))
        (commas gs' ^ " against " ^ commas gs)
  | (Exn.Exn exn, _) => SWC.fail label ("raised " ^ Runtime.exn_message exn)
  | (_, Exn.Exn exn) => SWC.fail label ("raised " ^ Runtime.exn_message exn))
val _ = same_goals "8 _ beyond c, subgoals" "CASE_SPLIT n WITH h" "CASE_SPLIT n WITH h _"
val _ = same_goals "8 _ beyond c, INDUCT subgoals" "INDUCT n WITH h" "INDUCT n WITH h _"

(*a block with the goal's own schematic variable*)
val suw = SWC.setup \<^context> "subgoals" "r ?w" []
val _ = SWC.expect_error "8 Prem with the goal's ?w" suw ["CASE_SPLIT rule: c8e"]
          "Schematic variable ?w must be instantiated."
val _ = SWC.expect_error "8 Prem with the goal's ?w, target" (SWC.setup \<^context> "subgoals" "r ?w \<and> p t" [])
          ["RULE conjI", "CASE_SPLIT t rule: c8e'"] "Schematic variable ?w must be instantiated."
(*a stored case with a variable in its hypotheses*)
val sut = SWC.setup \<^context> "subgoals" "r t" []
val _ = SWC.expect_error "8 stored case hyp" sut ["CASE_SPLIT rule: c8f"]
          "Schematic variable ?x must be instantiated."
val _ = SWC.expect_error "8 stored case hyp, target" sut ["CASE_SPLIT t rule: c8f'"]
          "Schematic variable ?x must be instantiated."
(*a stored case whose goal has a variable and is not the rule's conclusion*)
val _ = SWC.expect_error "8 stored case goal" sut ["CASE_SPLIT rule: c8g"]
          "Schematic variable ?x must be instantiated."
val _ = SWC.expect_error "8 stored case goal, require" (SWC.setup \<^context> "require" "r t" [])
          ["CASE_SPLIT rule: c8g"] "Schematic variable ?x must be instantiated."
(*the goal's own variable in a stored case's hypotheses*)
val _ = SWC.expect_error "8 goal's ?w in a case hyp" suw ["INDUCT rule: i8h"]
          "Schematic variable ?w must be instantiated."
val _ = SWC.expect_error "8 INDUCT on a schematic goal"
          (SWC.setup \<^context> "subgoals" "p2 n ?w" []) ["INDUCT n"]
          "Schematic variable ?w must be instantiated."
(*tail Prem blocks*)
val _ = SWC.expect_error "8 tail block" (SWC.setup \<^context> "subgoals" "R" [])
          ["CASE_SPLIT rule: c8i"] "Schematic variable ?y must be instantiated."
val sut' = SWC.setup \<^context> "subgoals" "r t" [("hp", "p t")]
val _ = SWC.expect_error "8 tail block after a fact" sut' ["CASE_SPLIT rule: c8i2 WITH hp"]
          "Schematic variable ?y must be instantiated."
val _ = SWC.expect_error "8 named case after a fact" sut' ["CASE_SPLIT rule: c8i3 WITH hp"]
          "Schematic variable ?y must be instantiated."
(*simp closes the first tail case premise (Suc 0 = 0); the one left cannot be told from it:
  rejected*)
val _ = SWC.expect_error "8 tail block, simp closed one" suw ["CASE_SPLIT \"Suc 0\" rule: c8n"]
          "Schematic variable ?w must be instantiated."
(*accepted*)
val _ = SWC.expect_goals "8 accepted: case goal is the rule's conclusion" sut
          ["CASE_SPLIT rule: c8e", "SORRY", "SORRY"] [("Prem0", "p t"), ("a", "r t")]
val _ = (case Exn.capture (SWC.run sut) ["CASE_SPLIT rule: c8e", "SORRY", "SORRY"] of
          Exn.Res (_, s) => SWC.check "8 accepted: closed" (Minilang.is_finished s) "not finished"
        | Exn.Exn exn => SWC.fail "8 accepted: closed" (Runtime.exn_message exn))
val _ = SWC.expect_goals "8 accepted: exception by the copy" 
          (SWC.setup \<^context> "require" "r2 t u" [("h", "p t")])
          ["CASE_SPLIT t rule: c8j WITH h", "SORRY"] [("a", "r2 t u")]
val _ = SWC.expect_names "8 accepted: single ?P case on r ?w" suw
          ["CASE_SPLIT rule: c8k", "SORRY"] ["1"]
val _ = SWC.expect_goals "8 accepted: tail ?P block on r ?w" suw
          ["CASE_SPLIT rule: c8l", "SORRY", "SORRY"] [("a", "r ?w"), ("Prem0", "r ?w")]
(*the goal's ?k and the rule's unfilled ?k*)
val _ = SWC.expect_error "8 goal's ?k and rule's ?k" (SWC.setup \<^context> "subgoals" "r ?k" [])
          ["CASE_SPLIT rule: c8m"] "Schematic variable ?k must be instantiated."
\<close>


section \<open>9: require and strict\<close>

ML \<open>
(*extra facts are inserted, not consumed*)
fun t9 policy =
  let val su = SWC.setup \<^context> policy "Q (n::nat)" [("h", "ev n"), ("e", "A \<Longrightarrow> B")]
      val label = "9 extra fact (" ^ policy ^ ") "
      fun has_B (b : SWC.block) =
        exists (fn (_, t) => String.isSubstring "B" t) (#facts b)
   in (case SWC.blocks (label ^ "INDUCT") su ["INDUCT n WITH h e", "SORRY", "SORRY"] of
         SOME bs => SWC.check (label ^ "INDUCT")
                      (map #name bs = ["zero", "step"] andalso forall has_B bs) (SWC.show_blocks bs)
       | NONE => ());
      (case SWC.blocks (label ^ "CASE_SPLIT") su ["CASE_SPLIT n WITH h e", "SORRY", "SORRY"] of
         SOME bs => SWC.check (label ^ "CASE_SPLIT")
                      (map #name bs = ["zero", "step"] andalso not (exists has_B bs))
                      (SWC.show_blocks bs)
       | NONE => ())
  end
val _ = t9 "require"
val _ = t9 "subgoals"

val _ = SWC.expect_error "9 require: nat.exhaust without target"
          (SWC.setup \<^context> "require" "p n" []) ["CASE_SPLIT rule: nat.exhaust"]
          "Schematic variable ?y must be instantiated."
val _ = SWC.expect_error "9 require: a fact's premise with a variable"
          (SWC.setup \<^context> "require" "p 4" []) ["CASE_SPLIT rule: ev.cases WITH hv_fact"]
          "Schematic variable ?z1 must be instantiated."

val sur = SWC.setup \<^context> "require" "Q (n::nat)" [("h", "p n"), ("h2", "q2 n")]
val _ = SWC.expect_error "9 require c=1 u=0" sur ["CASE_SPLIT n rule: ev.cases"]
          "Case-split rule `Subgoals_Without_Case_Test.ev.cases` has 1 consuming premise, but no \
          \fact was given after `WITH`."
val _ = SWC.expect_error "9 require c=2 u=1" sur ["CASE_SPLIT rule: two_cons2 WITH h"]
          "Case-split rule `Subgoals_Without_Case_Test.two_cons2` has 2 consuming premises, but \
          \only 1 fact was given after `WITH`."
val _ = SWC.expect_error "9 require c=3 u=2" sur ["CASE_SPLIT rule: three_cons WITH h h2"]
          "Case-split rule `Subgoals_Without_Case_Test.three_cons` has 3 consuming premises, but \
          \only 2 facts were given after `WITH`."
val sus = SWC.setup \<^context> "strict" "Q (n::nat)" [("h", "ev n"), ("h2", "q2 n")]
val _ = SWC.expect_error "9 strict c=1 u=2" sus ["INDUCT n rule: ev.induct WITH h h2"]
          "Induction rule `Subgoals_Without_Case_Test.ev.induct` consumes 1 fact, but 2 were given \
          \after `WITH`."
val _ = SWC.expect_error "9 strict c=2 u=1" sus ["CASE_SPLIT rule: two_cons2 WITH h"]
          "Case-split rule `Subgoals_Without_Case_Test.two_cons2` consumes 2 facts, but 1 was \
          \given after `WITH`."
(*no `rule:`: the first candidate's count stops the command*)
val _ = SWC.expect_error "9 strict, no rule:" sus ["INDUCT n WITH h h2"]
          "Induction rule `Subgoals_Without_Case_Test.ev.inducts` consumes 1 fact, but 2 were given \
          \after `WITH`."
val _ = SWC.expect_error "9 strict c=1 u=0" sus ["CASE_SPLIT n rule: ev.cases"]
          "Case-split rule `Subgoals_Without_Case_Test.ev.cases` consumes 1 fact, but no fact was \
          \given after `WITH`."
\<close>

section \<open>Fixtures for 10--17\<close>

inductive vr :: "nat \<Rightarrow> bool" where
  named: "vr 0"
| "vr n \<Longrightarrow> vr (Suc n)"

inductive vr2 :: "nat \<Rightarrow> bool" where
  "vr2 0"
| named: "vr2 n \<Longrightarrow> vr2 (Suc n)"

inductive vr3 :: "nat \<Rightarrow> bool" where
  a: "vr3 0"
| "vr3 n \<Longrightarrow> vr3 (Suc n)"
| c: "vr3 n \<Longrightarrow> vr3 (Suc (Suc n))"

inductive evn and odd where
  "evn 0"
| eo: "odd n \<Longrightarrow> evn (Suc n)"
| oe: "evn n \<Longrightarrow> odd (Suc n)"

inductive tw :: "nat \<Rightarrow> bool" where
  t1: "q2 n \<Longrightarrow> tw n"
| t2: "q2 n \<Longrightarrow> q2 (f n) \<Longrightarrow> tw (Suc n)"

datatype tree = Leaf | Node tree nat tree

datatype ta = A1 | A2 tb and tb = B1 | B2 ta


section \<open>10: picking the rule, against Isar's own methods\<close>

ML \<open>
fun names_of_isar su tac = Option.map (map #1) (SWC.isar "Isar" su tac)
fun cases_tac ctxt ts facts =
  Induct.cases_context_tactic true [map (SOME o SWC.read ctxt) ts] NONE facts 1
fun induct_tac ctxt ts facts =
  Induct.induct_context_tactic true [map (fn t => SOME (NONE, (SWC.read ctxt t, false))) ts]
    [] [] NONE facts 1
fun sorries n = replicate n "SORRY"
fun against_isar label su cmd NONE = SWC.fail label "no Isar result"
  | against_isar label su cmd (SOME isar) =
  (case SWC.blocks label su (cmd :: sorries 6) of
    SOME bs => SWC.check label (map #name bs = isar)
                 ("Minilang " ^ commas (map #name bs) ^ "; Isar " ^ commas isar)
  | NONE => ())

val su as (ctxt, _) = SWC.setup \<^context> "subgoals" "Q (n::nat) (xs::nat list) (x::nat)"
                        [("h", "ev n"), ("hm", "ev m")]
val _ = against_isar "10 cases nat" su "CASE_SPLIT n" (names_of_isar su (cases_tac ctxt ["n"] []))
val _ = against_isar "10 cases list" su "CASE_SPLIT xs" (names_of_isar su (cases_tac ctxt ["xs"] []))
val _ = against_isar "10 cases bool" su "CASE_SPLIT \"x < 3\""
          (names_of_isar su (cases_tac ctxt ["x < 3"] []))
val h = Proof_Context.get_thm ctxt "h"
val hm = Proof_Context.get_thm ctxt "hm"
val _ = against_isar "10 cases by fact" su "CASE_SPLIT n WITH h"
          (names_of_isar su (cases_tac ctxt ["n"] [h]))
val _ = against_isar "10 induct by fact" su "INDUCT n WITH h"
          (names_of_isar su (induct_tac ctxt ["n"] [h]))
(*the rule found by the fact does not apply: the next candidate*)
val _ = against_isar "10 induct falls through" su "INDUCT x WITH hm"
          (names_of_isar su (induct_tac ctxt ["x"] [hm]))
(*every candidate fails (section 10, item 3)*)
val suf = SWC.setup \<^context> "subgoals" "Q (g :: nat \<Rightarrow> nat)" [("hf", "fp g'")]
val _ = SWC.expect_error "10 no rule applies, induction" suf ["INDUCT g WITH hf"]
          "No induction rule applies here. Tried: `Subgoals_Without_Case_Test.fp.inducts`. \
          \Last error: Fail to apply the induction operation."
val _ = SWC.expect_error_prefix "10 no rule applies, case split" suf ["CASE_SPLIT g"]
          "No case-split rule applies here. Tried: `HOL.case_split`. Last error: "
(*no candidate at all: Isabelle's own method reports it, as before*)
val _ = SWC.expect_raise "10 no candidate"
          (SWC.setup \<^context> "subgoals" "Q (g :: nat \<Rightarrow> nat)" []) ["INDUCT g"]
          "Unable to figure out induct rule"
val _ = SWC.expect_names "10 elim rule as the first fact" su
          ["CASE_SPLIT WITH ev.cases[case_names a b] h", "SORRY", "SORRY"] ["a", "b"]
\<close>


section \<open>11: name lists\<close>

ML \<open>
val su = SWC.setup \<^context> "subgoals" "Q (n::nat)"
           [("h", "ev n"), ("hv", "vr n"), ("hv2", "vr2 n"), ("hv3", "vr3 n")]
val _ = SWC.expect_names "11 short" su
          ["CASE_SPLIT n rule: nat.exhaust[case_names z]", "SORRY", "SORRY"] ["z", "Prem0"]
val _ = SWC.expect_names "11 long" su
          ["CASE_SPLIT n rule: nat.exhaust[case_names a b c]", "SORRY", "SORRY"] ["a", "b"]
val _ = SWC.expect_names "11 long, unfilled premise" su
          ["CASE_SPLIT n rule: ev.cases[case_names a b c]", "SORRY", "SORRY", "SORRY"]
          ["Prem0", "a", "b"]
val _ = SWC.expect_names "11 unnamed after named" su
          ["CASE_SPLIT n WITH hv", "SORRY", "SORRY"] ["named", "2"]
val _ = SWC.expect_names "11 unnamed before named" su
          ["CASE_SPLIT n WITH hv2", "SORRY", "SORRY"] ["1", "named"]
val _ = SWC.expect_names "11 unnamed in the middle" su
          ["CASE_SPLIT n WITH hv3", "SORRY", "SORRY", "SORRY"] ["a", "2", "c"]
val _ = SWC.expect_names "11 unnamed in the middle, INDUCT" su
          ["INDUCT n WITH hv3", "SORRY", "SORRY", "SORRY"] ["a", "2", "c"]
val su' = SWC.setup \<^context> "subgoals" "Q (Suc m)" [("hs", "vr2 (Suc m)")]
val _ = SWC.expect_names "11 simp closes an unnamed case" su'
          ["CASE_SPLIT \"Suc m\" WITH hs", "SORRY"] ["named"]
(*several rules: the first's names give the cases (Isar's evn_odd.inducts take goals with meta
  premises, which Minilang's goals do not have)*)
val _ = SWC.expect_names "11 several rules, unnamed first"
          (SWC.setup \<^context> "subgoals" "P (a::ta) \<and> R (b::tb)" [])
          ["SPLIT_CONJS", "INDUCT a and b rule: ta.induct[case_names \"\" A2 B1 B2] tb.induct",
           "SORRY", "SORRY", "SORRY", "SORRY"]
          ["1", "A2", "B1", "B2"]
\<close>


section \<open>12: cases closed by simp\<close>

ML \<open>
val su = SWC.setup \<^context> "subgoals" "Q (Suc (Suc m))" []
val _ = SWC.expect_names "12 ev.cases on Suc (Suc m)" su
          ["CASE_SPLIT \"Suc (Suc m)\" rule: ev.cases", "SORRY", "SORRY"] ["Prem0", "step"]
val _ = SWC.expect_names "12 ev.cases on Suc 0" (SWC.setup \<^context> "subgoals" "Q (Suc 0)" [])
          ["CASE_SPLIT \"Suc 0\" rule: ev.cases", "SORRY"] ["Prem0"]
val _ = SWC.expect_names "12 short names" su
          ["CASE_SPLIT \"Suc (Suc m)\" rule: ev.cases[case_names z]", "SORRY", "SORRY"]
          ["Prem0", "Prem1"]
val sk = SWC.setup \<^context> "subgoals" "Q (Suc k)" []
val _ = (case SWC.blocks "12 INDUCT Suc k" sk ["INDUCT \"Suc k\" rule: nat.induct", "SORRY", "SORRY"] of
          SOME bs => SWC.check "12 INDUCT Suc k" (map #name bs = ["0", "Suc"] orelse map #name bs = ["Suc"])
                       (SWC.show_blocks bs)
        | NONE => ())
(*k = 1; the zero case is closed: one True case of two goes*)
val _ = SWC.expect_goals "12 INDUCT ev.induct on Suc (Suc m)" su
          ["INDUCT \"Suc (Suc m)\" rule: ev.induct", "SORRY", "SORRY"]
          [("Prem0", "ev (Suc (Suc m))"), ("step", "Q (Suc (Suc m))")]
val _ = SWC.expect_names "12 goal True" (SWC.setup \<^context> "subgoals" "True \<and> (n::nat) = n" [])
          ["RULE conjI", "INDUCT n rule: nat.induct", "SORRY", "SORRY"] ["zero", "Suc"]
\<close>


section \<open>13: a consuming rule without case names\<close>

ML \<open>
val _ = SWC.expect_names "13 numbered names" (SWC.setup \<^context> "subgoals" "Q (n::nat)" [])
          ["CASE_SPLIT rule: r13[where x = n]", "SORRY", "SORRY", "SORRY"] ["Prem0", "1", "2"]
\<close>


section \<open>14: parameter names, against Isar\<close>

ML \<open>
(*Isar's case parameters are internal names*)
fun fixes_of_isar su tac =
  SWC.isar "Isar" su tac |> Option.map (map (apsnd (map (perhaps (try Name.dest_internal)))))
fun fixes_against label su cmds NONE = SWC.fail label "no Isar result"
  | fixes_against label su cmds (SOME isar) =
  (case SWC.blocks label su (cmds @ sorries 6) of
    SOME bs => SWC.check label (map (fn b => (#name b, #fixes b)) bs = isar)
                 ("Minilang " ^ commas (map (fn b => #name b ^ "(" ^ commas (#fixes b) ^ ")") bs) ^
                  "; Isar " ^ commas (map (fn (n, xs) => n ^ "(" ^ commas xs ^ ")") isar))
  | NONE => ())
val su as (ctxt, _) = SWC.setup \<^context> "subgoals" "Q (m::nat) (n::nat) (t::tree) (f y)"
                        [("h", "ev n")]
val _ = fixes_against "14 nat" su ["INDUCT m"] (fixes_of_isar su (induct_tac ctxt ["m"] []))
val _ = fixes_against "14 tree" su ["INDUCT t"] (fixes_of_isar su (induct_tac ctxt ["t"] []))
val _ = fixes_against "14 non-variable target" su ["INDUCT \"f y\""]
          (fixes_of_isar su (induct_tac ctxt ["f y"] []))
val _ = fixes_against "14 rule by a fact" su ["INDUCT n WITH h"]
          (fixes_of_isar su (induct_tac ctxt ["n"] [Proof_Context.get_thm ctxt "h"]))
val _ = fixes_against "14 rule given" su ["INDUCT t rule: tree.induct"]
          (fixes_of_isar su (Induct.induct_context_tactic true [[SOME (NONE, (SWC.read ctxt "t", false))]]
             [] [] (SOME @{thms tree.induct}) [] 1))
\<close>


section \<open>15--16: several rules, several targets\<close>

ML \<open>
val sut as (ctxt, _) = SWC.setup \<^context> "subgoals" "P (a::ta) (z::nat) \<and> R (b::tb) z" []
(*Isar's induct on both targets: the goal is the conjunction of the two*)
fun isar_two ctxt arbitrary =
  SWC.isar "15 Isar" (ctxt, Goal.init (Thm.cterm_of ctxt
                        (Logic.mk_conjunction (HOLogic.mk_Trueprop (SWC.read ctxt "P a z"),
                                               HOLogic.mk_Trueprop (SWC.read ctxt "R b z")))))
    (Induct.induct_context_tactic true
       [[SOME (NONE, (SWC.read ctxt "a", false))], [SOME (NONE, (SWC.read ctxt "b", false))]]
       arbitrary [] NONE [] 1)
val isar_ab = Option.map (map #1) (isar_two ctxt [])
val isar_ab = the_default ["?"] isar_ab
val _ = SWC.expect_names "15 rule: ta.induct tb.induct" sut
          ["SPLIT_CONJS", "INDUCT a and b rule: ta.induct tb.induct", "SORRY", "SORRY", "SORRY", "SORRY"]
          isar_ab
val _ = SWC.expect_names "15 rule: ta.induct tb.induct, arbitrary" sut
          ["SPLIT_CONJS", "INDUCT a and b arbitrary: and z rule: ta.induct tb.induct",
           "SORRY", "SORRY", "SORRY", "SORRY"]
          isar_ab
val _ = SWC.expect_names "16 automatic" sut
          ["SPLIT_CONJS", "INDUCT a and b", "SORRY", "SORRY", "SORRY", "SORRY"] isar_ab
val _ = SWC.expect_names "16 automatic, arbitrary" sut
          ["SPLIT_CONJS", "INDUCT a and b arbitrary: and z", "SORRY", "SORRY", "SORRY", "SORRY"]
          isar_ab
(*the generalization against Isar: z only in the cases of the second target*)
val isar_fixes = isar_two ctxt [[], [dest_Free (SWC.read ctxt "z")]]
                 |> Option.map (map (apsnd (map (perhaps (try Name.dest_internal)))))
val _ = fixes_against "16 automatic, arbitrary: parameters" sut
          ["SPLIT_CONJS", "INDUCT a and b arbitrary: and z"] isar_fixes
\<close>


section \<open>17: hypothesis names\<close>

ML \<open>
fun facts_of label su cmds =
  (case SWC.blocks label su cmds of
    SOME bs => map (fn b => (#name b, map #1 (#facts b))) bs
  | NONE => [])
val su = SWC.setup \<^context> "subgoals" "Q (i::int)" []
val _ = SWC.check "17 WITH _"
          (facts_of "17 WITH _" su ["INDUCT i rule: int_le_induct[where k = 5] WITH _", "SORRY", "SORRY", "SORRY"]
           = [("Prem0", []), ("base", []), ("step", ["step.hyps", "step.IH"])]) "names"
val sut = SWC.setup \<^context> "subgoals" "Q (n::nat)" [("h", "tw n")]
val _ = SWC.check "17 one and two hypotheses"
          (facts_of "17 one and two hypotheses" sut ["INDUCT n WITH h", "SORRY", "SORRY"]
           = [("t1", ["t1.hyps"]), ("t2", ["t2.hyps(1)", "t2.hyps(2)"])]) "names"
\<close>

ML \<open>SWC.report ()\<close>

end
