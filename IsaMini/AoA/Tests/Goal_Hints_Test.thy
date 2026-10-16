theory Goal_Hints_Test
  imports User_Operation_Test_Base
begin

text \<open>
  Goal hints (docs/GOAL_HINTS.md, section 7): the matching walk and the
  declaration checks. No goal hint is declared at top level: each case builds
  exactly the context it names by applying the attribute from source text with
  \<open>declared\<close>, and calls \<open>Agent_Hint.goal_hints\<close> on a term read in that context.
\<close>

ML \<open>
local
open User_Operation_Test
val declared = declared "aoa_notice_goal"

val ctxt0 = \<^context>
(*the variables of the goals, fixed with their types*)
val (_, ctxt) =
  Proof_Context.add_fixes
    (map (fn (x, T) => (Binding.name x, SOME T, NoSyn))
      [("a", \<^typ>\<open>nat\<close>), ("b", \<^typ>\<open>nat\<close>), ("n", \<^typ>\<open>nat\<close>), ("k", \<^typ>\<open>nat\<close>),
       ("x", \<^typ>\<open>nat\<close>), ("c", \<^typ>\<open>bool\<close>), ("A", \<^typ>\<open>nat set\<close>),
       ("f", \<^typ>\<open>bool \<Rightarrow> bool\<close>)]) ctxt0

(*a declaration's arguments: the text, then the clauses*)
fun hint text clauses = "\<open>" ^ text ^ "\<close> " ^ clauses
fun with_hints ctxt hints = fold (fn h => fn c => declared c h) hints ctxt

(*the running example's two hints and the test-only ones*)
val dvd_text = "To prove a divisibility `a dvd b`, look for a witness `b = a * k` (`dvd_def`), or chain through `dvd_trans`."
val gcd_text = "`gcd` goals usually go through `gcd_unique_nat` / `gcd_dvd1` / `gcd_dvd2`."
val dvd_hint = hint dvd_text "whole_prop \<open>_ dvd _\<close>"
val gcd_hint = hint gcd_text "subterm \<open>gcd _ _\<close>"
val sub_dvd = hint "sub dvd" "subterm \<open>_ dvd _\<close>"
val not_dvd = hint "not dvd" "whole_prop \<open>\<not> (_ dvd _)\<close>"
val neq = hint "neq" "whole_prop \<open>_ \<noteq> 0\<close>"
val le0 = hint "le0" "whole_prop \<open>0 \<le> _\<close>"
val sub_le = hint "sub le" "subterm \<open>_ \<le> _\<close>"
val finite_hint = hint "finite" "subterm \<open>finite _\<close>"

fun texts_of ctxt t = map #text (Agent_Hint.goal_hints ctxt t)
fun expect what ctxt s texts =
  let val actual = texts_of ctxt (Syntax.read_prop ctxt s)
   in assert (what ^ ": " ^ s ^ " gave " ^ commas_quote actual) (actual = texts) end
in

(*1: the running example*)
val both = with_hints ctxt [dvd_hint, gcd_hint]
val only_sub_dvd = with_hints ctxt [sub_dvd]
val _ = expect "both, in declaration order" both "gcd a b dvd a \<and> 0 < a" [dvd_text, gcd_text]
val _ = expect "a proposition passed as an argument is a term position" both "f (a dvd b) = c" []
val _ = expect "subterm finds the argument" (with_hints both [sub_dvd]) "f (a dvd b) = c" ["sub dvd"]
val _ = expect "nothing registered" ctxt "gcd a b dvd a \<and> 0 < a" []
val _ = expect "a conclusion that is not a Trueprop yields the subterm hint" both "gcd a b \<equiv> 1" [gcd_text]

(*2: what Intro would turn into a hypothesis is never visited, by either kind*)
val _ = expect "consequent" both "\<forall>x. x \<le> n \<longrightarrow> x dvd n" [dvd_text]
val _ = expect "antecedent" both "\<forall>x. x dvd n \<longrightarrow> x \<le> n" []
val _ = expect "antecedent: subterm" only_sub_dvd "\<forall>x. x dvd n \<longrightarrow> x \<le> n" []
val _ = expect "antecedent under a conjunction" both "(\<forall>x. x dvd n \<longrightarrow> x \<le> n) \<and> 0 < n" []
val _ = expect "Pure conclusion" both "\<And>x. x \<in> A \<Longrightarrow> x dvd n" [dvd_text]
val _ = expect "Pure premise" both "\<And>x. x dvd n \<Longrightarrow> x \<in> A" []
val _ = expect "Pure premise: subterm" only_sub_dvd "\<And>x. x dvd n \<Longrightarrow> x \<in> A" []
(*a fully applied connective of the table is not a position, in the
  propositional structure or outside it, and neither is its partial
  application: a schematic-headed pattern cannot fire on the implication
  before Intro and not after it*)
val f_dvd = with_hints ctxt [hint "f dvd" "subterm \<open>?f (_ dvd _)\<close>"]
val f_dvd_2 = with_hints ctxt [hint "f dvd 2" "subterm \<open>?f (_ dvd _) _\<close>"]
val _ = List.app (fn s =>
          (expect "an implication's partial application is not a position" f_dvd s [];
           expect "an implication node is not a position" f_dvd_2 s []))
  ["x dvd n \<longrightarrow> x \<le> n", "\<not> (a dvd b \<longrightarrow> c)"]
val _ = expect "the same pattern on an application" f_dvd "f (a dvd b) = c" ["f dvd"]
(*the abstraction a quantifier binds is not a position, in the propositional
  structure or outside it; the abstraction of a comprehension is*)
val lam = with_hints ctxt [hint "lam" "subterm \<open>\<lambda>x. x dvd _ \<longrightarrow> _\<close>"]
val _ = List.app (fn s => expect "the abstraction a quantifier binds" lam s [])
  ["\<forall>x. x dvd n \<longrightarrow> x \<le> n", "\<not> (\<forall>x. x dvd n \<longrightarrow> x \<le> n)"]
val _ = expect "the abstraction of a comprehension" lam "card {x. x dvd n \<longrightarrow> x \<le> n} = k" ["lam"]

(*3: the rows of the connective table, both sides of the symmetric ones*)
val _ = List.app (fn s => expect "a row of the connective table" both s [dvd_text])
  ["0 < a \<and> a dvd b", "0 < a \<or> a dvd b", "a dvd b \<or> 0 < a", "c \<longleftrightarrow> a dvd b",
   "a dvd b \<longleftrightarrow> c", "\<exists>k. a dvd k", "\<exists>!k. a dvd k", "\<exists>x\<in>A. x dvd n"]

(*4: \<not> is a leaf of the propositional structure and hides nothing from subterm*)
val _ = expect "not: whole_prop" both "\<not> (a dvd b)" []
val _ = expect "not: whole_prop on the negation" (with_hints ctxt [not_dvd]) "\<not> (a dvd b)" ["not dvd"]
val _ = expect "not: subterm" only_sub_dvd "\<not> (a dvd b)" ["sub dvd"]
val _ = expect "an implication under not" only_sub_dvd "\<not> (a dvd b \<longrightarrow> c)" ["sub dvd"]
val _ = expect "an implication in a comprehension" only_sub_dvd
          "card {x. x dvd n \<longrightarrow> x \<le> n} = k" ["sub dvd"]
val _ = expect "an antecedent outside the propositional structure" both
          "card {x. gcd x n = 1 \<longrightarrow> x dvd n} = k" [gcd_text]

(*5: \<noteq> is \<not> (=); = is the connective \<longleftrightarrow> only at bool*)
val neq_ctxt = with_hints ctxt [neq]
val _ = expect "neq" neq_ctxt "x \<noteq> 0" ["neq"]
val _ = expect "eq is not neq" neq_ctxt "x = 0" []
val eq_ctxt = with_hints ctxt [hint "eq" "whole_prop \<open>_ = _\<close>"]
val _ = expect "an equation at nat is one proposition position" eq_ctxt "gcd a b = 1" ["eq"]
val _ = expect "a bi-implication node is not a position" eq_ctxt "c \<longleftrightarrow> a dvd b" []

(*6: binders, eta-contracted or not, inside and outside the propositional
  structure*)
val le0_ctxt = with_hints ctxt [le0]
val le0_sub_le = with_hints ctxt [le0, sub_le]
val _ = expect "a bound variable" le0_ctxt "\<forall>x::nat. 0 \<le> x" ["le0"]
val eta = Syntax.read_term ctxt "All ((\<le>) (0::nat))"
val _ = assert "the eta-contracted goal is eta-contracted" (case #2 (Term.dest_comb eta) of Abs _ => false | _ => true)
val _ = assert "eta-contracted: whole_prop" (texts_of le0_ctxt (HOLogic.mk_Trueprop eta) = ["le0"])
val _ = assert "eta-contracted: subterm alone"
          (texts_of (with_hints ctxt [sub_le]) (HOLogic.mk_Trueprop eta) = ["sub le"])
val _ = assert "eta-contracted: subterm beside a whole_prop hint"
          (texts_of le0_sub_le (HOLogic.mk_Trueprop eta) = ["le0", "sub le"])
(*\<not> is a leaf of the propositional structure, so the quantifier under it
  is outside it: its body is a term position, not a proposition position*)
val neg_eta = HOLogic.mk_Trueprop (HOLogic.mk_not eta)
val _ = assert "eta-contracted under not" (texts_of le0_sub_le neg_eta = ["sub le"])
val _ = expect "under not" le0_sub_le "\<not> (\<forall>x::nat. 0 \<le> x)" ["sub le"]
val _ = expect "the body of Ball" both "\<forall>x\<in>A. x dvd n" [dvd_text]
val finite_ctxt = with_hints ctxt [finite_hint]
val _ = expect "the body of a comprehension" finite_ctxt "card {X. finite X} = k" ["finite"]
val _ = expect "an eta-contracted argument of a non-quantifier" finite_ctxt "card (Collect finite) = k" []

(*7: the domain of Ball is not visited, the domain of Bex is*)
val _ = expect "the domain of Ball" only_sub_dvd "\<forall>x\<in>{y. y dvd n}. x \<le> n" []
val _ = expect "the domain of Bex" only_sub_dvd "\<exists>x\<in>{y. y dvd n}. x \<le> n" ["sub dvd"]

(*8: only a whole_prop hint registered: the same results*)
val only_whole = with_hints ctxt [dvd_hint]
val _ = expect "pruned: the running example" only_whole "gcd a b dvd a \<and> 0 < a" [dvd_text]
val _ = expect "pruned: the argument" only_whole "f (a dvd b) = c" []
val _ = expect "pruned: the consequent" only_whole "\<forall>x. x \<le> n \<longrightarrow> x dvd n" [dvd_text]
val _ = expect "pruned: not" only_whole "\<not> (a dvd b)" []

(*9: the net ignores types and repeated variables; Pattern.matches decides*)
val int_dvd = with_hints ctxt [hint "int dvd" "whole_prop \<open>(_::int) dvd _\<close>"]
val _ = expect "a typed pattern: nat" int_dvd "a dvd b" []
val _ = expect "a typed pattern: int" int_dvd "int a dvd int b" ["int dvd"]
val self_dvd = with_hints ctxt [hint "self dvd" "whole_prop \<open>?x dvd ?x\<close>"]
val _ = expect "a repeated variable: same" self_dvd "a dvd a" ["self dvd"]
val _ = expect "a repeated variable: different" self_dvd "a dvd b" []

(*10: one declaration is one hint however many patterns it carries*)
val two = with_hints ctxt [hint "two" "whole_prop \<open>_ dvd _\<close> and \<open>0 < _\<close>"]
val _ = expect "the second pattern" two "0 < a" ["two"]
val _ = expect "both patterns, one hint" two "gcd a b dvd a \<and> 0 < a" ["two"]

(*11: the declaration checks, with the approved texts*)
fun refused text clauses = fails_with text (fn () => declared ctxt0 (hint "t" clauses))
val _ = refused "Goal hint whole_prop \"card _\": its type is nat, not bool" "whole_prop \<open>card _\<close>"
val _ = refused "Goal hint whole_prop \"gcd _ _\": its type is ?'a::gcd, not bool" "whole_prop \<open>gcd _ _\<close>"
val _ = refused "Goal hint whole_prop \"_ \<and> _\": it contains the connective \<and>" "whole_prop \<open>_ \<and> _\<close>"
val _ = refused "Goal hint subterm \"\<forall>x. _ x\": it contains the connective \<forall>" "subterm \<open>\<forall>x. _ x\<close>"
val _ = refused "Goal hint whole_prop \"_ \<longleftrightarrow> _\": it contains the connective \<longleftrightarrow>"
          "whole_prop \<open>_ \<longleftrightarrow> _\<close>"
val _ = refused "Goal hint whole_prop \"(\<lambda>x. x \<and> _) _\": it contains the connective \<and>"
          "whole_prop \<open>(\<lambda>x. x \<and> _) _\<close>"
val _ = refused "Goal hint subterm \"(\<and>) _\": it contains the connective \<and>" "subterm \<open>(\<and>) _\<close>"
val _ = refused ("Goal hint whole_prop \"a dvd b\": a is neither a constant nor fixed here; " ^
                 "write _ or ?a for an open position, or import the theory that defines it")
          "whole_prop \<open>a dvd b\<close>"
val _ = refused ("Goal hint whole_prop \"gdc _ _\": gdc is neither a constant nor fixed here; " ^
                 "write _ or ?gdc for an open position, or import the theory that defines it")
          "whole_prop \<open>gdc _ _\<close>"
(*the grammar: a clause starts with its keyword; a keyword without its patterns,
  a pattern without a keyword, a second pattern without `and` and a text
  without any clause are parse errors*)
val _ = fails_with "Outer syntax error" (fn () => declared ctxt0 (hint "t" "whole_prop"))
val _ = fails_with "Bad arguments" (fn () => declared ctxt0 (hint "t" ""))
val _ = fails_with "Bad arguments" (fn () => declared ctxt0 (hint "t" "\<open>_ dvd _\<close>"))
val _ = fails_with "Bad arguments" (fn () => declared ctxt0 (hint "t" "subterm \<open>_ dvd _\<close> \<open>_ < _\<close>"))
(*accepted; `and` continues a clause and keeps its kind: read as whole_prop,
  `card _` would be refused for its type*)
val _ = List.app (fn clauses => (declared ctxt0 (hint "t" clauses); ()))
  ["whole_prop \<open>_\<close>", "whole_prop \<open>_ = _\<close>", "whole_prop \<open>_ \<noteq> 0\<close>", "whole_prop \<open>_ \<notin> _\<close>",
   "subterm \<open>card {x. _ x \<and> _ x}\<close>",
   "whole_prop \<open>_ dvd _\<close> and \<open>gcd _ _ = _\<close> subterm \<open>gcd _ _\<close> and \<open>card _\<close>"]
(*a fixed variable passes*)
val _ = (declared ctxt (hint "t" "whole_prop \<open>a dvd b\<close>"); ())

(*12: the ML entry: the same hints as the attribute, one hint per call however
  many patterns of either kind it carries, and the same checks*)
fun added ctxt hint = Context.the_proof (Agent_Hint.add_goal_hint hint (Context.Proof ctxt))
val ml_both =
  added ctxt {text = dvd_text, whole_prop = ["_ dvd _"], subterm = []}
  |> (fn c => added c {text = gcd_text, whole_prop = [], subterm = ["gcd _ _"]})
val _ = expect "ML entry: the running example" ml_both "gcd a b dvd a \<and> 0 < a" [dvd_text, gcd_text]
val _ = expect "ML entry: a proposition passed as an argument" ml_both "f (a dvd b) = c" []
val ml_two = added ctxt {text = "two", whole_prop = ["_ dvd _", "0 < _"], subterm = []}
val _ = expect "ML entry: the second pattern" ml_two "0 < a" ["two"]
val _ = expect "ML entry: both patterns, one hint" ml_two "gcd a b dvd a \<and> 0 < a" ["two"]
val ml_mixed = added ctxt {text = "mixed", whole_prop = ["_ dvd _"], subterm = ["gcd _ _"]}
val _ = expect "ML entry: both kinds, one hint" ml_mixed "gcd a b dvd a \<and> 0 < a" ["mixed"]
val _ = expect "ML entry: the subterm clause alone fires in a term position" ml_mixed
          "f (gcd a b dvd a) = c" ["mixed"]
val _ = expect "ML entry: an abbreviation is expanded as it is read"
          (added ctxt {text = "neq", whole_prop = ["_ \<noteq> 0"], subterm = []}) "x \<noteq> 0" ["neq"]
val _ = fails_with "Goal hint whole_prop \"card _\": its type is nat, not bool"
          (fn () => added ctxt0 {text = "t", whole_prop = ["card _"], subterm = []})
val _ = fails_with "Goal hint subterm \"\<forall>x. _ x\": it contains the connective \<forall>"
          (fn () => added ctxt0 {text = "t", whole_prop = [], subterm = ["\<forall>x. _ x"]})
val _ = fails_with ("Goal hint whole_prop \"a dvd b\": a is neither a constant nor fixed here; " ^
                    "write _ or ?a for an open position, or import the theory that defines it")
          (fn () => added ctxt0 {text = "t", whole_prop = ["a dvd b"], subterm = []})
val _ = (added ctxt {text = "t", whole_prop = ["a dvd b"], subterm = []}; ())

val _ = writeln "ALL PASS: Goal_Hints_Test"
end
\<close>

end
