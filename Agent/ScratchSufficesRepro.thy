theory ScratchSufficesRepro
  imports Minilang_Agent
begin

(* ===== Baseline: pure Isabelle behaviour of the rewrite on the implication ===== *)

thm of_int_0_less_iff

lemma baseline_simp:
  fixes a :: int
  shows "(0::rat) < Rat.of_int a \<longrightarrow> (0::int) < a"
  apply (simp add: of_int_0_less_iff)
  oops

(* What does of_int_0_less_iff[symmetric] do to the bare consequent 0 < a? *)
lemma baseline_consequent:
  fixes a :: int
  shows "(0::int) < a"
  apply (simp only: of_int_0_less_iff[symmetric, where ?'a = rat])
  oops

ML \<open>
  val ctxt = @{context}
  val t_rat   = Syntax.read_term ctxt "Rat.of_int a :: rat"
  val t_ofint = Syntax.read_term ctxt "of_int a :: rat"
  val t_abbr  = Syntax.read_term ctxt "rat_of_int a"
  fun headc t = case Term.head_of t of Const (n, T) => n ^ " :: " ^ Syntax.string_of_typ ctxt T | _ => "(not const)"
  val _ = writeln ("Rat.of_int a  head = " ^ headc t_rat)
  val _ = writeln ("of_int a::rat head = " ^ headc t_ofint)
  val _ = writeln ("rat_of_int a  head = " ^ headc t_abbr)
  val _ = writeln ("Rat.of_int = of_int ?  " ^ Bool.toString (t_rat aconv t_ofint))
  val _ = writeln ("Rat.of_int = rat_of_int ?  " ^ Bool.toString (t_rat aconv t_abbr))
\<close>

thm of_int_0_less_iff [where ?'a = rat]

(* Enumerate every constant whose base name is "of_int" visible here *)
ML \<open>
  val ctxt = @{context}
  val thy = Proof_Context.theory_of ctxt
  val consts = Sign.consts_of thy
  val all = map fst (#constants (Consts.dest consts))
  val ofints = filter (fn n => Long_Name.base_name n = "of_int") all
  val _ = writeln ("constants with base name of_int (" ^ string_of_int (length ofints) ^ "):")
  val _ = List.app (fn n => writeln ("  " ^ n)) ofints
\<close>

(* Is Rat.of_int provably the int->rat embedding at all? try harder *)
lemma rat_of_int_same: "Rat.of_int a = rat_of_int a"
  by (simp add: Rat.of_int_def)

ML \<open>
  val thy = Proof_Context.theory_of @{context}
  val space = Sign.const_space thy
  val {pos, theory_long_name, ...} = Name_Space.the_entry space "Rat.of_int"
  val _ = writeln ("Rat.of_int declared in theory " ^ theory_long_name ^ " at " ^ Position.here pos)
  val e2 = Name_Space.the_entry space "Int.ring_1_class.of_int"
  val _ = writeln ("Int.ring_1_class.of_int declared in theory " ^ #theory_long_name e2 ^ " at " ^ Position.here (#pos e2))
\<close>

thm Rat.of_int_def

end
