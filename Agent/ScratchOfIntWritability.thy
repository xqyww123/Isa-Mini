theory ScratchOfIntWritability
  imports Minilang_AoA
begin

ML \<open>
  val ctxt = @{context}
  val t = Syntax.read_term ctxt "Int.ring_1_class.of_int (a::int) :: rat"
  val h = Term.head_of t
  val _ = writeln ("HEAD: " ^ @{make_string} h)
\<close>

term "Int.ring_1_class.of_int (3::int) :: rat"

ML \<open>
  val ctxt = @{context}
  val t1 = Syntax.read_term ctxt "Int.ring_1_class.of_int (a::int) :: rat"
  val t2 = Syntax.read_term ctxt "of_int (a::int) :: rat"
  val t3 = Syntax.read_term ctxt "rat_of_int (a::int)"
  val t4 = Syntax.read_term ctxt "Rat.of_int (a::int)"
  fun hd_str t = @{make_string} (Term.head_of t)
  val _ = writeln ("t1 head: " ^ hd_str t1)
  val _ = writeln ("t2 head: " ^ hd_str t2)
  val _ = writeln ("t3 head: " ^ hd_str t3)
  val _ = writeln ("t4 head: " ^ hd_str t4)
  val _ = writeln ("t1 aconv t2: " ^ @{make_string} (t1 aconv t2))
  val _ = writeln ("t1 aconv t3: " ^ @{make_string} (t1 aconv t3))
  val _ = writeln ("t1 aconv t4: " ^ @{make_string} (t1 aconv t4))
  val _ = writeln ("t3 aconv t4: " ^ @{make_string} (t3 aconv t4))
\<close>

lemma exp3a:
  fixes a::int assumes "(0::int) < a" shows "(0::rat) < of_int a"
  using assms by (simp add: of_int_0_less_iff)

lemma exp3b:
  fixes a::int assumes "(0::int) < a" shows "(0::rat) < rat_of_int a"
  using assms by (simp add: of_int_0_less_iff)

lemma exp3c:
  fixes a::int assumes "(0::int) < a" shows "(0::rat) < Int.ring_1_class.of_int a"
  using assms by (simp add: of_int_0_less_iff)

lemma exp3d:
  fixes a::int assumes "(0::int) < a" shows "(0::rat) < Rat.of_int a"
  using assms by (simp add: of_int_0_less_iff)

end
