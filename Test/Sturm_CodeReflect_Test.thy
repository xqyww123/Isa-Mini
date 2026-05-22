theory Sturm_CodeReflect_Test
  imports Sturm_Sequences.Sturm_Method Auto_Sledgehammer.Auto_Sledgehammer
begin

text \<open>Test: does code_reflect speed up dynamic_holds_conv for sturm functions?\<close>

text \<open>Pre-compile Sturm functions to ML at theory-load time.\<close>

code_reflect Sturm_Reflect
  functions
    "count_roots"
    "count_roots_between"
    "count_roots_above"
    "count_roots_below"
    "poly_inf :: _ poly \<Rightarrow> _"
    "poly_neg_inf :: _ poly \<Rightarrow> _"
    "Polynomial.poly :: _ poly \<Rightarrow> _ \<Rightarrow> _"
    "sign_changes :: _ poly list \<Rightarrow> _ \<Rightarrow> _"
    "sign_changes_inf"
    "sign_changes_neg_inf"

text \<open>Now test: does dynamic_holds_conv become faster after code_reflect?\<close>

ML \<open>
fun time_conv name f =
  let
    val start = Timing.start ()
    val result = (SOME (f ()) handle ERROR msg => (writeln (name ^ " ERROR: " ^ msg); NONE)
                                   | Match => (writeln (name ^ " Match"); NONE))
    val timing = Timing.result start
    val _ = writeln (name ^ ": " ^ Timing.message timing ^
                     " => " ^ (case result of SOME _ => "OK" | NONE => "FAIL"))
  in result end
\<close>

subsection \<open>Test 1: dynamic_holds_conv after code_reflect\<close>
ML \<open>
val ct1 = \<^cterm>\<open>count_roots [:- 1, 0, 1 :: real:] = 2\<close>
val _ = writeln "=== After code_reflect: dynamic_holds_conv ==="
val _ = time_conv "holds-call1" (fn () =>
  Code_Runtime.dynamic_holds_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct1))
val _ = time_conv "holds-call2" (fn () =>
  Code_Runtime.dynamic_holds_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct1))
val _ = time_conv "holds-call3" (fn () =>
  Code_Runtime.dynamic_holds_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct1))
\<close>

subsection \<open>Test 2: Full sturm tactic after code_reflect\<close>
ML \<open>
fun time_sturm msg goal =
  let
    val start = Timing.start ()
    val result = SINGLE (Sturm.sturm_tac \<^context> false 1) goal
    val timing = Timing.result start
    val _ = writeln (msg ^ ": " ^ Timing.message timing ^
                     " => " ^ (case result of SOME _ => "OK" | NONE => "FAIL"))
  in result end

val _ = writeln "=== Full sturm after code_reflect ==="
val _ = time_sturm "sturm(x^2+1>0)" (Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x^2 + 1 > 0)\<close>))
val _ = time_sturm "sturm(x>1->x^3>1)" (Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x > 1 \<longrightarrow> x^3 > 1)\<close>))
val _ = time_sturm "sturm(x^10+1>0)" (Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x^10 + 1 > 0)\<close>))

val _ = writeln "=== Second round (warm) ==="
val _ = time_sturm "sturm2(x^2+1>0)" (Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x^2 + 1 > 0)\<close>))
val _ = time_sturm "sturm2(x>1->x^3>1)" (Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x > 1 \<longrightarrow> x^3 > 1)\<close>))
val _ = time_sturm "sturm2(x^10+1>0)" (Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x^10 + 1 > 0)\<close>))
\<close>

subsection \<open>Test 3: Compare with NBE on same terms\<close>
ML \<open>
val _ = writeln "=== NBE after code_reflect (for comparison) ==="
val ct_compound = \<^cterm>\<open>[:1, 0, 1 :: real:] \<noteq> 0 \<and> 0 < poly_inf [:1, 0, 1 :: real:] \<and> count_roots [:1, 0, 1 :: real:] = 0\<close>
val _ = time_conv "NBE-compound-1" (fn () =>
  Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct_compound))
val _ = time_conv "NBE-compound-2" (fn () =>
  Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct_compound))
\<close>

end
