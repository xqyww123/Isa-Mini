theory Sturm_Static_Test
  imports Sturm_Sequences.Sturm_Method Auto_Sledgehammer.Auto_Sledgehammer
begin

ML \<open>
fun time_it name f =
  let
    val start = Timing.start ()
    val result = (SOME (f ()) handle ERROR msg => (writeln (name ^ " ERROR: " ^ msg); NONE)
                                   | Match => (writeln (name ^ " Match"); NONE)
                                   | Fail msg => (writeln (name ^ " Fail: " ^ msg); NONE))
    val timing = Timing.result start
    val _ = writeln (name ^ ": " ^ Timing.message timing ^
                     " => " ^ (case result of SOME _ => "OK" | NONE => "FAIL"))
  in result end
\<close>

section \<open>Approach 1: Nbe.static_conv on BARE terms (no Trueprop wrapper)\<close>

ML \<open>
val _ = writeln "=== Building Nbe.static_conv ==="
val nbe_static = time_it "nbe_static_build" (fn () =>
  Nbe.static_conv {ctxt = \<^context>, consts =
    [\<^const_name>\<open>count_roots\<close>,
     \<^const_name>\<open>count_roots_between\<close>,
     \<^const_name>\<open>count_roots_above\<close>,
     \<^const_name>\<open>count_roots_below\<close>,
     \<^const_name>\<open>poly_inf\<close>,
     \<^const_name>\<open>poly_neg_inf\<close>,
     \<^const_name>\<open>sign_changes\<close>,
     \<^const_name>\<open>sign_changes_inf\<close>,
     \<^const_name>\<open>sign_changes_neg_inf\<close>,
     \<^const_name>\<open>Polynomial.poly\<close>,
     \<^const_name>\<open>HOL.eq\<close>,
     \<^const_name>\<open>less\<close>,
     \<^const_name>\<open>less_eq\<close>,
     \<^const_name>\<open>HOL.Not\<close>,
     \<^const_name>\<open>HOL.conj\<close>,
     \<^const_name>\<open>HOL.disj\<close>]})
\<close>

text \<open>Test on BARE boolean terms (no Trueprop).\<close>

ML \<open>
val _ = writeln "=== Testing Nbe.static_conv (bare terms) ==="
val bare1 = \<^cterm>\<open>count_roots [:- 1, 0, 1 :: real:] = 2\<close>
val bare2 = \<^cterm>\<open>[:1, 0, 1 :: real:] \<noteq> 0 \<and> 0 < poly_inf [:1, 0, 1 :: real:] \<and> count_roots [:1, 0, 1 :: real:] = 0\<close>
val bare3 = \<^cterm>\<open>[:1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 :: real:] \<noteq> 0
  \<and> 0 < poly_inf [:1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 :: real:]
  \<and> count_roots [:1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 :: real:] = 0\<close>

val nbe_s = the nbe_static
val _ = time_it "static(simple)" (fn () => nbe_s \<^context> bare1)
val _ = time_it "static(compound)" (fn () => nbe_s \<^context> bare2)
val _ = time_it "static(deg10)" (fn () => nbe_s \<^context> bare3)
val _ = writeln "--- second round (warm) ---"
val _ = time_it "static(simple)2" (fn () => nbe_s \<^context> bare1)
val _ = time_it "static(compound)2" (fn () => nbe_s \<^context> bare2)
val _ = time_it "static(deg10)2" (fn () => nbe_s \<^context> bare3)
\<close>

section \<open>Approach 2: Nbe.dynamic_conv on bare terms (for comparison)\<close>

ML \<open>
val _ = writeln "=== Nbe.dynamic_conv (bare terms) ==="
val _ = time_it "dynamic(simple)" (fn () => Nbe.dynamic_conv \<^context> bare1)
val _ = time_it "dynamic(compound)" (fn () => Nbe.dynamic_conv \<^context> bare2)
val _ = time_it "dynamic(deg10)" (fn () => Nbe.dynamic_conv \<^context> bare3)
val _ = writeln "--- second round ---"
val _ = time_it "dynamic(simple)2" (fn () => Nbe.dynamic_conv \<^context> bare1)
val _ = time_it "dynamic(compound)2" (fn () => Nbe.dynamic_conv \<^context> bare2)
val _ = time_it "dynamic(deg10)2" (fn () => Nbe.dynamic_conv \<^context> bare3)
\<close>

section \<open>Approach 3: Wrap Nbe.static_conv with Trueprop handling for use as conv\<close>

ML \<open>
(* Wrap: strip Trueprop, apply static conv on the inner bool, re-wrap *)
fun nbe_static_prop_conv nbe_s ctxt ct =
  let val inner_conv = Conv.arg_conv (nbe_s ctxt)
  in inner_conv ct end

val _ = writeln "=== Nbe.static_conv with Trueprop wrapper ==="
val prop1 = Thm.apply \<^cterm>\<open>Trueprop\<close> bare1
val prop2 = Thm.apply \<^cterm>\<open>Trueprop\<close> bare2
val prop3 = Thm.apply \<^cterm>\<open>Trueprop\<close> bare3
val _ = time_it "static_prop(simple)" (fn () => nbe_static_prop_conv nbe_s \<^context> prop1)
val _ = time_it "static_prop(compound)" (fn () => nbe_static_prop_conv nbe_s \<^context> prop2)
val _ = time_it "static_prop(deg10)" (fn () => nbe_static_prop_conv nbe_s \<^context> prop3)
val _ = writeln "--- second round ---"
val _ = time_it "static_prop(simple)2" (fn () => nbe_static_prop_conv nbe_s \<^context> prop1)
val _ = time_it "static_prop(compound)2" (fn () => nbe_static_prop_conv nbe_s \<^context> prop2)
val _ = time_it "static_prop(deg10)2" (fn () => nbe_static_prop_conv nbe_s \<^context> prop3)
\<close>

section \<open>Final comparison: all backends on same Trueprop-wrapped term\<close>

ML \<open>
val _ = writeln "=== FINAL: All backends on compound term ==="
val _ = time_it "dynamic_holds" (fn () => Code_Runtime.dynamic_holds_conv \<^context> prop2)
val _ = time_it "nbe_dynamic" (fn () => Nbe.dynamic_conv \<^context> prop2)
val _ = time_it "nbe_static_wrapped" (fn () => nbe_static_prop_conv nbe_s \<^context> prop2)
val _ = time_it "code_simp" (fn () => Code_Simp.dynamic_conv \<^context> prop2)
\<close>

end
