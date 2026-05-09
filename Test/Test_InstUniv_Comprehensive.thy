theory Test_InstUniv_Comprehensive
  imports Minilang.Minilang
begin

text \<open>Comprehensive tests for @{ML Minilang_Aux.inst_universal_quantifiers}
  covering: schematic variables (various indices), Pure \<open>\<And>\<close> bound variables,
  HOL \<open>\<forall>\<close> bound variables, display-renamed names (via deconflict_bound_names),
  display_of_indexname parsing, mixed instantiation, and edge cases.\<close>

ML \<open>
fun test label ctxt insts thm =
  let val result =
    (let val thm' = Minilang_Aux.inst_universal_quantifiers ctxt insts thm
     in "OK: " ^ Thm.string_of_thm ctxt thm' end)
    handle ERROR msg => "ERROR: " ^ msg
  in writeln (label ^ ": " ^ result) end

fun test_fail label ctxt insts thm =
  let val result =
    (Minilang_Aux.inst_universal_quantifiers ctxt insts thm;
     "BUG: should have failed")
    handle ERROR _ => "OK: correctly rejected"
  in writeln (label ^ ": " ^ result) end

val ctxt0 = \<^context>
val P1 = Free("P", \<^typ>\<open>nat \<Rightarrow> bool\<close>)
val P2 = Free("P", \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>)
val P3 = Free("P", \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close>)
val P4 = Free("P", \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close>)
val nat = \<^typ>\<open>nat\<close>
fun mk thm = Skip_Proof.make_thm (Proof_Context.theory_of ctxt0) thm
fun N n = HOLogic.mk_number nat n

(* Raw HOL.All constructor — does NOT abstract Free vars like mk_all does *)
fun raw_hol_all name T body =
  Const(\<^const_name>\<open>HOL.All\<close>, (T --> \<^typ>\<open>bool\<close>) --> \<^typ>\<open>bool\<close>) $ Abs(name, T, body)
\<close>

section \<open>1. Schematic variables\<close>

subsection \<open>1.1 Basic schematic at index 0\<close>
ML \<open>
val thm = mk (HOLogic.mk_Trueprop (P1 $ Var(("n",0), nat)))
val _ = writeln ("1.1 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "1.1a: (n,0) match" ctxt0 [(("n",0), N 5)] thm
val _ = test_fail "1.1b: (n,1) no match" ctxt0 [(("n",1), N 5)] thm
val _ = test_fail "1.1c: (m,0) wrong name" ctxt0 [(("m",0), N 5)] thm
\<close>

subsection \<open>1.2 Schematic at non-zero index\<close>
ML \<open>
val thm = mk (HOLogic.mk_Trueprop (P1 $ Var(("n",2), nat)))
val _ = writeln ("1.2 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "1.2a: (n,2) exact" ctxt0 [(("n",2), N 7)] thm
val _ = test_fail "1.2b: (n,0) wrong index" ctxt0 [(("n",0), N 7)] thm
val _ = test_fail "1.2c: (n2,0) wrong parse" ctxt0 [(("n2",0), N 7)] thm
\<close>

subsection \<open>1.3 Multiple schematics with same base name, different indices\<close>
ML \<open>
val thm = mk (HOLogic.mk_Trueprop (P3
    $ Var(("n",0), nat) $ Var(("n",1), nat) $ Var(("n",2), nat)))
val _ = writeln ("1.3 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "1.3a: just (n,0)" ctxt0 [(("n",0), N 10)] thm
val _ = test "1.3b: just (n,2)" ctxt0 [(("n",2), N 30)] thm
val _ = test "1.3c: all three" ctxt0
    [(("n",0), N 10), (("n",1), N 20), (("n",2), N 30)] thm
\<close>

subsection \<open>1.4 Schematic with name ending in digit: Var("n2",0)\<close>
ML \<open>
val thm = mk (HOLogic.mk_Trueprop (P1 $ Var(("n2",0), nat)))
val _ = writeln ("1.4 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "1.4a: (n2,0) exact" ctxt0 [(("n2",0), N 5)] thm
val _ = test_fail "1.4b: (n,2) wrong — different var" ctxt0 [(("n",2), N 5)] thm
\<close>

subsection \<open>1.5 Both Var("n2",0) and Var("n",2) in same theorem\<close>
ML \<open>
val thm = mk (HOLogic.mk_Trueprop (P2
    $ Var(("n2",0), nat) $ Var(("n",2), nat)))
val _ = writeln ("1.5 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "1.5a: (n2,0) only" ctxt0 [(("n2",0), N 10)] thm
val _ = test "1.5b: (n,2) only" ctxt0 [(("n",2), N 20)] thm
val _ = test "1.5c: both" ctxt0 [(("n2",0), N 10), (("n",2), N 20)] thm
\<close>


section \<open>2. HOL \<open>\<forall>\<close> bound variables\<close>

subsection \<open>2.1 Simple bound var\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("n", nat, P1 $ Bound 0) |> HOLogic.mk_Trueprop)
val _ = writeln ("2.1 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "2.1a: (n,0) match" ctxt0 [(("n",0), N 5)] thm
\<close>

subsection \<open>2.2 Bound var named "n2" — user writes n2 parsed as ("n",2)\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("n2", nat, P1 $ Bound 0) |> HOLogic.mk_Trueprop)
val _ = writeln ("2.2 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "2.2a: (n,2) via display_of_indexname" ctxt0 [(("n",2), N 5)] thm
val _ = test "2.2b: (n2,0) direct" ctxt0 [(("n2",0), N 5)] thm
\<close>

subsection \<open>2.3 Multiple bound vars: \<open>\<forall>n n1 n2\<close>\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("n", nat,
  HOLogic.mk_all ("n1", nat,
  HOLogic.mk_all ("n2", nat,
    P3 $ Bound 2 $ Bound 1 $ Bound 0))) |> HOLogic.mk_Trueprop)
val _ = writeln ("2.3 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "2.3a: n only" ctxt0 [(("n",0), N 10)] thm
val _ = test "2.3b: n1 as (n,1)" ctxt0 [(("n",1), N 20)] thm
val _ = test "2.3c: n2 as (n,2)" ctxt0 [(("n",2), N 30)] thm
val _ = test "2.3d: all three" ctxt0
    [(("n",0), N 10), (("n",1), N 20), (("n",2), N 30)] thm
\<close>

subsection \<open>2.4 Bound var behind HOL implication: \<open>\<forall>n. Q \<longrightarrow> P n\<close>\<close>
ML \<open>
val Q = Free("Q", \<^typ>\<open>bool\<close>)
val thm = mk (HOLogic.mk_all ("n", nat,
    HOLogic.mk_imp (Q, P1 $ Bound 0)) |> HOLogic.mk_Trueprop)
val _ = writeln ("2.4 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "2.4: n behind implication" ctxt0 [(("n",0), N 5)] thm
\<close>

subsection \<open>2.5 Selective instantiation: \<open>\<forall>a b. P a b\<close>, only instantiate b\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("a", nat,
  HOLogic.mk_all ("b", nat,
    P2 $ Bound 1 $ Bound 0)) |> HOLogic.mk_Trueprop)
val _ = writeln ("2.5 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "2.5a: only b" ctxt0 [(("b",0), N 5)] thm
val _ = test "2.5b: only a" ctxt0 [(("a",0), N 3)] thm
\<close>


section \<open>3. Pure \<open>\<And>\<close> bound variables\<close>

subsection \<open>3.1 Simple Pure bound\<close>
ML \<open>
val thm = mk (Logic.all_const nat $ Abs("n", nat,
    HOLogic.mk_Trueprop (P1 $ Bound 0)))
val _ = writeln ("3.1 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "3.1: (n,0)" ctxt0 [(("n",0), N 5)] thm
\<close>

subsection \<open>3.2 Pure bound named "n2"\<close>
ML \<open>
val thm = mk (Logic.all_const nat $ Abs("n2", nat,
    HOLogic.mk_Trueprop (P1 $ Bound 0)))
val _ = writeln ("3.2 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "3.2a: (n,2) via display" ctxt0 [(("n",2), N 5)] thm
val _ = test "3.2b: (n2,0) direct" ctxt0 [(("n2",0), N 5)] thm
\<close>

subsection \<open>3.3 Multiple Pure bounds\<close>
ML \<open>
val thm = mk (Logic.all_const nat $ Abs("a", nat,
  Logic.all_const nat $ Abs("b", nat,
    HOLogic.mk_Trueprop (P2 $ Bound 1 $ Bound 0))))
val _ = writeln ("3.3 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "3.3a: a only" ctxt0 [(("a",0), N 1)] thm
val _ = test "3.3b: b only" ctxt0 [(("b",0), N 2)] thm
val _ = test "3.3c: both" ctxt0 [(("a",0), N 1), (("b",0), N 2)] thm
\<close>


section \<open>4. Mixed: schematic + Pure \<open>\<And>\<close> + HOL \<open>\<forall>\<close>\<close>

subsection \<open>4.1 Schematic + HOL bound\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("m", nat,
    HOLogic.mk_imp (
      HOLogic.mk_binrel \<^const_name>\<open>Orderings.ord_class.less\<close>
        (Var(("n",0), nat), Bound 0),
      P2 $ Var(("n",0), nat) $ Bound 0)) |> HOLogic.mk_Trueprop)
val _ = writeln ("4.1 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "4.1a: n only (schematic)" ctxt0 [(("n",0), N 5)] thm
val _ = test "4.1b: m only (HOL bound)" ctxt0 [(("m",0), N 10)] thm
val _ = test "4.1c: both" ctxt0 [(("n",0), N 5), (("m",0), N 10)] thm
\<close>

subsection \<open>4.2 Schematic Var("n",2) + HOL bound "n2"\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("n2", nat,
    HOLogic.mk_imp (
      HOLogic.mk_binrel \<^const_name>\<open>Orderings.ord_class.less\<close>
        (Var(("n",2), nat), Bound 0),
      P2 $ Var(("n",2), nat) $ Bound 0)) |> HOLogic.mk_Trueprop)
val _ = writeln ("4.2 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "4.2a: (n,2) for schematic only" ctxt0 [(("n",2), N 5)] thm
val _ = test "4.2b: (n2,0) for bound only" ctxt0 [(("n2",0), N 10)] thm
val _ = test "4.2c: both" ctxt0 [(("n",2), N 5), (("n2",0), N 10)] thm
\<close>

subsection \<open>4.3 Pure \<open>\<And>\<close> + schematic + HOL \<open>\<forall>\<close>\<close>
ML \<open>
val thm = mk (Logic.all_const nat $ Abs("a", nat,
    HOLogic.mk_all ("b", nat,
      P3 $ Bound 1 $ Var(("c",0), nat) $ Bound 0) |> HOLogic.mk_Trueprop))
val _ = writeln ("4.3 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "4.3a: a (Pure) only" ctxt0 [(("a",0), N 1)] thm
val _ = test "4.3b: c (schematic) only" ctxt0 [(("c",0), N 2)] thm
val _ = test "4.3c: all three" ctxt0
    [(("a",0), N 1), (("c",0), N 2), (("b",0), N 3)] thm
\<close>


section \<open>5. Display-renamed names (deconflict_bound_names)\<close>

subsection \<open>5.1 Free n in term + HOL bound n — raw term to avoid mk_all abstraction\<close>
text \<open>Construct raw term so Free("n",nat) is NOT abstracted by mk_all.
  Term: \<open>HOL.All (\<lambda>n. P n (Free n))\<close> — bound n (Bound 0) and free n coexist.
  deconflict_bound_names should rename bound n to n1.\<close>
ML \<open>
val thm_51 = mk (HOLogic.mk_Trueprop (raw_hol_all "n" nat
    (P2 $ Bound 0 $ Free("n", nat))))
val _ = writeln ("5.1 thm: " ^ Thm.string_of_thm ctxt0 thm_51)
val deconf_51 = Minilang_Aux.deconflict_bound_names ctxt0 (Thm.prop_of thm_51)
val _ = writeln ("5.1 deconf: " ^ Syntax.string_of_term ctxt0 deconf_51)
(* Agent sees display-renamed n1, writes n1 → parsed as (n,1) *)
val _ = test "5.1a: (n,1) display name n1" ctxt0 [(("n",1), N 5)] thm_51
(* Also accept raw name *)
val _ = test "5.1b: (n,0) raw name n" ctxt0 [(("n",0), N 5)] thm_51
\<close>

subsection \<open>5.2 Free n in term + bound n and n1 — display: n2 and n1\<close>
ML \<open>
val thm_52 = mk (HOLogic.mk_Trueprop (raw_hol_all "n" nat
  (raw_hol_all "n1" nat
    (P3 $ Bound 1 $ Bound 0 $ Free("n", nat)))))
val _ = writeln ("5.2 thm: " ^ Thm.string_of_thm ctxt0 thm_52)
val deconf_52 = Minilang_Aux.deconflict_bound_names ctxt0 (Thm.prop_of thm_52)
val _ = writeln ("5.2 deconf: " ^ Syntax.string_of_term ctxt0 deconf_52)
val _ = test "5.2a: outer n via display n2" ctxt0 [(("n",2), N 10)] thm_52
val _ = test "5.2b: inner n1" ctxt0 [(("n",1), N 20)] thm_52
val _ = test "5.2c: both" ctxt0 [(("n",2), N 10), (("n",1), N 20)] thm_52
\<close>

subsection \<open>5.3 Schematic Var(n,0) display "n" conflicts with bound n\<close>
ML \<open>
val thm_53 = mk (HOLogic.mk_Trueprop (raw_hol_all "n" nat
    (P2 $ Bound 0 $ Var(("n",0), nat))))
val _ = writeln ("5.3 thm: " ^ Thm.string_of_thm ctxt0 thm_53)
val deconf_53 = Minilang_Aux.deconflict_bound_names ctxt0 (Thm.prop_of thm_53)
val _ = writeln ("5.3 deconf: " ^ Syntax.string_of_term ctxt0 deconf_53)
val _ = test "5.3a: (n,0) for schematic" ctxt0 [(("n",0), N 5)] thm_53
val _ = test "5.3b: (n,1) for display-renamed bound n1" ctxt0 [(("n",1), N 10)] thm_53
val _ = test "5.3c: both" ctxt0 [(("n",0), N 5), (("n",1), N 10)] thm_53
\<close>

subsection \<open>5.4 Var(n,2) display "n2" conflicts with bound "n2"\<close>
ML \<open>
val thm_54 = mk (HOLogic.mk_Trueprop (raw_hol_all "n2" nat
    (P2 $ Bound 0 $ Var(("n",2), nat))))
val _ = writeln ("5.4 thm: " ^ Thm.string_of_thm ctxt0 thm_54)
val deconf_54 = Minilang_Aux.deconflict_bound_names ctxt0 (Thm.prop_of thm_54)
val _ = writeln ("5.4 deconf: " ^ Syntax.string_of_term ctxt0 deconf_54)
(* bound "n2" should be renamed to avoid schematic display "n2" *)
\<close>


section \<open>6. Pure \<open>\<And>\<close> with display_of_indexname\<close>

subsection \<open>6.1 Pure bound named "x3" — user writes x3 parsed as ("x",3)\<close>
ML \<open>
val thm = mk (Logic.all_const nat $ Abs("x3", nat,
    HOLogic.mk_Trueprop (P1 $ Bound 0)))
val _ = writeln ("6.1 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "6.1a: (x,3) via display" ctxt0 [(("x",3), N 5)] thm
val _ = test "6.1b: (x3,0) direct" ctxt0 [(("x3",0), N 5)] thm
\<close>


section \<open>7. Edge cases\<close>

subsection \<open>7.1 No instantiation — identity\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("n", nat, P1 $ Bound 0) |> HOLogic.mk_Trueprop)
val _ = test "7.1: empty insts" ctxt0 [] thm
\<close>

subsection \<open>7.2 Variable not in theorem\<close>
ML \<open>
val thm = mk (HOLogic.mk_Trueprop (P1 $ Free("x", nat)))
val _ = test_fail "7.2: (z,0) not found" ctxt0 [(("z",0), N 5)] thm
\<close>

subsection \<open>7.3 Pure \<open>\<And>\<close> before Pure \<open>\<Longrightarrow>\<close> premise\<close>
ML \<open>
val prem = HOLogic.mk_Trueprop (Free("Q", \<^typ>\<open>bool\<close>))
val concl = HOLogic.mk_Trueprop (P1 $ Bound 0)
val thm = mk (Logic.all_const nat $ Abs("n", nat, Logic.mk_implies (prem, concl)))
val _ = writeln ("7.3 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "7.3: n with premise" ctxt0 [(("n",0), N 5)] thm
\<close>

subsection \<open>7.4 HOL \<open>\<forall>\<close> with type annotation: \<open>\<forall>(n::int)\<close>\<close>
ML \<open>
val int = \<^typ>\<open>int\<close>
val P_int = Free("P", \<^typ>\<open>int \<Rightarrow> bool\<close>)
val thm = mk (HOLogic.mk_all ("n", int, P_int $ Bound 0) |> HOLogic.mk_Trueprop)
val _ = writeln ("7.4 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "7.4: n::int" ctxt0 [(("n",0), \<^term>\<open>42::int\<close>)] thm
\<close>

subsection \<open>7.5 Deeply nested: \<open>\<forall>a. \<forall>b. a < b \<longrightarrow> \<forall>c. P a b c\<close>\<close>
ML \<open>
val (a,b,c) = (Free("a",nat), Free("b",nat), Free("c",nat))
val thm = mk (
  HOLogic.mk_all ("a", nat,
  HOLogic.mk_all ("b", nat,
  HOLogic.mk_imp (
    HOLogic.mk_binrel \<^const_name>\<open>Orderings.ord_class.less\<close> (a, b),
  HOLogic.mk_all ("c", nat,
    P3 $ a $ b $ c)))) |> HOLogic.mk_Trueprop)
val _ = writeln ("7.5 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "7.5a: a only" ctxt0 [(("a",0), N 1)] thm
val _ = test "7.5b: c only" ctxt0 [(("c",0), N 3)] thm
val _ = test "7.5c: all three" ctxt0
    [(("a",0), N 1), (("b",0), N 2), (("c",0), N 3)] thm
\<close>

subsection \<open>7.6 Phase ordering: schematic instantiated before inst_hol_alls\<close>
text \<open>Var("n",0) and HOL-bound m.  Phase 2 (schematic) must run before
  Phase 3 (inst_hol_alls + zero_var_indexes) to avoid index corruption.\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("m", nat,
    P2 $ Var(("n",0), nat) $ Bound 0) |> HOLogic.mk_Trueprop)
val _ = writeln ("7.6 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "7.6a: n (schematic) + m (bound)" ctxt0
    [(("n",0), N 5), (("m",0), N 10)] thm
val _ = test "7.6b: m (bound) only, schematic survives" ctxt0
    [(("m",0), N 10)] thm
val _ = test "7.6c: n (schematic) only, bound survives" ctxt0
    [(("n",0), N 5)] thm
\<close>

subsection \<open>7.7 Var("n",2) schematic + HOL-bound "m" — phase ordering with non-zero index\<close>
ML \<open>
val thm = mk (HOLogic.mk_all ("m", nat,
    P2 $ Var(("n",2), nat) $ Bound 0) |> HOLogic.mk_Trueprop)
val _ = writeln ("7.7 thm: " ^ Thm.string_of_thm ctxt0 thm)
val _ = test "7.7: (n,2) + (m,0) — phase ordering" ctxt0
    [(("n",2), N 5), (("m",0), N 10)] thm
\<close>

subsection \<open>7.8 Display-renamed with multiple renames: Free n, bound n and n1\<close>
text \<open>Free n in term, bound n renamed to n2 (since n1 is taken by inner bound).
  Both display names should work.\<close>
ML \<open>
val thm_78 = mk (HOLogic.mk_Trueprop (raw_hol_all "n" nat
  (raw_hol_all "n1" nat
    (P3 $ Bound 1 $ Bound 0 $ Free("n", nat)))))
val _ = writeln ("7.8 thm: " ^ Thm.string_of_thm ctxt0 thm_78)
val deconf_78 = Minilang_Aux.deconflict_bound_names ctxt0 (Thm.prop_of thm_78)
val _ = writeln ("7.8 deconf: " ^ Syntax.string_of_term ctxt0 deconf_78)
val _ = test "7.8a: (n,2) for outer" ctxt0 [(("n",2), N 100)] thm_78
val _ = test "7.8b: (n,1) for inner" ctxt0 [(("n",1), N 200)] thm_78
val _ = test "7.8c: both" ctxt0 [(("n",2), N 100), (("n",1), N 200)] thm_78
\<close>

end
