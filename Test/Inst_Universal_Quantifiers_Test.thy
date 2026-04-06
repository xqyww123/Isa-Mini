theory Inst_Universal_Quantifiers_Test
  imports Minilang.Minilang
begin

section \<open>Tests for @{ML Minilang_Aux.inst_universal_quantifiers}\<close>

subsection \<open>HOL.All instantiation\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x y :: nat. x < y \<longrightarrow> x \<le> y\<close> by auto}
  val _ = writeln ("HOL.All input: " ^ Thm.string_of_thm ctxt thm)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("x", 0), "0::nat"), (("y", 0), "1::nat")] thm
  val _ = writeln ("HOL.All full: " ^ Thm.string_of_thm ctxt result)
in () end
\<close>

text \<open>Partial: instantiate only x, keep y\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x y :: nat. x < y \<longrightarrow> x \<le> y\<close> by auto}
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("x", 0), "0::nat")] thm
  val _ = writeln ("HOL.All partial: " ^ Thm.string_of_thm ctxt result)
  (* should be: \<forall>y. 0 < y \<longrightarrow> 0 \<le> y *)
in () end
\<close>

text \<open>Instantiate inner variable only (requires reordering via all_comm)\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x y :: nat. x + y = y + x\<close> by auto}
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("y", 0), "0::nat")] thm
  val _ = writeln ("HOL.All inner: " ^ Thm.string_of_thm ctxt result)
  (* should be: \<forall>x. x + 0 = 0 + x *)
in () end
\<close>

subsection \<open>Pure.all (\<And>) instantiation\<close>

text \<open>conjI has Pure.all: \<And>P Q. P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{thm conjI}
  val _ = writeln ("Pure.all input: " ^ Thm.string_of_thm ctxt thm)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("P", 0), "True"), (("Q", 0), "False")] thm
  val _ = writeln ("Pure.all full: " ^ Thm.string_of_thm ctxt result)
  (* should be: True \<Longrightarrow> False \<Longrightarrow> True \<and> False *)
in () end
\<close>

text \<open>Selective: instantiate P only, keep Q\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{thm conjI}
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("P", 0), "True")] thm
  val _ = writeln ("Pure.all selective: " ^ Thm.string_of_thm ctxt result)
  (* should be: \<And>Q. True \<Longrightarrow> Q \<Longrightarrow> True \<and> Q *)
in () end
\<close>

text \<open>Instantiate inner variable only (b in sym: \<And>a b. a = b \<Longrightarrow> b = a)\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<And>a b :: nat. a = b \<Longrightarrow> b = a\<close> by auto}
  val _ = writeln ("Pure.all inner input: " ^ Thm.string_of_thm ctxt thm)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("b", 0), "0::nat")] thm
  val _ = writeln ("Pure.all inner: " ^ Thm.string_of_thm ctxt result)
  (* should be: \<And>a. a = 0 \<Longrightarrow> 0 = a *)
in () end
\<close>

subsection \<open>Schematic variable instantiation\<close>

text \<open>mp: ?P \<longrightarrow> ?Q \<Longrightarrow> ?P \<Longrightarrow> ?Q\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{thm mp}
  val _ = writeln ("Schematic input: " ^ Thm.string_of_thm ctxt thm)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("P", 0), "True"), (("Q", 0), "False")] thm
  val _ = writeln ("Schematic: " ^ Thm.string_of_thm ctxt result)
  (* should be: True \<longrightarrow> False \<Longrightarrow> True \<Longrightarrow> False *)
in () end
\<close>

subsection \<open>Mixed: Pure.all + HOL.All\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<And>P :: nat \<Rightarrow> bool. (\<forall>x. P x) \<Longrightarrow> (\<forall>x. P x)\<close> by auto}
  val _ = writeln ("Mixed input: " ^ Thm.string_of_thm ctxt thm)
  (* P is Pure.all, x is HOL.All *)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("x", 0), "42::nat")] thm
  val _ = writeln ("Mixed (inst x only): " ^ Thm.string_of_thm ctxt result)
in () end
\<close>

subsection \<open>Mixed: schematic + HOL.All\<close>

ML \<open>
let 
  val ctxt = \<^context>
  (* spec: \<forall>x. ?P x \<Longrightarrow> ?P ?a — x is HOL.All, P and a are schematic *)
  val thm = @{lemma \<open>\<forall>x. P x \<Longrightarrow> \<forall>x. P a\<close> for P a by auto}
  val _ = @{print} thm
  val _ = writeln ("Mixed sch+hol input: " ^ Thm.string_of_thm ctxt thm)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("x", 0), "0::nat"), (("a", 0), "1::nat")] thm
  val _ = writeln ("Mixed sch+hol: " ^ Thm.string_of_thm ctxt result)
in () end
\<close>

subsection \<open>No instantiations (identity)\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{thm conjI}
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt [] thm
  val _ = \<^assert> (Thm.prop_of result = Thm.prop_of thm)
  val _ = writeln "Empty inst: passed"
in () end
\<close>

subsection \<open>Schematic with polymorphic type variable\<close>

text \<open>?a :: ?'a requires type inference during instantiation\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x. P x \<Longrightarrow> P a\<close> for P a by auto}
  val _ = writeln ("Poly schematic input: " ^ Thm.string_of_thm ctxt thm)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("a", 0), "1::nat")] thm
  val _ = writeln ("Poly schematic: " ^ Thm.string_of_thm ctxt result)
  (* ?a :: ?'a should be inferred to nat *)
in () end
\<close>

subsection \<open>Mixed: all three kinds at once\<close>

text \<open>Pure.all + schematic + HOL.All in a single theorem\<close>
ML \<open>
let
  val ctxt = \<^context>
  (* \<And>n. \<forall>x. P x \<Longrightarrow> P a  —  n is Pure.all, x is HOL.All, P and a are schematic *)
  val thm = @{lemma \<open>\<And>n :: nat. \<forall>x. P n x \<Longrightarrow> \<forall>x. P n a\<close> for P a by auto}
  val _ = writeln ("All-three input: " ^ Thm.string_of_thm ctxt thm)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("n", 0), "5::nat"), (("x", 0), "0::nat"), (("a", 0), "1::nat")] thm
  val _ = writeln ("All-three: " ^ Thm.string_of_thm ctxt result)
in () end
\<close>

subsection \<open>HOL.All nested inside HOL.implies\<close>

lemma t1: \<open>\<forall>x :: nat. P x \<longrightarrow> (\<forall>y :: nat. Q x y)\<close> for P Q
  sorry
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{thm t1}
  val _ = writeln ("Nested HOL input: " ^ Thm.string_of_thm ctxt thm)
  (* instantiate inner y only *)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("y", 0), "0::nat")] thm
  val _ = writeln ("Nested HOL (inst y): " ^ Thm.string_of_thm ctxt result)
in () end
\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x :: nat. P x \<longrightarrow> (\<forall>y :: nat. Q x y)\<close> for P Q by auto}
  (* instantiate both *)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("x", 0), "1::nat"), (("y", 0), "2::nat")] thm
  val _ = writeln ("Nested HOL (both): " ^ Thm.string_of_thm ctxt result)
in () end
\<close>

subsection \<open>HOL.All inside Pure.imp (conclusion only)\<close>

ML \<open>
let
  val ctxt = \<^context>
  (* A \<Longrightarrow> \<forall>x. B x — HOL.All in the conclusion, behind Pure.imp *)
  val thm = @{lemma \<open>P \<Longrightarrow> \<forall>x :: nat. Q x\<close> for P Q by auto}
  val _ = writeln ("HOL behind Pure.imp input: " ^ Thm.string_of_thm ctxt thm)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("x", 0), "7::nat")] thm
  val _ = writeln ("HOL behind Pure.imp: " ^ Thm.string_of_thm ctxt result)
in () end
\<close>

subsection \<open>inst_hol_alls preserves schematic indices (zero_var_indexes)\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x. P x \<Longrightarrow> P a\<close> for P a by auto}
  val _ = writeln ("Index input: " ^ Thm.string_of_thm ctxt thm ^
                   " maxidx=" ^ string_of_int (Thm.maxidx_of thm))
  val result = Minilang_Aux.inst_hol_alls ctxt
    [("x", Thm.cterm_of ctxt @{term "0::nat"})] thm
  val _ = writeln ("Index after inst_hol_alls: " ^ Thm.string_of_thm ctxt result ^
                   " maxidx=" ^ string_of_int (Thm.maxidx_of result))
  (* maxidx should be 0 thanks to Drule.zero_var_indexes *)
in () end
\<close>

subsection \<open>inst_universal_quantifiers' with schematic patterns\<close>

text \<open>mode_pattern allows parsing schematic variables like ?f\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x :: nat. P x\<close> for P by auto}
  val _ = writeln ("Pattern input: " ^ Thm.string_of_thm ctxt thm)
  (* instantiate with a schematic — mode_pattern should allow this *)
  val result = Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("x", 0), "?z :: nat")] thm
  val _ = writeln ("Pattern result: " ^ Thm.string_of_thm ctxt result)
in () end
\<close>

subsection \<open>Error case: variable not found\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x :: nat. x = x\<close> by auto}
  val failed = (Minilang_Aux.inst_universal_quantifiers' ctxt
    [(("nonexistent", 0), "0::nat")] thm; false)
    handle ERROR _ => true
  val _ = \<^assert> failed
  val _ = writeln "Error case (not found): passed"
in () end
\<close>

subsection \<open>SPECIALIZE operation (via min_script)\<close>

lemma spec_test_rule: "\<forall>x y :: nat. x < y \<longrightarrow> x \<le> y"
  by auto

text \<open>Full: instantiate + discharge\<close>
lemma "True"    
  by (min_script \<open>
    SPECIALIZE result: spec_test_rule where x = "0" and y = "1"
    END
  \<close>)

text \<open>Auto-naming (no name given)\<close>
lemma "True"
  by (min_script \<open>
    SPECIALIZE spec_test_rule where x = "0" and y = "1"
    END
  \<close>)

text \<open>SPECIALIZE with discharge via WITH\<close>
lemma spec_discharge_rule: "\<forall>x y :: nat. x < y \<longrightarrow> Suc x \<le> y"
  by auto

lemma assumes "0 < (1::nat)" shows "Suc 0 \<le> (1::nat)"
  by (min_script \<open>
    SPECIALIZE result: spec_discharge_rule where x = "0" and y = "1" WITH \<open>0 < 1\<close>
    END
  \<close>)

text \<open>SPECIALIZE with only discharge (no where clause)\<close>
lemma pure_rule: "\<And>P Q. P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q"
  by auto

lemma assumes "True" "False" shows "True \<and> False"
  by (min_script \<open>
    SPECIALIZE result: pure_rule WITH True False
    END
  \<close>)

text \<open>SPECIALIZE with partial discharge\<close>
lemma partial_rule: "\<forall>x y :: nat. x < y \<longrightarrow> x \<le> y"
  by auto

lemma "True"
  by (min_script \<open>
    SPECIALIZE impl: partial_rule where x = "0" and y = "1"
    END
  \<close>)

end
