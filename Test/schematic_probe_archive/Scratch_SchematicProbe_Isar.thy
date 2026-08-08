theory Scratch_SchematicProbe_Isar
  imports Minilang.Minilang
begin

axiomatization RR :: "nat \<Rightarrow> bool" where
  rr_rule: "RR n"

section \<open>INDUCT / CASE_SPLIT through the real Isar path\<close>

text \<open>Control: plain lemma, no schematic anywhere.\<close>
lemma ctl_induct: "rev (rev (ys::nat list)) = ys"
  apply (min_script \<open>INDUCT ys PRINT\<close>)
  oops

lemma ctl_case: "rev (rev (ys::nat list)) = ys"
  apply (min_script \<open>CASE_SPLIT ys PRINT\<close>)
  oops

text \<open>Same, but a schematic \<open>?x\<close> sits in another conjunct.\<close>
schematic_goal p_induct: "rev (rev (ys::nat list)) = ys \<and> RR ?x"
  apply (min_script \<open>INDUCT ys PRINT\<close>)
  oops

schematic_goal p_case: "rev (rev (ys::nat list)) = ys \<and> RR ?x"
  apply (min_script \<open>CASE_SPLIT ys PRINT\<close>)
  oops

text \<open>Case split ON a term that contains the schematic.\<close>
schematic_goal p_case_on_schematic: "RR ?x \<or> \<not> RR ?x"
  apply (min_script \<open>CASE_SPLIT "RR ?x" PRINT\<close>)
  oops

text \<open>Induct on the schematic itself.\<close>
schematic_goal p_induct_on_schematic: "rev (rev (?xs::nat list)) = ?xs"
  apply (min_script \<open>INDUCT ?xs PRINT\<close>)
  oops

section \<open>BRANCH and CONTRADICTION\<close>

schematic_goal p_branch: "RR ?x"
  apply (min_script \<open>CONSIDER c1: "RR (1::nat)" | c2: "RR (2::nat)" PRINT\<close>)
  oops

schematic_goal p_ccontr: "RR ?x"
  apply (min_script \<open>RULE ccontr PRINT\<close>)
  oops

section \<open>Does a finished Minilang proof really export a schematic theorem?\<close>

schematic_goal exported_schematic: "?x + 0 = (?x::nat)"
  by (min_script \<open>END\<close>)

thm exported_schematic

schematic_goal exported_pinned: "(?x::nat) = 0"
  by (min_script \<open>END\<close>)

thm exported_pinned

ML \<open>
writeln ("exported_schematic = " ^
  Syntax.string_of_term \<^context> (Thm.prop_of @{thm exported_schematic}));
writeln ("exported_pinned = " ^
  Syntax.string_of_term \<^context> (Thm.prop_of @{thm exported_pinned}));
\<close>

text \<open>Now use the exported schematic fact at an arbitrary instance.\<close>
lemma use_it: "(5::nat) + 0 = 5"
  by (rule exported_schematic)

section \<open>INTERPRET (OPEN_MODULE) and SETUP_REWRITING-shaped HAVE\<close>

locale probe_loc =
  fixes k :: nat
  assumes k_pos: "0 < k"
begin
lemma k_nonzero: "k \<noteq> 0" using k_pos by simp
end

schematic_goal p_interpret: "RR ?x"
  apply (min_script \<open>OPEN_MODULE probe_loc where k = "1::nat" PRINT\<close>)
  oops

text \<open>SETUP_REWRITING is (agent.ML:1785-1830) a HAVE of `redex = residue`.\<close>
schematic_goal p_setup_rewriting: "RR ?x"
  apply (min_script \<open>HAVE eqn: "(0::nat) + 0 = 0" PRINT\<close>)
  oops

end
