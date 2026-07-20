theory Test_Induction_AmendTargetFree
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_AmendTargetFree"]]

text \<open>
  Regression test for the "target-in-arbitrary on amend" bug
  (see contrib/Isa-Mini/Test/Induct_HO_Unif_Probe.thy for the underlying
  ML-level pathology).

  Agent flow originally observed in
  \<^verbatim>\<open>$ISABELLE_HOME_USER/log/AoA/DAF690E06_168BB2A/proofs.yaml\<close>
  (2026-04-21 17:46:25--31, Rabinowitz):

    1. fill step 1 with
         [Intro(var_bindings=[i], fact_bindings=[ile]),
          Induction(target=i, rule=less_induct,
                    variables=[i generalized, ile generalized])]
       \<rightarrow> step 2 fails Python validation "f and p not classified"
          (but Python-side kept \<open>i\<close> in self.variables because the
           \<open>if is_init:\<close> guard at model.py:6235 is skipped on amend).

    2. amend step 2 with
         Induction(target=i, rule=less_induct,
                   variables=[i generalized, ile generalized,
                              f fixed, p fixed])
       Before the fix: \<open>beginning_opr()\<close> emits
         \<open>INDUCT(('i', None, ['i', 'ile'], 'less_induct'))\<close>
       ie target \<open>i\<close> appears in the ML \<open>arbitrary:\<close> slot, which
       triggers a degenerate HO unification and an IH of shape
         \<open>less.IH: ?y < x \<longrightarrow> ?i \<le> p-2 \<longrightarrow> prime (f ?i)\<close>
       (two independent schematics).

       After the fix: target-stripping at model.py:6235 is unconditional,
       so the amend emits
         \<open>INDUCT(('i', None, ['ile'], 'less_induct'))\<close>
       and the IH is well-formed:
         \<open>less.IH: \<lbrakk>?y < x; ?y \<le> p-2\<rbrakk> \<Longrightarrow> prime (f ?y)\<close>.

  This test exercises that sequence against a minimal Rabinowitz-shape
  goal and asserts the resulting IH is well-formed.
\<close>

lemma
  fixes f :: "nat \<Rightarrow> nat" and p :: nat and Q :: "nat \<Rightarrow> bool"
  assumes h0: "\<And>x. f x = x * x + x + p"
  assumes h1: "\<And>k. k \<le> p div 3 \<Longrightarrow> Q (f k)"
  shows "\<forall>i. i \<le> p - 2 \<longrightarrow> Q (f i)"
  by aoa

end
