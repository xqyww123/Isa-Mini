theory Test_Induction_IHRename
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_IHRename"]]

text \<open>
  Reproducer: the Induction case's IH displays an Isabelle-internal
  variant of the induction variable (e.g. ``na__``) instead of the
  external display name (``n``) shown in the same step's
  ``fixing variables`` header.

  Observed (from log ``edit target_step='5.2'``)::

    step 5: Have gen
      step 5.1: Intro
      step 5.2: Induction n :: nat
        fixing variables:
          - n: nat
        assuming premises:
          - premise2: n \<le> p - (2 :: nat)
          - 1.IH: \<forall>m<na__. \<forall>x \<le> p - (2 :: nat). prime (f x)

  Outer theorem context: f :: nat \<Rightarrow> nat, p :: nat, i :: nat, plus
  prior premises premise0, premise1 (hence premise2 at the Have's
  Intro). The induction happens INSIDE a Have sub-proof, which is the
  structural detail the first (top-level) reproducer was missing.
\<close>

lemma
  fixes f :: "nat \<Rightarrow> nat" and p :: nat and i :: nat
  shows "True"
  by aoa

end
