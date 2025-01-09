theory Minilang_Base
  imports HOL.HOL
begin

definition \<open>TAG X \<equiv> X\<close>
definition \<open>GOAL (X::prop) \<equiv> X\<close>
definition \<open>ISO_ALL \<equiv> HOL.All\<close>
definition \<open>ISO_IMP \<equiv> HOL.implies\<close>
definition \<open>ISO_PROP (X::bool) \<equiv> X\<close>

lemma ISO_PROP:
  \<open>Trueprop (ISO_PROP P) \<equiv> Pure.prop (Trueprop P)\<close>
  unfolding ISO_PROP_def Pure.prop_def .

ML_file \<open>./library/aux_thms.ML\<close>

hide_fact ISO_PROP

end
