theory Test_Rewrite_Targeted_Drop imports
  Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Rewrite_Targeted_Drop"]]

text \<open>
  Test that dismissing the interaction (selecting no targets) drops the
  looping rule entirely. The Rewrite should proceed with no user-provided
  rules, relying only on the system simplifiers (if enabled) or failing
  gracefully.
\<close>

definition "g (x::nat) \<equiv> x"
consts f :: \<open>'a \<Rightarrow> 'a\<close>

lemma my_wrap: "f x = g (f (x::nat))"
  by (simp add: g_def)

lemma drop_test:
  assumes h1: "f (a::nat) = c"
  shows "g (f a) = c"
  by  aoa

end
