theory Test_Rewrite_Once_Simproc imports
  Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Rewrite_Once_Simproc"]]

text \<open>
  Test that the once-simproc fallback fires when a user-provided rewrite rule
  would cause the simplifier to loop.

  The rule @{text "my_wrap"} rewrites @{text "f x \<equiv> g (f x)"}, which is
  genuinely self-looping: the LHS @{text "f ?x"} matches a subterm of the
  RHS @{text "g (f ?x)"}. The simplifier cannot detect this as permutative
  and will diverge. The once-simproc fallback should wrap the rule so it
  fires at most once, preventing the infinite loop.
\<close>

definition "g (x::nat) \<equiv> x"
consts f :: \<open>'a \<Rightarrow> 'a\<close>

lemma my_wrap: "f x = g (f (x::nat))"
  by (simp add: g_def)

lemma once_simproc_test:
  assumes h1: "f (a::nat) = c"
  shows "g (f a) = c"
  by aoa

end
