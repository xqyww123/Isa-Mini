theory Test_Rewrite_Targeted imports
  Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Rewrite_Targeted"]]

text \<open>
  Test interactive target selection for looping rewrite rules.
  The rule @{text "my_wrap"} rewrites @{text "f x \<equiv> g (f x)"}, which is
  self-looping. The goal contains two matching subterms: @{text "f a"}
  and @{text "f b"}. The test selects only @{text "f a"} to rewrite,
  leaving @{text "f b"} untouched.
\<close>

definition "g (x::nat) \<equiv> x"
consts f :: \<open>'a \<Rightarrow> 'a\<close>

lemma my_wrap: "f x = g (f (x::nat))"
  by (simp add: g_def)

lemma targeted_test:
  assumes h1: "f (a::nat) = c"
      and h2: "f (b::nat) = d"
  shows "g (f a) + f b = c + d"
  by  aoa

end
