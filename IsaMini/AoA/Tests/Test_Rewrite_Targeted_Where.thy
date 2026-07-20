theory Test_Rewrite_Targeted_Where imports
  Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Rewrite_Targeted_Where"]]

definition "g (x::nat) \<equiv> x"
consts f :: \<open>'a \<Rightarrow> 'a\<close>

lemma my_looping: "f x = g (f (x::nat))"
  by (simp add: g_def)

lemma targeted_where_test:
  assumes h1: "f (a::nat) = c"
  shows "g (f a) = c"
  by aoa

end
