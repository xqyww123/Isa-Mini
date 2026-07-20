theory Test_Rewrite_LoopingForkCtxt imports
  Minilang_AoA.Minilang_AoA
begin

 declare [[AoA_driver="ClaudeCode"]] (* declare [[AoA_driver="test.Rewrite_LoopingForkCtxt"]] *)

definition "g (x::nat) \<equiv> x"
consts f :: \<open>'a \<Rightarrow> 'a\<close>

lemma my_wrap: "f x = g (f (x::nat))"
  by (simp add: g_def)

lemma looping_fork_test:
  assumes h1: "f (a::nat) = c"
  shows "g (f a) = c"
  by aoa

end
