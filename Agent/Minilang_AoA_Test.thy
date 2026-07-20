theory Minilang_AoA_Test
  imports Minilang_AoA
begin
 

declare [[agent_driver=EchoDebugger, enable_proof_cache=false]]
  
lemma t1: "(1::nat) > 0"
(*  by (min_script \<open>END\<close>) *)
  by agent
lemma "4 \<le> n \<Longrightarrow> n\<^sup>2 \<le> fact n"
  by agen

(*
lemma "(1::nat) + 1 = 2"
  by agent

theorem induction_divisibility_3div2tooddnp1:
  fixes n ::nat
  shows "(3::nat) dvd (2^(2 * n + 1) + 1)"
by agent *)


end