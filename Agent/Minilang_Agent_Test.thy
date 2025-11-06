theory Minilang_Agent_Test
  imports Minilang_Agent
begin
 

declare [[agent_driver=EchoDebugger, enable_proof_cache=false]]
     
lemma "4 \<le> n \<Longrightarrow> n\<^sup>2 \<le> fact n"
  by agent

(*
lemma "(1::nat) + 1 = 2"
  by agent

theorem induction_divisibility_3div2tooddnp1:
  fixes n ::nat
  shows "(3::nat) dvd (2^(2 * n + 1) + 1)"
by agent *)


end