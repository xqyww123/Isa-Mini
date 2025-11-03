theory Minilang_Agent
  imports Minilang.Minilang Isa_REPL.Isa_REPL Complex_Main
begin

declare [[ML_debugger, ML_exception_trace, ML_exception_debugger]]

ML_file "agent.ML"
ML_file "agent_packer.ML"
ML_file "agent_server.ML"
ML_file "tactic.ML"

method_setup agent = \<open>
  Scan.succeed (K MiniLang_Agent.method)
\<close>

declare [[agent_driver=EchoDebugger]]

(*
lemma "\<exists>k. 0 < k"
  by agent*)


lemma "(1::nat) + 1 = 2"
  by agent

(*
lemma "(1::nat) + 1 = 2"
  by agent

theorem induction_divisibility_3div2tooddnp1:
  fixes n ::nat
  shows "(3::nat) dvd (2^(2 * n + 1) + 1)"
by agent *)

end