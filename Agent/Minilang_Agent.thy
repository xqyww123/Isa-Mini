theory Minilang_Agent
  imports Minilang.Minilang Isa_REPL.Isa_REPL
begin

ML_file "agent.ML"
ML_file "agent_packer.ML"
ML_file "agent_server.ML"
ML_file "tactic.ML"

method_setup agent = \<open>
  Scan.succeed (K MiniLang_Agent.method)
\<close>

end