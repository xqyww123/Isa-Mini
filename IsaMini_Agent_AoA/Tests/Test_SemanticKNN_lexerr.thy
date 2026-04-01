theory Test_SemanticKNN_lexerr
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.SemanticKNN_lexerr"]]

lemma "coprime (m::nat) n \<Longrightarrow> \<not> (2 dvd m \<and> 2 dvd n)"
  by AgentAoA

end
