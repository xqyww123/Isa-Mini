theory Test_ResolveNotation
  imports Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ResolveNotation"]]

lemma resolve_notation_test: "(n::nat) = n"
  by aoa

end
