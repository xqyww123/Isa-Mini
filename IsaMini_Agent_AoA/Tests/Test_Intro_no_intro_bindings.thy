theory Test_Intro_no_intro_bindings
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Intro_no_intro_bindings"]]

lemma t_bool: "P (b::bool)"
  by  aoa

end
