theory Test_FactByNameFlip
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.FactByNameFlip"]]

lemma factbyname_flip_test:
  assumes h: "(a :: nat) = b"
  shows "b = a"
  by aoa

end
