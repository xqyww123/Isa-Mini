theory Test_Specialize6
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Derive6"]]

lemma specialize_test6:
  assumes h1: "(x::nat) mod q = y mod q"
      and h2: "coprime q (2::nat)"
  shows "x mod q = y mod q"
  by aoa

end
