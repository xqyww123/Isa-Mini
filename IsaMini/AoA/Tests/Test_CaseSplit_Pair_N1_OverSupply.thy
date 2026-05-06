theory Test_CaseSplit_Pair_N1_OverSupply
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_Pair_N1_OverSupply"]]

lemma t_pair: "P (p :: 'a \<times> 'b)"
  by aoa

end
