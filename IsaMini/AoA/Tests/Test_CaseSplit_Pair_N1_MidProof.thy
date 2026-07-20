theory Test_CaseSplit_Pair_N1_MidProof
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CaseSplit_Pair_N1_MidProof"]]

lemma t_pair: "P (p :: 'a \<times> 'b)"
  by aoa

end
