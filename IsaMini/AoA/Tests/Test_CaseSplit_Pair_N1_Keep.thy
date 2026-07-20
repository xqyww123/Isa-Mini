theory Test_CaseSplit_Pair_N1_Keep
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_Pair_N1_Keep"]]

lemma t_pair: "P (p :: 'a \<times> 'b)"
  by aoa

end
