theory Test_SpliceHaveRefresh
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SpliceHaveRefresh"]]

lemma "\<not> False \<and> True"
  by aoa

end
