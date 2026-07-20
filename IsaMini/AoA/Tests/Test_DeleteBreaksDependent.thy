theory Test_DeleteBreaksDependent
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.DeleteBreaksDependent"]]

lemma t: "(0::nat) = 0"
  by  aoa

end
