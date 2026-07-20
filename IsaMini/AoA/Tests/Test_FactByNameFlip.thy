theory Test_FactByNameFlip
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FactByNameFlip"]]

lemma factbyname_flip_test:
  assumes h: "(a :: nat) = b"
  shows "b = a"
  by aoa

end
