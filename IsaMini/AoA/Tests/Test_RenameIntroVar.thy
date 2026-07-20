theory Test_RenameIntroVar
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RenameIntroVar"]]

lemma "\<forall>x::nat. x = x"
  by   aoa

end
