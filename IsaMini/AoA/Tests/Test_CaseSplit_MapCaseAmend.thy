theory Test_CaseSplit_MapCaseAmend
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_MapCaseAmend"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
