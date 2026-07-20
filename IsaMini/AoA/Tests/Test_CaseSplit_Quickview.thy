theory Test_CaseSplit_Quickview
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_Quickview"]]

lemma t_list_qv: "P (l::'a list)"
  by   aoa

end
