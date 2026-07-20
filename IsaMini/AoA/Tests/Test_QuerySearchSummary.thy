theory Test_QuerySearchSummary
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.QuerySearchSummary"]]

lemma "length (xs @ ys) = length xs + length ys"
  by  aoa

end
