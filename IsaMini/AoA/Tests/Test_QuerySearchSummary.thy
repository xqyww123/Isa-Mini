theory Test_QuerySearchSummary
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.QuerySearchSummary"]]

lemma "length (xs @ ys) = length xs + length ys"
  by  aoa

end
