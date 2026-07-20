theory Test_Compute1
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Compute1"]]

lemma compute_test1:
  shows "(3::nat) * 7 = 21"
  by aoa

end
