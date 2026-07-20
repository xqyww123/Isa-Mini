theory Test_FillCancelledPredecessor
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.FillCancelledPredecessor"]]

lemma t1:
  assumes hP: "P"
      and hQ: "Q"
  shows "P \<and> Q"
  by aoa

end
