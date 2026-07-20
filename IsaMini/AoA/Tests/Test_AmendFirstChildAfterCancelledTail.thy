theory Test_AmendFirstChildAfterCancelledTail
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AmendFirstChildAfterCancelledTail"]]

lemma t1:
  assumes hP: "P"
      and hQ: "Q"
  shows "P \<and> Q"
  by aoa

end
