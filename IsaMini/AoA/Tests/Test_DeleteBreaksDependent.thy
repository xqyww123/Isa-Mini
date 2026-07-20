theory Test_DeleteBreaksDependent
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.DeleteBreaksDependent"]]

lemma t: "(0::nat) = 0"
  by  aoa

end
