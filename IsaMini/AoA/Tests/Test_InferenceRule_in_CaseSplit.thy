theory Test_InferenceRule_in_CaseSplit
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.InferenceRule_in_CaseSplit"]]

lemma t: "P (b::bool) \<or> Q b"
  by  aoa

end
