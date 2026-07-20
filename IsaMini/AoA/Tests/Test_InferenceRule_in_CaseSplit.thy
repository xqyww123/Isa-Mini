theory Test_InferenceRule_in_CaseSplit
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InferenceRule_in_CaseSplit"]]

lemma t: "P (b::bool) \<or> Q b"
  by  aoa

end
