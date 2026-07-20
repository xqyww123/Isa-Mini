theory Test_HaveLeakSibling
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.HaveLeakSibling"]]

lemma "(1::nat) + 1 = 2 \<and> (2::nat) + 2 = 4"
  by  aoa

end
