theory Test_DeleteIntro
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.DeleteIntro"]]

lemma conj_test:
  assumes "P" and "Q" and "R"
  shows "P \<and> Q \<and> R"
  by   aoa

end
