theory Test_DeleteIntro
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.DeleteIntro"]]

lemma conj_test:
  assumes "P" and "Q" and "R"
  shows "P \<and> Q \<and> R"
  by   aoa

end
