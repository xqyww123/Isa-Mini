theory Test_SemanticKNN_lexerr
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SemanticKNN_lexerr"]]

lemma "coprime (m::nat) n \<Longrightarrow> \<not> (2 dvd m \<and> 2 dvd n)"
  by  aoa

end
