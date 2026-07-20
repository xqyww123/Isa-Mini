theory Test_Intro_no_intro_bindings
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Intro_no_intro_bindings"]]

lemma t_bool: "P (b::bool)"
  by  aoa

end
