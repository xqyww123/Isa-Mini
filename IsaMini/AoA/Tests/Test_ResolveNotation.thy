theory Test_ResolveNotation
  imports Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ResolveNotation"]]

lemma resolve_notation_test: "(n::nat) = n"
  by aoa

end
