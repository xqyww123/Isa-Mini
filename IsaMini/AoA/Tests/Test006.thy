theory Test006
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit"]]
(*declare [[AoA_driver="ClaudeCode"]]*)

lemma t4: "rev (rev l) = l"
  by  Age ntAoA

end