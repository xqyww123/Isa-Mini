theory Test_RenameVarNotFound
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.RenameVarNotFound"]]

lemma "(x::int) * x \<ge> 0"
  by   aoa

end
