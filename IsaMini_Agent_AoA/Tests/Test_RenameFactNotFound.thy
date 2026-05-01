theory Test_RenameFactNotFound
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RenameFactNotFound"]]

lemma assumes h1: "(x::int) \<ge> 0" shows "x \<ge> 0"
  by   aoa

end
