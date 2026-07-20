theory Test_BatchFill_HaveObvious
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.BatchFill_HaveObvious"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
