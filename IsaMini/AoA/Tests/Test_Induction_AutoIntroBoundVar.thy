theory Test_Induction_AutoIntroBoundVar
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Induction_AutoIntroBoundVar"]]

lemma t: "(x::int) * x \<ge> 0"
  by aoa

end
