theory Test_ExperienceMemory
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.ExperienceMemory"]]

lemma t1: "(1::real) \<le> 2"
  by   aoa

end
