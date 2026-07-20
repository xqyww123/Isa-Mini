theory Test005
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="CaseSplit"]]
(*declare [[AoA_driver="ClaudeCode"]]*)

lemma t4: "x * x \<ge> 0" for x :: int
  by aoa

end