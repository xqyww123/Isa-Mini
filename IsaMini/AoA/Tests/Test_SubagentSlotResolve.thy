theory Test_SubagentSlotResolve
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SubagentSlotResolve"]]

lemma subagent_slot_resolve: "(0::int) \<le> z * z"
  by Agent AoA

end
