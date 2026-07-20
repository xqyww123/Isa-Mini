theory Test_SubagentSlotResolve
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SubagentSlotResolve"]]

lemma subagent_slot_resolve: "(0::int) \<le> z * z"
  by Agent AoA

end
