theory Test_SubagentHintScopeOneShot
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SubagentHintScopeOneShot"]]

lemma subagent_hint_scope_oneshot_test: "(x::int) * x \<ge> 0"
  by aoa

end
