theory Test_SubagentHintScopeOneShot
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.SubagentHintScopeOneShot"]]

lemma subagent_hint_scope_oneshot_test: "(x::int) * x \<ge> 0"
  by aoa

end
