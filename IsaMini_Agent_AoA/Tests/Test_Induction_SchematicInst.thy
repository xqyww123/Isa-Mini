theory Test_Induction_SchematicInst
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_SchematicInst"]]

text \<open>
  Phase 3 end-to-end: FactByName + schematic-variable instantiation.
  `int_le_induct` has a schematic `?k` appearing in its consume premise
  (`i \<le> ?k`); the Phase 3 flow must surface an
  `Interaction_InstantiateSchematics` asking the agent to make `?k`
  concrete, then compose `int_le_induct[where ?k = k]` and hand it down
  to Minilang's INDUCT.
\<close>

lemma \<open>i \<le> k \<Longrightarrow> (i::int) + k \<ge> 2 * i\<close>
  by aoa

end
