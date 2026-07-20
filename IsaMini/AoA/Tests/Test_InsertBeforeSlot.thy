theory Test_InsertBeforeSlot
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.InsertBeforeSlot"]]

lemma insert_before_slot_test: "(x::int) * x \<ge> 0"
  by Agent AoA

end
