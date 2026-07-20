theory Test_InsertBeforeSlot
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InsertBeforeSlot"]]

lemma insert_before_slot_test: "(x::int) * x \<ge> 0"
  by Agent AoA

end
