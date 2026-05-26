theory Test_Chaining_NoCounter_AutoName
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Chaining_NoCounter_AutoName"]]

(* Test: Chaining without explicit name under No_Counter mode.
   The agent server sets counter_mode="none", so auto-name generation
   via map_fact_counter must not crash. *)
lemma chaining_noname_test:
  fixes a b c :: nat
  assumes ab: "a = b" and bc: "b \<le> c"
  shows "a \<le> c"
  by  aoa

end
