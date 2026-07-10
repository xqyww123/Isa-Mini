theory Test_HaveSchematicVar2 imports Complex_Main
  Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HaveSchematicVar2"]]

(* Companion of Test_HaveSchematicVar.thy: with >= 2 schematic variables the
   `unflat` in `gen_HAVE'`'s `preruns` already has a leftover conjunct, so the
   Have blows up while being *opened*, before its body ever runs. *)

lemma have_schematic_var2_test: "(x::nat) + y = y + x"
  by aoa

end
