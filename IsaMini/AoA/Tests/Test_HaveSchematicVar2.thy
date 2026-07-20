theory Test_HaveSchematicVar2 imports Complex_Main
  Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.HaveSchematicVar2"]]

(* Companion of Test_HaveSchematicVar.thy: two schematic variables, so the
   rejection message must name both. *)

lemma have_schematic_var2_test: "(x::nat) + y = y + x"
  by aoa

end
