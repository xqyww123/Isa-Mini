theory Test_HaveSchematicVar imports Complex_Main
  Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HaveSchematicVar"]]

(* AoA rejects a Have whose statement carries schematic variables (agent.ML
   `reject_schematic_goal`), pointing the agent at `for_any` instead.  Minilang's
   own HAVE supports them -- the guard is an AoA-level policy, not a limitation
   of the proof language. *)

lemma have_schematic_var_test: "\<bar>x::real\<bar> = max x 0 + max (- x) 0"
  by aoa

end
