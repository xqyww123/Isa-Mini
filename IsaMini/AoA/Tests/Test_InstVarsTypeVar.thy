theory Test_InstVarsTypeVar
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InstVarsTypeVar"]]

(* Residual schematic TYPE variable: InstVarsInGoal's leading-' name form must
   take a type expression as value; refl then closes the goal. *)
schematic_goal "(?y::?'a) = ?y"
  by aoa

end
