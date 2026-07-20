theory Test_Interpret_NoInstantiations
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Interpret_NoInstantiations"]]

(* `instantiations` is optional in the schema. A parameterless locale is
   interpreted with no `where` clause at all -- exercising the empty branch of
   `interpret_i`'s where-clause assembly. *)

locale ini_two = assumes ini_gt: "(1::nat) < 2"
begin
lemma ini_zero_lt: "(0::nat) < 2" by simp
end

lemma "(0::nat) < 2"
  by aoa

end
