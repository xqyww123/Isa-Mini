theory Test_SymbolicFactName
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin
declare [[AoA_driver="test.SymbolicFactName"]]

(* The whole point of this fixture: fact names carrying Isabelle symbols, so a
   name that is not converted to ASCII notation before it is sent cannot
   resolve.  `the_\<phi>` mirrors the phi-system name the defect was found on;
   `sym_pair\<^sub>R` adds a sub-script, a differently-shaped symbol. *)
lemma the_\<phi>: "(0::int) \<le> x * x"
  by simp

lemma sym_pair\<^sub>R: "(1::int) \<le> 1" "(2::int) \<le> 2"
  by simp_all

(* A name that resolves but binds nothing, for the three-way split between
   "no such name", "index past the end" and "resolves to zero theorems". *)
named_theorems empty_coll\<^sub>R

lemma symbolic_fact_name_test: "(0::int) \<le> y * y"
  by aoa

end
