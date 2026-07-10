theory Test_HaveSchematicVar imports Complex_Main
  Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HaveSchematicVar"]]

(* HAVE is built on `Specification.schematic_theorem_cmd`, so a `?x` in the
   statement is accepted.  Isar's `generic_goal` then prepends one `TERM ?v`
   conjunct per schematic variable (Pure/Isar/proof.ML `implicit_vars`), which
   `gen_HAVE'` does not account for -> `unflat` raises UnequalLengths. *)

lemma have_schematic_var_test: "\<bar>x::real\<bar> = max x 0 + max (- x) 0"
  by aoa

end
