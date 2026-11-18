(* The concept patch's API, filled in by Minilang.thy when this Isabelle has it (a trial compile
   per hook); NONE on stock Isabelle, where Minilang falls back to the stock logic. *)

structure Minilang_Concept_Hooks =
struct

(*the concept positions of a rule; its consumes counted in positions, also when untagged*)
type concept = {concept_positions: Proof.context -> thm -> int list,
                consumes: Proof.context -> thm -> int}

(*the candidate rules the cases and induct methods try when no rule is given*)
type selection =
  {cases_candidates: Proof.context -> thm list -> term option list list ->
     {rule_fact: thm option, facts: thm list, candidates: thm list},
   induct_candidates: Proof.context -> Proof.context -> thm list -> term option list list ->
     thm list list}

val concept : concept option Unsynchronized.ref = Unsynchronized.ref NONE
val selection : selection option Unsynchronized.ref = Unsynchronized.ref NONE

end
