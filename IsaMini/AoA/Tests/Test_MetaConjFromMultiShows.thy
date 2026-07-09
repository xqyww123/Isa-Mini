theory Test_MetaConjFromMultiShows
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.MetaConjFromMultiShows"]]

(* Reproduces the "meta conjunction" obstacle seen in mbzuai log e9912b2bf_8
   (= avl_AVL_front_nodeqtvc). The why3->Isabelle VC export emits one `shows`
   clause per verification condition, e.g.

     theorem front_node'vc:
       shows "case o1 of AEmpty => True | ANode .. => 0 <= hgt (m1 l) & .."
       and   "ALL result. (case o1 of ..) --> result = .."

   Isar bundles multiple `shows .. and ..` clauses into a SINGLE goal that is a
   Pure meta-conjunction `A &&& B` (Pure.conjunction), NOT a HOL `A & B`. The
   Minilang goal printer atomizes meta-connectives to object logic for display,
   so the agent SEES `A & B` while the underlying term is `A &&& B`. Every
   object-level conjunction operation (SplitConjs, Derive/InferenceRule conjI,
   ..) then fails on the real `&&&`.

   The two atomic clauses below produce goal `P &&& Q`, which displays as
   `P & Q` but is rejected by SplitConjs. *)
lemma
  shows "(P::bool)"
  and "(Q::bool)"
  by aoa

end
