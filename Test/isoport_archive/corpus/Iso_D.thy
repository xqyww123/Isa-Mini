theory Iso_D
  imports Iso_Base
begin
(* D : plain goal, no conjunction, no schematic (regression control) *)
lemma caseD: "QQ 7"
  by (min_script \<open>
    CONSIDER z::nat where c: "PP z" END WITH ax_ex
    END WITH ax_q7
  \<close>)
ML \<open>report \<^context> "caseD"\<close>
end
