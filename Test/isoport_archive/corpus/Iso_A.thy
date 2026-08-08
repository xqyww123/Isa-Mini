theory Iso_A
  imports Iso_Base
begin
(* A : schematic_goal, one schematic var *)
schematic_goal caseA: "QQ (?x::nat)"
  by (min_script \<open>
    INST_VAR ?x = "(7::nat)"
    CONSIDER z::nat where c: "PP z" END WITH ax_ex
    END WITH ax_q7
  \<close>)
ML \<open>report \<^context> "caseA"\<close>
end
