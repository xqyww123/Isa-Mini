theory Iso_E
  imports Iso_Base
begin
schematic_goal caseE: "QQ (?x::nat)"
  by (min_script \<open>
    INST_VAR ?x = "(7::nat)"
    CONSIDER "PP 3" | "QQ 7" NEXT WITH ax_p3
    NEXT WITH ax_q7
    END WITH ax_q7
  \<close>)
ML \<open>report \<^context> "caseE"\<close>
end
