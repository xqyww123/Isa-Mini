theory Iso_B
  imports Iso_Base
begin
(* B : schematic_goal, two schematic vars -> nested &&& *)
schematic_goal caseB: "QQ (?x::nat) \<and> PP (?y::nat)"
  by (min_script \<open>
    INST_VAR ?x = "(7::nat)" and ?y = "(3::nat)"
    CONSIDER z::nat where c: "PP z" END WITH ax_ex
    END WITH ax_q7 ax_p3
  \<close>)
ML \<open>report \<^context> "caseB"\<close>
end
