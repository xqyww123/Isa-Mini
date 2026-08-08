theory Iso_E0
  imports Iso_Base
begin
lemma caseE0: "QQ 7"
  by (min_script \<open>
    CONSIDER "PP 3" | "QQ 7" NEXT WITH ax_p3
    NEXT WITH ax_q7
    END WITH ax_q7
  \<close>)
ML \<open>report \<^context> "caseE0"\<close>
end
