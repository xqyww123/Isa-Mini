theory Iso_C2
  imports Iso_Base
begin
lemma caseC2:
  shows c2a: "PP 3" and c2b: "QQ 7"
  by (min_script \<open>
    CONSIDER z::nat where c: "PP z" END WITH ax_ex
    NEXT WITH ax_p3
    END WITH ax_q7
  \<close>)
ML \<open>report \<^context> "c2a"; report \<^context> "c2b"\<close>
end
