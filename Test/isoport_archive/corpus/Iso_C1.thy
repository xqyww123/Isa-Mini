theory Iso_C1
  imports Iso_Base
begin
lemma caseC1:
  shows c1a: "PP 3" and c1b: "QQ 7"
  by (min_script \<open>
    CONSIDER z::nat where c: "PP z" END WITH ax_ex
    END WITH ax_p3
  \<close>)
ML \<open>report \<^context> "c1a"; report \<^context> "c1b"\<close>
end
