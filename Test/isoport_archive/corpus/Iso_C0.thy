theory Iso_C0
  imports Iso_Base
begin
lemma caseC0:
  shows c0a: "PP 3" and c0b: "QQ 7"
  by (min_script \<open>
    END WITH ax_p3
  \<close>)
ML \<open>report \<^context> "c0a"; report \<^context> "c0b"\<close>
end
