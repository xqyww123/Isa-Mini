theory Iso_A2
  imports Iso_Base
begin
axiomatization RR :: "nat \<Rightarrow> bool" where
  ax_rr: "PP n \<Longrightarrow> RR 7"

(* A2 : genuinely schematic -- ?x is determined by the proof, not by INST_VAR *)
schematic_goal caseA2: "RR (?x::nat)"
  by (min_script \<open>
    CONSIDER z::nat where c: "PP z" END WITH ax_ex
    RULE ax_rr
    END WITH c
  \<close>)
ML \<open>report \<^context> "caseA2"\<close>
end
