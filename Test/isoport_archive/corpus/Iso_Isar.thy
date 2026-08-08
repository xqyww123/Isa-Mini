theory Iso_Isar
  imports Iso_Base
begin
(* pure-Isar control: does plain `obtain` work inside a schematic_goal? *)
schematic_goal caseIsar: "QQ (?x::nat)"
proof -
  obtain z :: nat where "PP z" using ax_ex by blast
  show "QQ 7" by (rule ax_q7)
qed
ML \<open>report \<^context> "caseIsar"\<close>
end
