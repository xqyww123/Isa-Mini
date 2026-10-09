theory Test_UserOp_WithInduction
  imports Sample_Plugin
begin

declare [[AoA_driver="test.UserOp_WithInduction"]]

lemma "rev (rev (l::nat list)) = l \<and> True"
  by aoa

end
