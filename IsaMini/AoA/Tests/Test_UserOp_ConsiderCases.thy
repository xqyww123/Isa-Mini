theory Test_UserOp_ConsiderCases
  imports Sample_Plugin
begin

declare [[AoA_driver="test.UserOp_ConsiderCases"]]

lemma "(x::int) * x \<ge> 0"
  by aoa

end
