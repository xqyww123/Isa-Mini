theory Test_UserOp_HaveText
  imports Sample_Plugin
begin

declare [[AoA_driver="test.UserOp_HaveText"]]

lemma "(x::int) * x \<ge> 0"
  by aoa

end
