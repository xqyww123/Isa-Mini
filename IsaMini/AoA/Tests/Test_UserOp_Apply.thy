theory Test_UserOp_Apply
  imports Sample_Plugin
begin

declare [[AoA_driver="test.UserOp_Apply"]]

lemma "(x::int) * x \<ge> 0 \<and> (y::int) * y \<ge> 0"
  by aoa

end
