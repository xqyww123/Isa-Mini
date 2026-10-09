theory Test_UserOp_ApplyShared
  imports Sample_Plugin
begin

declare [[AoA_driver="test.UserOp_ApplyShared"]]

lemma assumes "a = b" and "b = c" shows "(a::nat) = c"
  by aoa

end
