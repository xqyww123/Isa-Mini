theory Test_UserOp_Consider
  imports Sample_Plugin
begin

declare [[AoA_driver="test.UserOp_Consider"]]

consts PP :: "nat \<Rightarrow> bool"
consts QQ :: "nat \<Rightarrow> bool"

schematic_goal "PP 7 \<and> QQ ?y"
  by aoa

end
