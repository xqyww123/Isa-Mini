theory Test_UserOp_HaveText_Schematic
  imports Sample_Plugin
begin

declare [[AoA_driver="test.UserOp_HaveText_Schematic"]]

consts PP :: "nat \<Rightarrow> bool"
lemma pp7: "PP 7" sorry

schematic_goal "PP ?x"
  by aoa

end
