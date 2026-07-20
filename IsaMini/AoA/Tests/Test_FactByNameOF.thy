theory Test_FactByNameOF
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FactByNameOF"]]

lemma factbyname_of_test:
  assumes rule: "\<lbrakk>A; B\<rbrakk> \<Longrightarrow> C" and hb: "B" and ha: "A"
  shows "C"
  by aoa

end
