theory Test_SimpRoles
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0"
| "double (Suc n) = Suc (Suc (double n))"

declare [[AoA_driver="test.SimpRoles"]]

lemma "double n = 2 * n"
  by aoa

end
