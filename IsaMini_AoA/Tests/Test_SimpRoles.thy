theory Test_SimpRoles
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0"
| "double (Suc n) = Suc (Suc (double n))"

declare [[agent_AoA_driver="test.SimpRoles"]]

lemma "double n = 2 * n"
  by aoa

end
