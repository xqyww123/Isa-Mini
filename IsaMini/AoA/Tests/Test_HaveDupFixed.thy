theory Test_HaveDupFixed
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HaveDupFixed"]]

lemma "\<forall>(a::nat) b. a * b + 1 dvd a^2 + b^2 \<longrightarrow> (\<exists>x::nat. real (x^2) = real (a^2 + b^2) / real (a * b + 1))"
  by aoa

end
