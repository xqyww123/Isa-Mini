theory Test_HaveDupFixed
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HaveDupFixed"]]

lemma "\<forall>(a::nat) b. a * b + 1 dvd a^2 + b^2 \<longrightarrow> (\<exists>x::nat. real (x^2) = real (a^2 + b^2) / real (a * b + 1))"
  by aoa

end
