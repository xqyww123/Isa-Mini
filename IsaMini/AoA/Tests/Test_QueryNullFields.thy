theory Test_QueryNullFields
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.QueryNullFields"]]

lemma "a * b + 1 dvd a ^ 2 + b ^ 2 \<Longrightarrow> \<exists>k::nat. k ^ 2 = (a ^ 2 + b ^ 2) div (a * b + 1)"
  by  aoa

end
