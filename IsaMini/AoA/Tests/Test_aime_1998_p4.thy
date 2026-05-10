(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_aime_1998_p4 imports
MathBench_Prover.MathBench_Prover
Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false, agent_AoA_driver="ClaudeCode"]]
theorem aime_1988_p4:
  fixes n :: nat
    and a :: "nat \<Rightarrow> real"
  assumes h0 : "\<And>n. abs (a n) < 1"
    and h1 : "(\<Sum>(k::nat) = 0..(n-1). (abs (a k))) = 19 + abs(\<Sum>(k::nat) = 0..(n-1). (a k))"
  shows "20 \<le> n"
  by    aoa


end