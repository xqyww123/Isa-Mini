(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_aime_1998_p4 imports
Complex_Main
(*MathBench_Prover.MathB ench_Prover
Minilang_AoA.Minilang_AoA *)
begin

term \<open>a :: nat\<close>

lemma "a = a"
  by auto

term \<open>a :: nat\<close>


(* declare [[auto_interpret_for_embedding=false, AoA_driver="ClaudeCode"]] *)
theorem aime_1988_p4:
  fixes n :: nat
    and a :: "nat \<Rightarrow> real"
  assumes h0 : "\<And>n. abs (a n) < 1"
    and h1 : "(\<Sum>(k::nat) = 0..(n-1). (abs (a k))) = 19 + abs(\<Sum>(k::nat) = 0..(n-1). (a k))"
  shows "20 \<le> n"
  by   a oa


end