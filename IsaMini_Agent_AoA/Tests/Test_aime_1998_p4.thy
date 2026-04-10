(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_aime_1998_p4 imports
Complex_Main
Minilang_Agent.Minilang_Agent
begin

theorem aime_1988_p4:
  fixes n :: nat
    and a :: "nat \<Rightarrow> real"
  assumes h0 : "\<And>n. abs (a n) < 1"
    and h1 : "(\<Sum>(k::nat) = 0..(n-1). (abs (a k))) = 19 + abs(\<Sum>(k::nat) = 0..(n-1). (a k))"
  shows "20 \<le> n"
  by   aoa


end