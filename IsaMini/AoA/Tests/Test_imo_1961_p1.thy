(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_imo_1961_p1 imports Complex_Main
MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent

begin

declare [[auto_interpret_for_embedding=false, agent_AoA_driver="ClaudeCode.claude-opus-4-5"]]
theorem imo_1961_p1:
  fixes x y z a b :: real
  assumes h0 : "0 < x \<and> 0 < y \<and> 0 < z"
    and h1 : "x \<noteq> y"
    and h2 : "y \<noteq> z"
    and h3 : "z \<noteq> x"
    and h4 : "x + y + z = a"
    and h5 : "x^2 + y^2 + z^2 = b^2"
    and h6 : "x * y = z^2"
  shows "0<a \<and> b^2 < a^2 \<and> a^2 < 3*b^2"
  by  aoa


end