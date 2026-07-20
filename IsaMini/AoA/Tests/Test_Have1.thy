theory Test_Have1
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.ProveInTime_ParseError"]]

(* Test: Prove x^2 >= 0 by showing x^2 + 1 > 0 suffices *)
lemma suffices_test1: "(x::int) * x \<ge> 0"
  by Agent AoA

term \<open>Exn.capture\<close>
term \<open>x + x \<ge> 0 \<Longrightarrow> x = x + 0\<close>
ML \<open>Par_Exn\<close>
ML \<open>\<^try>\<open>(Syntax.read_props \<^context> ["1 1 ", "1"]; NONE) catch e => SOME  e\<close>\<close>
end
