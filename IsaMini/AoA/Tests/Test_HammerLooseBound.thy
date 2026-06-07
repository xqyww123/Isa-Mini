theory Test_HammerLooseBound
  imports Minilang_Agent.Minilang_Agent "HOL-Analysis.Analysis"
begin

declare [[agent_AoA_driver="test.HammerLooseBound"]]

text \<open>
  Regression reproducer for
    exception TERM raised (line 375 of "term.ML"): fastype_of: Bound

  This is the production case putnam_1970_b4 (data/PutnamBench/isabelle), with
  the SAME imports (HOL-Analysis.Derivative) so the sledgehammer/mepo background
  fact database matches the original run. The driver (test.HammerLooseBound)
  replays the production proof up to the crashing Obvious at step `x_cont`.
\<close>

theorem putnam_1970_b4:
  fixes x :: "real \<Rightarrow> real"
  assumes hdiff : "x differentiable_on {0::real..1} \<and> (deriv x) differentiable_on {0::real..1}"
    and hx : "x 1 - x 0 = 1"
    and hv : "deriv x 0 = 0 \<and> deriv x 1 = 0"
    and hs : "\<forall> t \<in> {(0::real)<..<1}. \<bar>deriv x t\<bar> \<le> 3/2"
  shows "\<exists> t \<in> {(0::real)..1}. \<bar>(deriv (deriv x)) t\<bar> \<ge> 9/2"
  by aoa

end
