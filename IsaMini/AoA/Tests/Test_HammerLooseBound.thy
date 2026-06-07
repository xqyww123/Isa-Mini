theory Test_HammerLooseBound
  imports Minilang_Agent.Minilang_Agent "HOL-Analysis.Analysis"
begin

declare [[agent_AoA_driver="test.HammerLooseBound"]]

text \<open>
  Regression reproducer for
    exception TERM raised (line 375 of "term.ML"): fastype_of: Bound
  observed on this exact problem (putnam_1970_b4 from PutnamBench).

  The crash happens when the agent drives the FTC block: after Derive
  fundamental_theorem_of_calculus_strong and Rewrite (yielding premise4 with
  a HOL \<forall>x1 binder), the Obvious (HAMMER) on `continuous_on {0..1} x` crashes
  inside run_mepo_and_render / fast_force when traversing the binder and calling
  fastype_of on a subterm carrying a loose de Bruijn Bound.
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
