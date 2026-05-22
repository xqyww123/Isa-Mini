theory Sturm_Test
  imports MathBench_Prover.MathBench_Prover
begin

section \<open>Basic: sturm method works\<close>

subsection \<open>Global positivity\<close>
lemma "\<forall>x::real. x^2 + 1 > 0" by sturm
lemma "\<forall>x::real. x^4 + x^2 + 1 > 0" by sturm

subsection \<open>No-roots\<close>
lemma "\<forall>x::real. x^2 + 1 \<noteq> 0" by sturm
lemma "\<forall>x::real. x*x \<noteq> -1" by sturm

subsection \<open>Interval positivity\<close>
lemma "(x::real) > 1 \<Longrightarrow> x^3 > 1" by sturm
lemma "(x::real) \<ge> 0 \<Longrightarrow> x \<le> 1 \<Longrightarrow> 4*x*(1-x) \<le> 1" by sturm

subsection \<open>Root counting\<close>
schematic_goal "card {x::real. x^2 - 1 = 0} = ?n" by sturm
schematic_goal "card {x::real. x^3 - x = 0} = ?n" by sturm
schematic_goal "card {x::real. 0 < x \<and> x < 10 \<and> x^2 - 5*x + 6 = 0} = ?n" by sturm

subsection \<open>AND/OR of root conditions\<close>
schematic_goal "card {x::real. x^3 + x = 2*x^2 \<and> x^3 - 6*x^2 + 11*x = 6} = ?n" by sturm
schematic_goal "card {x::real. x^3 + x = 2*x^2 \<or> x^3 - 6*x^2 + 11*x = 6} = ?n" by sturm

section \<open>Failure cases: sturm should fail gracefully (not hang)\<close>

subsection \<open>Non-polynomial: should fail immediately\<close>
lemma "\<forall>x::real. sin x \<le> 1"
  oops

subsection \<open>Free variable in coefficients: should fail\<close>
lemma "\<forall>x::real. x^2 + a*x + 1 > 0"
  oops

subsection \<open>Non-real type: should fail\<close>
lemma "\<forall>x::nat. x + 1 > 0"
  oops

subsection \<open>Multiple free variables: should fail\<close>
lemma "\<forall>x::real. \<forall>y::real. x^2 + y^2 \<ge> 0"
  oops

section \<open>Timing test: sturm on increasingly hard polynomials\<close>

lemma "\<forall>x::real. x^2 + 1 > 0" by sturm                   \<comment> \<open>degree 2\<close>
lemma "\<forall>x::real. x^4 + 1 > 0" by sturm                   \<comment> \<open>degree 4\<close>
lemma "\<forall>x::real. x^6 + 1 > 0" by sturm                   \<comment> \<open>degree 6\<close>
lemma "\<forall>x::real. x^8 + 1 > 0" by sturm                   \<comment> \<open>degree 8\<close>
lemma "\<forall>x::real. x^10 + 1 > 0" by sturm                  \<comment> \<open>degree 10\<close>
lemma "\<forall>x::real. x^20 + 1 > 0" by sturm                  \<comment> \<open>degree 20\<close>

section \<open>Test: what happens when sturm fails on a valid but unsolvable goal?\<close>

text \<open>These test whether sturm returns quickly or hangs when given
      goals it cannot solve (but which are syntactically close to solvable ones).\<close>

subsection \<open>Non-strict inequality (sturm only handles > and \<noteq>, not \<ge>)\<close>
lemma test_geq: "\<forall>x::real. x^2 \<ge> 0"
  apply sturm  \<comment> \<open>Expected: sturm fails (no matching prop_subst for \<ge>)\<close>
  oops

subsection \<open>Existential (sturm doesn't handle \<exists>)\<close>
lemma test_exists: "\<exists>x::real. x^2 - 2 = 0"
  apply sturm  \<comment> \<open>Expected: sturm fails\<close>
  oops

subsection \<open>Division by variable (not polynomial)\<close>
lemma test_divide: "\<forall>x::real. x > 1 \<Longrightarrow> 1/x < 1"
  apply sturm  \<comment> \<open>Expected: sturm fails (1/x not polynomial)\<close>
  oops

end
