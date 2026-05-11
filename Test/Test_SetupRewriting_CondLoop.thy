theory Test_SetupRewriting_CondLoop
  imports Main
begin

text \<open>Test whether a conditional simp rule with recursive RHS fires at all.
  The rule @{text "3 \<le> x \<Longrightarrow> f x = x\<^sup>2 - f(x-1)"} should terminate at f(2).\<close>

text \<open>Test 1: Small case (3 steps). Does the conditional simp rule work?\<close>
lemma small_case:
  fixes f :: "int \<Rightarrow> int"
  assumes h0: "\<forall>(x :: int). f x + f (x - 1) = x ^ 2"
    and h1: "f (2::int) = (5::int)"
  shows "f (5::int) = (13::int)"
proof -
  \<comment> \<open>Derive the conditional rewriting rule from h0\<close>
  from h0 have rule: "\<And>x::int. (3::int) \<le> x \<Longrightarrow> f x = x ^ 2 - f (x - 1)"
    by (simp add: algebra_simps)
  \<comment> \<open>Now try applying it as a simp rule\<close>
  show ?thesis
    by (simp add: rule h1)
qed

text \<open>Test 2: Medium case (10 steps). Does it still work?\<close>
lemma medium_case:
  fixes f :: "int \<Rightarrow> int"
  assumes h0: "\<forall>(x :: int). f x + f (x - 1) = x ^ 2"
    and h1: "f (2::int) = (5::int)"
  shows "f (12::int) = (80::int)"
proof -
  from h0 have rule: "\<And>x::int. (3::int) \<le> x \<Longrightarrow> f x = x ^ 2 - f (x - 1)"
    by (simp add: algebra_simps)
  show ?thesis
    by (simp add: rule h1)
qed

text \<open>Test 3: Large case (75 steps). Does it time out or work?\<close>
lemma large_case:
  fixes f :: "int \<Rightarrow> int"
  assumes h0: "\<forall>(x :: int). f x + f (x - 1) = x ^ 2"
    and h1: "f (19::int) = (94::int)"
  shows "f (94::int) mod (1000::int) = (561::int)"
proof -
  from h0 have rule: "\<And>x::int. (20::int) \<le> x \<Longrightarrow> f x = x ^ 2 - f (x - 1)"
    by (simp add: algebra_simps)
  show ?thesis
    by (simp add: rule h1)
qed

end
