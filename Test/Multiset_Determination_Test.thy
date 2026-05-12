theory Multiset_Determination_Test
  imports Main "HOL-Computational_Algebra.Primes" "HOL-Library.Multiset"
begin

section \<open>Stuck proof goals from AoA agent session e1ae52d29\_5\<close>

text \<open>
  The agent was proving a miniF2F problem: given a degree-6 monic polynomial
  @{text "f(z) = z^6 - 10z^5 + az^4 + bz^3 + cz^2 + dz + 16"}
  whose roots are all positive real integers, show @{text "b = -88"}.

  The agent completed ~99\% of the proof but got stuck on the combinatorial
  step: determining that the multiset of roots must be @{text "{1,1,2,2,2,2}"}.

  Below are the stuck sub-goals extracted from the proof log, arranged from
  the outermost (hardest) to the innermost (simplest).
\<close>

subsection \<open>Goal 1 (nat\_fact): The core combinatorial fact\<close>

text \<open>
  6 positive naturals with sum 10 and product 16 must be @{text "{1,1,2,2,2,2}"}.
  This is the main stuck goal. The agent decomposed it into sub-goals below,
  but none of the sub-goals could be closed by Obvious either.
\<close>

lemma nat_fact:
  fixes N :: "nat multiset"
  assumes nsz: "size N = 6"
      and npos: "\<forall>x. x \<in># N \<longrightarrow> x \<ge> 1"
      and npr: "\<Prod>\<^sub># N = 16"
      and nsm: "\<Sum>\<^sub># N = 10"
    shows "N = {#Suc 0, Suc 0, 2, 2, 2, 2#}"
  sorry


subsection \<open>Goal 1a (elem\_dvd): Each element divides 16\<close>

text \<open>This sub-goal was actually solved by the agent (dvd\_prod\_mset + npr).\<close>

lemma elem_dvd:
  fixes N :: "nat multiset"
  assumes npr: "\<Prod>\<^sub># N = 16"
    shows "\<forall>x. x \<in># N \<longrightarrow> x dvd 16"
  sorry


subsection \<open>Goal 1b (elem\_le): Each element is at most 5\<close>

text \<open>
  From sum = 10 with 6 terms each @{text "\<ge> 1"}, each term is at most 5.
  The agent proved sub-steps (sum\_split, rest\_size, rest\_pos) but got stuck
  on the final inequality @{text "5 \<le> \<Sum>\<^sub># (N - {#x#})"}.
\<close>

lemma elem_le:
  fixes N :: "nat multiset"
  assumes nsz: "size N = 6"
      and npos: "\<forall>x. x \<in># N \<longrightarrow> x \<ge> 1"
      and nsm: "\<Sum>\<^sub># N = 10"
    shows "\<forall>x. x \<in># N \<longrightarrow> x \<le> 5"
  sorry


subsection \<open>Goal 1b-inner: sum of remaining multiset is at least 5\<close>

text \<open>
  Given @{text "x \<in># N"}, @{text "size (N - {#x#}) = 5"},
  and all elements @{text "\<ge> 1"}, show @{text "5 \<le> \<Sum>\<^sub># (N - {#x#})"}.
  The agent tried multiset induction (lost positivity premise),
  sum\_mset\_mono + size\_eq\_sum\_mset (syntax errors), and Chaining (node ID conflicts).
\<close>

lemma sum_mset_ge_size:
  fixes M :: "nat multiset"
  assumes "\<forall>x. x \<in># M \<longrightarrow> x \<ge> (1::nat)"
  shows "size M \<le> \<Sum>\<^sub># M"
  sorry


subsection \<open>Goal 1c (elem\_124): Elements are 1, 2, or 4\<close>

text \<open>
  From: each element divides 16, each @{text "\<le> 5"}, each @{text "\<ge> 1"}.
  The agent's Obvious failed on the residual:
  @{text "x dvd 16 \<Longrightarrow> x \<le> 5 \<Longrightarrow> 1 \<le> x \<Longrightarrow> x \<noteq> 1 \<Longrightarrow> x \<noteq> 4 \<Longrightarrow> x = 2"}
  (i.e., divisors of 16 in [1..5] are exactly {1, 2, 4}).
\<close>

lemma elem_124:
  fixes x :: nat
  assumes "x dvd 16" "x \<le> 5" "x \<ge> 1"
  shows "x = 1 \<or> x = 2 \<or> x = 4"
  sorry


subsection \<open>Goal 1d (elem\_12): Elements are 1 or 2 (ruling out 4)\<close>

text \<open>
  If any element were 4, the remaining 5 elements would need sum = 6 and
  product = 4 with values in @{text "{1,2}"}, giving product = 2 @{text "\<noteq>"} 4.
  Obvious failed with residual @{text "x = Suc 0"}.
\<close>

lemma elem_12:
  fixes N :: "nat multiset"
  assumes nsz: "size N = 6"
      and npos: "\<forall>x. x \<in># N \<longrightarrow> x \<ge> 1"
      and npr: "\<Prod>\<^sub># N = 16"
      and nsm: "\<Sum>\<^sub># N = 10"
      and elem_124: "\<forall>x. x \<in># N \<longrightarrow> x = 1 \<or> x = 2 \<or> x = 4"
    shows "\<forall>x. x \<in># N \<longrightarrow> x = 1 \<or> x = 2"
  sorry


subsection \<open>Goal 1e (final assembly): From elem\_12 + sum + size to exact multiset\<close>

text \<open>
  Given all elements are 1 or 2, size = 6, sum = 10:
  let k = count of 2s. Then @{text "(6-k) + 2k = 10"} gives k = 4.
  Product check: @{text "2^4 = 16"}. So @{text "N = {#1,1,2,2,2,2#}"}.
\<close>

lemma final_assembly:
  fixes N :: "nat multiset"
  assumes nsz: "size N = 6"
      and nsm: "\<Sum>\<^sub># N = 10"
      and elem_12: "\<forall>x. x \<in># N \<longrightarrow> x = 1 \<or> x = 2"
    shows "N = {#Suc 0, Suc 0, 2, 2, 2, 2#}"
  sorry


subsection \<open>Goal 2 (multiset\_det): Lift from nat to complex\<close>

text \<open>
  The agent also could not bridge the gap from the nat fact to the complex
  multiset version. The complex premises state that each root has
  @{text "Im = 0"}, @{text "Re > 0"}, @{text "\<lfloor>Re\<rfloor> = Re"} (i.e., positive real integer).
\<close>

lemma multiset_det:
  fixes M :: "complex multiset"
  assumes sz: "size M = 6"
      and pos: "\<forall>x. x \<in># M \<longrightarrow> Im x = 0 \<and> 0 < Re x \<and> real_of_int \<lfloor>Re x\<rfloor> = Re x"
      and pr: "\<Prod>\<^sub># M = 16"
      and sm: "\<Sum>\<^sub># M = 10"
    shows "M = {#1, 1, 2, 2, 2, 2#}"
  sorry

end
