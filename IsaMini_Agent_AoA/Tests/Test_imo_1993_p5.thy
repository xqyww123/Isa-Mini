(*
  Authors: Wenda Li
*)

theory Test_imo_1993_p5
  imports
    "MathBench_Prover.MathBench_Prover"
    Minilang_Agent.Minilang_Agent
begin

declare [[auto_interpret_for_embedding=false]]
theorem imo_1993_p5:
  "\<exists> f :: nat \<Rightarrow> nat. 
    (\<forall> a b. (a < b) \<longleftrightarrow> f a < f b) 
      \<and> f 1 = 2 \<and> (\<forall> n. f (f n) = f n + n)"
  by  aoa


(*
term "prime (5::int)"
value "prime (5::int)"
lemma "prime (5::nat)"
  by auto
declare sqrt_prime_irrational[simp]
*)

theorem sqrt_prime_irrational:
  fixes p :: int
  assumes x: "prime p"
  shows "sqrt p \<notin> \<rat>"
proof
  from \<open>prime p\<close> have p: "p > 1"
    using prime_gt_1_int by blast
  assume "sqrt p \<in> \<rat>"
  then obtain m n :: nat
    where n: "n \<noteq> 0"
      and sqrt_rat: "\<bar>sqrt p\<bar> = m / n"
      and "coprime m n" by (rule Rats_abs_nat_div_natE)
  have eq: "m\<^sup>2 = p * n\<^sup>2"
  proof -
    from n and sqrt_rat have "m = \<bar>sqrt p\<bar> * n" by simp
    then have "m\<^sup>2 = (sqrt p)\<^sup>2 * n\<^sup>2" by (simp add: power_mult_distrib)
    also have "(sqrt p)\<^sup>2 = p"
      by (simp add: assms prime_ge_0_int)
    also have "\<dots> * n\<^sup>2 = p * n\<^sup>2" by simp
    finally show ?thesis by linarith
  qed
  have "p dvd m \<and> p dvd n"
  proof
    from eq have "p dvd m\<^sup>2" ..
    with \<open>prime p\<close> show "p dvd m"
      by (simp add: prime_dvd_power_int_iff)
    then obtain k where "m = p * k" ..
    with eq have "p * n\<^sup>2 = p\<^sup>2 * k\<^sup>2"
      by (simp add: power_mult_distrib)
    with p have "n\<^sup>2 = p * k\<^sup>2" by (simp add: power2_eq_square)
    then have "p dvd n\<^sup>2" ..
    with \<open>prime p\<close> show "p dvd n"
      by (metis coprime_dvd_mult_left_iff int_ops(7) power2_eq_square prime_imp_coprime)
  qed
  then have "p dvd gcd m n"
    using \<open>coprime m n\<close> coprime_common_divisor coprime_int_iff by blast
  with \<open>coprime m n\<close> have "p = 1"
    using p by force
  with p show False by simp
qed

simproc_setup sqrt_prime_rat (\<open>sqrt (numeral n) \<in> \<rat>\<close>) =
  \<open>K (fn ctxt => fn ct =>
    let
      val ((_ $ (_ $ (_ $ bits))) $ _) = Thm.term_of ct
    in
      @{lemma \<open>prime (numeral n :: int) \<Longrightarrow> (sqrt (numeral n :: real) \<in> \<rat>) = False\<close> for n
           by (metis sqrt_prime_irrational[of "numeral n"] of_int_eq_numeral_iff)}
      |> Thm.instantiate' [] [SOME (Thm.cterm_of ctxt bits)]
      |> (fn thm => thm RS @{thm eq_reflection})
      |> SOME
    end
    handle Match => NONE | THM _ => NONE)\<close>
 
lemma "sqrt 23 \<notin> \<rat>"
  by simp

end