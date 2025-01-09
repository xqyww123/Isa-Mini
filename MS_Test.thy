theory MS_Test
  imports Main Proof_Shell HOL.Transcendental HOL.Groups_Big
begin

  
lemma \<open>0 < length x \<Longrightarrow> x \<noteq> []\<close>
  by (min_script \<open>CASE_SPLIT x PRINT END\<close>)

lemma \<open>rev (rev l) = l\<close>
  by (min_script \<open>END\<close>)

lemma \<open>rev (rev l) = l\<close>
  by (min_script \<open>INDUCT l PRINT END\<close>)

        
lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>END\<close>)
 
lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>INTRO HAVE "A" PRINT END END\<close>)

lemma  
  \<open> \<And>a y. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>INTRO CRUSH PRINT HAVE "A" END PRINT HAMMER PRINT END\<close>)

lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> B\<close>
  by (min_script \<open>PRINT INTRO END\<close>)

lemma   
  \<open> A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P y \<and> B\<close>
  by (min_script \<open>
  CONSIDER x :: int and z :: nat where "0 < x" and c: "2 < z" and "1 < x" PRINT end PRINT end\<close>)






lemma  
  \<open> \<And>y. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P y \<and> B\<close>
  by (min_script \<open> 
  INTRO
  CONSIDER x :: int and z :: nat where "0 < x" and c: "2 < z" and "1 < x" PRINT end PRINT end\<close>)

lemma
  \<open> \<And>y. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P y \<and> B\<close>
  by (min_script \<open>
    INTRO
    RULE
    HAMMER
    RULE assm0(1)[THEN conjunct2]
    END
 \<close>)

lemma \<comment> \<open>Meta and Object-level \<open>\<forall>, \<and>\<close> are unified.
          The two following proofs have the same pretty print.\<close>
  \<open> \<And>y. A \<and> B \<Longrightarrow> (\<forall>x. P x) \<Longrightarrow> P y \<and> B\<close>
  by (min_script \<open>
  PRINT INTRO PRINT END
\<close>)

lemma
  \<open> \<forall>y. A \<and> B \<longrightarrow> (\<forall>x. P x) \<longrightarrow> P y \<and> B\<close>
  by (min_script \<open>
  PRINT INTRO PRINT END
\<close>)
 

theorem sqrt2_not_rational:
  "sqrt 2 \<notin> \<rat>"
by (min_script \<open>
  CRUSH
  CONSIDER m n :: nat where "\<bar>sqrt 2\<bar> = m / n" and "coprime m n" END
  HAVE "m^2 = (sqrt 2)^2 * n^2" END
  HAVE "m^2 = 2 * n^2" END
  HAVE "2 dvd m^2" END
  HAVE "2 dvd m" END
  HAVE "2 dvd n"
    CONSIDER k where "m = 2 * k" END
    HAVE "2 * n^2 = 2^2 * k^2" END
    HAVE "2 dvd n^2" END
    HAVE "2 dvd n" END
  END
  HAVE "2 dvd gcd m n" END
  HAVE "2 dvd 1" END
  END
\<close>)

lemma binomial_maximum: "n choose k \<le> n choose (n div 2)"
proof -
  have "k \<le> n div 2 \<longleftrightarrow> 2*k \<le> n" by linarith
  consider "2*k \<le> n" | "2*k \<ge> n" "k \<le> n" | "k > n" by linarith
  thus ?thesis
  proof cases
    case 1
    thus ?thesis by (intro binomial_mono) linarith+
  next
    case 2
    thus ?thesis by (intro binomial_antimono) simp_all
  qed (simp_all add: binomial_eq_0)
qed


lemma binomial_maximum': "n choose k \<le> n choose (n div 2)"
  by (min_script \<open>
  HAVE "k \<le> n div 2 \<longleftrightarrow> 2*k \<le> n" END
  CONSIDER "2*k \<le> n" | "2*k \<ge> n" "k \<le> n" | "k > n" PRINT NEXT PRINT NEXT PRINT NEXT PRINT END
\<close>)

lemma "n choose k \<le> n choose (n div 2)"
  by (min_script \<open>
  HAVE "k \<le> n div 2 \<longleftrightarrow> 2*k \<le> n" END
  CONSIDER "2*k \<le> n" | "2*k \<ge> n" "k \<le> n" | "k > n" END
\<close>)

proposition lexn_transI:
  assumes "trans r" shows "trans (lexn r n)"
unfolding trans_def
proof (intro allI impI)
  fix as bs cs
  assume asbs: "(as, bs) \<in> lexn r n" and bscs: "(bs, cs) \<in> lexn r n"
  obtain abs a b as' bs' where
    n: "length as = n" and "length bs = n" and
    as: "as = abs @ a # as'" and
    bs: "bs = abs @ b # bs'" and
    abr: "(a, b) \<in> r"
    using asbs unfolding lexn_conv by blast
  obtain bcs b' c' cs' bs' where
    n': "length cs = n" and "length bs = n" and
    bs': "bs = bcs @ b' # bs'" and
    cs: "cs = bcs @ c' # cs'" and
    b'c'r: "(b', c') \<in> r"
    using bscs unfolding lexn_conv by blast
  consider (le) "length bcs < length abs"
    | (eq) "length bcs = length abs"
    | (ge) "length bcs > length abs" by linarith
  thus "(as, cs) \<in> lexn r n"
  proof cases
    let ?k = "length bcs"
    case le
    hence "as ! ?k = bs ! ?k" unfolding as bs by (simp add: nth_append)
    hence "(as ! ?k, cs ! ?k) \<in> r" using b'c'r unfolding bs' cs by auto
    moreover
    have "length bcs < length as" using le unfolding as by simp
    from id_take_nth_drop[OF this]
    have "as = take ?k as @ as ! ?k # drop (Suc ?k) as" .
    moreover
    have "length bcs < length cs" unfolding cs by simp
    from id_take_nth_drop[OF this]
    have "cs = take ?k cs @ cs ! ?k # drop (Suc ?k) cs" .
    moreover have "take ?k as = take ?k cs"
      using le arg_cong[OF bs, of "take (length bcs)"]
      unfolding cs as bs' by auto
    ultimately show ?thesis using n n' unfolding lexn_conv by auto
  next
    let ?k = "length abs"
    case ge
    hence "bs ! ?k = cs ! ?k" unfolding bs' cs by (simp add: nth_append)
    hence "(as ! ?k, cs ! ?k) \<in> r" using abr unfolding as bs by auto
    moreover
    have "length abs < length as" using ge unfolding as by simp
    from id_take_nth_drop[OF this]
    have "as = take ?k as @ as ! ?k # drop (Suc ?k) as" .
    moreover have "length abs < length cs" using n n' unfolding as by simp
    from id_take_nth_drop[OF this]
    have "cs = take ?k cs @ cs ! ?k # drop (Suc ?k) cs" .
    moreover have "take ?k as = take ?k cs"
      using ge arg_cong[OF bs', of "take (length abs)"]
      unfolding cs as bs by auto
    ultimately show ?thesis using n n' unfolding lexn_conv by auto
  next
    let ?k = "length abs"
    case eq
    hence *: "abs = bcs" "b = b'" using bs bs' by auto
    hence "(a, c') \<in> r"
      using abr b'c'r assms unfolding trans_def by blast
    with * show ?thesis using n n' unfolding lexn_conv as bs cs by auto
  qed
qed
 
lemma lexn_transI':
  assumes "trans r" shows "trans (lexn r n)"
  by (min_script \<open>
  UNFOLD trans_def
  CRUSH VARS as bs cs
  CONSIDER abs a b as' bs' where
    "length as = n" and "length bs = n" and
    "as = abs @ a # as'" and
    "bs = abs @ b # bs'" and
    "(a, b) \<in> r" END
  CONSIDER bcs b' c' cs' bs' where
    "length cs = n" and "length bs = n" and
    "bs = bcs @ b' # bs'" and
    "cs = bcs @ c' # cs'" and
    "(b', c') \<in> r" END
PRINT
  CONSIDER "length bcs < length abs"
         | "length bcs = length abs"
         | "length bcs > length abs"
  NEXT
    LET ?k = "length bcs"
    HAVE "as ! ?k = bs ! ?k" END
    HAVE "(as ! ?k, cs ! ?k) \<in> r" END
    HAVE "length bcs < length as" END
    HAVE "as = take ?k as @ as ! ?k # drop (Suc ?k) as" END
    HAVE "length bcs < length cs" END
    HAVE "cs = take ?k cs @ cs ! ?k # drop (Suc ?k) cs" END
    HAVE "take ?k as = take ?k cs" END
  NEXT
    LET ?k = "length abs"
    HAVE "abs = bcs" "b = b'" END
    HAVE "(a, c') \<in> r" END
  NEXT
    LET ?k = "length abs"
    HAVE "bs ! ?k = cs ! ?k" END
    HAVE "(as ! ?k, cs ! ?k) \<in> r" END
    HAVE "length abs < length as" END
    HAVE "as = take ?k as @ as ! ?k # drop (Suc ?k) as" END
    HAVE "length abs < length cs" END
    HAVE "cs = take ?k cs @ cs ! ?k # drop (Suc ?k) cs" END
    HAVE "take ?k as = take ?k cs" END
    PRINT
  END
\<close>)


definition \<open>TAG X = X\<close>

lemma test_unfold_prem:
  \<open>TAG P \<Longrightarrow> P\<close>
  by (min_script \<open>INTRO UNFOLD TAG_def IN assm0 PRINT END\<close>)


           
lemma comm_append_are_replicate':
  "xs @ ys = ys @ xs \<Longrightarrow> \<exists>m n zs. concat (replicate m zs) = xs \<and> concat (replicate n zs) = ys"
   
by (min_script \<open>
  INDUCT "length (xs @ ys) + length xs" arbitrary: xs ys rule: less_induct
PRINT
  CONSIDER "length ys < length xs" | "xs = []" | "length xs \<le> length ys \<and> xs \<noteq> []"
  NEXT
  NEXT
    HAVE "concat (replicate 0 ys) = xs \<and> concat (replicate 1 ys) = ys" END
  NEXT
    HAVE "length xs \<le> length ys" and "xs \<noteq> []" END
    CONSIDER ws where "ys = xs @ ws" END
    HAVE "length ws < length ys" END
    HAVE "xs @ ws = ws @ xs" END
    CONSIDER m n' zs where "concat (replicate m zs) = xs" and  "concat (replicate n' zs) = ws" END
    HAVE "concat (replicate (m+n') zs) = ys" END
  END
\<close>)


lemma comm_append_are_replicate:
  "xs @ ys = ys @ xs \<Longrightarrow> \<exists>m n zs. concat (replicate m zs) = xs \<and> concat (replicate n zs) = ys"
proof (induction "length (xs @ ys) + length xs" arbitrary: xs ys rule: less_induct)
  case less
  consider (1) "length ys < length xs" | (2) "xs = []" | (3) "length xs \<le> length ys \<and> xs \<noteq> []"
    by linarith
  then show ?case
  proof (cases)
    case 1
    then show ?thesis
      using less.hyps[OF _ less.prems[symmetric]] nat_add_left_cancel_less by auto
  next
    case 2
    then have "concat (replicate 0 ys) = xs \<and> concat (replicate 1 ys) = ys"
      by simp
    then show ?thesis
      by blast
  next
    case 3
    then have "length xs \<le> length ys" and "xs \<noteq> []"
      by blast+
    from \<open>length xs \<le> length ys\<close> and  \<open>xs @ ys = ys @ xs\<close>
    obtain ws where "ys = xs @ ws"
      by (auto simp: append_eq_append_conv2)
    from this and \<open>xs \<noteq> []\<close>
    have "length ws < length ys"
      by simp
    from \<open>xs @ ys = ys @ xs\<close>[unfolded \<open>ys = xs @ ws\<close>]
    have "xs @ ws = ws @ xs"
      by simp
    from less.hyps[OF _ this] \<open>length ws < length ys\<close>
    obtain m n' zs where "concat (replicate m zs) = xs" and  "concat (replicate n' zs) = ws"
      by auto
    then have "concat (replicate (m+n') zs) = ys"
      using \<open>ys = xs @ ws\<close>
      by (simp add: replicate_add)
    then show ?thesis
      using \<open>concat (replicate m zs) = xs\<close> by blast
  qed
qed


   
lemma polyfun_extremal_lemma': 
    fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "0 < e"
    shows "\<exists>M. \<forall>z. M \<le> norm(z) \<longrightarrow> norm (\<Sum>i\<le>n. c(i) * z^i) \<le> e * norm(z) ^ (Suc n)"
  by (min_script \<open>
INDUCT n
PRINT
NEXT
CONSIDER M where "\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n" END
RULE exI [where x= "max M (1 + norm(c(Suc n)) / e)"]
CRUSH
PRINT
HAVE "e + norm (c (Suc n)) \<le> e * norm z" END
HAVE "norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n" END
HAVE "norm (\<Sum>i\<le>n. c i * z^i) + norm (c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)" END
HAVE "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)" END
HAVE "e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n) \<le> (e + norm (c (Suc n))) * norm z ^ Suc n"  END
HAVE "(e + norm (c (Suc n))) * norm z ^ Suc n \<le> e * norm z * norm z ^ Suc n" END
END
\<close>)

lemma polyfun_extremal_lemma: 
    fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "0 < e"
    shows "\<exists>M. \<forall>z. M \<le> norm(z) \<longrightarrow> norm (\<Sum>i\<le>n. c(i) * z^i) \<le> e * norm(z) ^ (Suc n)"
proof (induct n)

  case 0 with assms
  show ?case
    apply (rule_tac x="norm (c 0) / e" in exI)
    apply (auto simp: field_simps)
    done
next
  case (Suc n)
  obtain M where M: "\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n"
    using Suc assms by blast
  show ?case
  proof (rule exI [where x= "max M (1 + norm(c(Suc n)) / e)"], clarsimp simp del: power_Suc)
    fix z::'a
    assume z1: "M \<le> norm z" and "1 + norm (c (Suc n)) / e \<le> norm z"
    then have z2: "e + norm (c (Suc n)) \<le> e * norm z"
      using assms by (simp add: field_simps)
    have "norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n"
      using M [OF z1] by simp
    then have "norm (\<Sum>i\<le>n. c i * z^i) + norm (c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)"
      by simp
    then have "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)"
      by (blast intro: norm_triangle_le elim: )
    also have "... \<le> (e + norm (c (Suc n))) * norm z ^ Suc n"
      by (simp add: norm_power norm_mult algebra_simps)
    also have "... \<le> (e * norm z) * norm z ^ Suc n"
      by (metis z2 mult.commute mult_left_mono norm_ge_zero norm_power)
    finally show "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc (Suc n)"
      by simp
  qed
qed

no_notation
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [51, 51] 50)

notation
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [50, 51] 50) and
  less  ("'(<')") and
  less  ("(_/ < _)"  [50, 51] 50)


term \<open>a \<le> b\<close>

translations
  "a \<le> b \<le> c" => "a \<le> b \<and> b \<le> c"
  "a < b < c" => "a < b \<and> b < c"
  "a = b = c" => "a = b \<and> b = c"
  "a \<longleftrightarrow> b \<longleftrightarrow> c" => "(a \<longleftrightarrow> b) \<and> (b \<longleftrightarrow> c)"

term \<open>a \<le> b \<le> c\<close>
term \<open>a < b < c\<close>
term \<open>a = b = c\<close>
term \<open>a = b \<longleftrightarrow> c = d\<close>
term \<open>a \<longleftrightarrow> b \<longleftrightarrow> c \<longleftrightarrow> d\<close>

lemma polyfun_extremal_lemma'': 
    fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "0 < e"
    shows "\<exists>M. \<forall>z. M \<le> norm(z) \<longrightarrow> norm (\<Sum>i\<le>n. c(i) * z^i) \<le> e * norm(z) ^ (Suc n)"
  by (min_script \<open>
INDUCT n
PRINT
NEXT
CONSIDER M where "\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n" END
CHOOSE "max M (1 + norm(c(Suc n)) / e)"
CRUSH
PRINT
HAVE "e + norm (c (Suc n)) \<le> e * norm z" END
HAVE "norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n" END
HAVE "norm (\<Sum>i\<le>n. c i * z^i) + norm (c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)" END
HAVE "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n)
    \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)
    \<le> (e + norm (c (Suc n))) * norm z ^ Suc n
    \<le> e * norm z * norm z ^ Suc n" END
END
\<close>)

(*
lemma comm_append_are_replicate':
  "xs @ ys = ys @ xs \<Longrightarrow> \<exists>m n zs. concat (replicate m zs) = xs \<and> concat (replicate n zs) = ys"
by (min_script \<open>
  INDUCT "length (xs @ ys) + length xs" arbitrary: xs ys rule: less_induct
  PRINT
  CONSIDER "length ys < length xs" | "xs = []" | "length xs \<le> length ys \<and> xs \<noteq> []"
  NEXT
  NEXT
    HAVE "concat (replicate 0 ys) = xs \<and> concat (replicate 1 ys) = ys" END
  PRINT
  NEXT
    
\<close>)
*)

lemma \<open>rev (rev l) = l\<close>
proof (cases l)
ML_val \<open>Proof_Context.dest_cases NONE \<^context> |> @{print} |> hd |> snd
    |> (fn C => Proof_Context.apply_case C \<^context> )\<close>

lemma comm_append_are_replicate:
  "xs @ ys = ys @ xs \<Longrightarrow> \<exists>m n zs. concat (replicate m zs) = xs \<and> concat (replicate n zs) = ys"
  
proof (induct "length (xs @ ys) + length xs" arbitrary: xs ys rule: less_induct)
ML_val \<open>Proof_Context.dest_cases NONE \<^context> |> @{print} |> hd |> snd
    |> (fn C => Proof_Context.apply_case C \<^context> )\<close>
term ?case

  case less
  term xs
  thm less.hyps
  thm less.prems
  
term ?case
  thm this  
ML_val \<open>Proof.the_facts (Toplevel.proof_of @{Isar.state})\<close>
thm less

  consider (1) "length ys < length xs" | (2) "xs = []" | (3) "length xs \<le> length ys \<and> xs \<noteq> []"
    by linarith
  then show ?case
thm less.hyps
thm less.prems
  

  proof (cases)
    case 1
    then show ?thesis
      using less.hyps[OF _ less.prems[symmetric]] nat_add_left_cancel_less by auto
  next
    case 2
    then have "concat (replicate 0 ys) = xs \<and> concat (replicate 1 ys) = ys"
      by simp
    then show ?thesis
      by blast
  next
    case 3
    then have "length xs \<le> length ys" and "xs \<noteq> []"
      by blast+
    from \<open>length xs \<le> length ys\<close> and  \<open>xs @ ys = ys @ xs\<close>
    obtain ws where "ys = xs @ ws"
      by (auto simp: append_eq_append_conv2)
    from this and \<open>xs \<noteq> []\<close>
    have "length ws < length ys"
      by simp
    from \<open>xs @ ys = ys @ xs\<close>[unfolded \<open>ys = xs @ ws\<close>]
    have "xs @ ws = ws @ xs"
      by simp
    from less.hyps[OF _ this] \<open>length ws < length ys\<close>
    obtain m n' zs where "concat (replicate m zs) = xs" and  "concat (replicate n' zs) = ws"
      by auto
    then have "concat (replicate (m+n') zs) = ys"
      using \<open>ys = xs @ ws\<close>
      by (simp add: replicate_add)
    then show ?thesis
      using \<open>concat (replicate m zs) = xs\<close> by blast
  qed
qed

lemma comm_append_are_replicate':
  "xs @ ys = ys @ xs \<Longrightarrow> \<exists>m n zs. concat (replicate m zs) = xs \<and> concat (replicate n zs) = ys"
  by (min_script \<open>
    
\<close>)



end
