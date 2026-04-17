theory Test_eval_simproc
  imports MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent "HOL-Library.Code_Target_Nat"
         "Gauss_Jordan.Determinants2"
begin
declare [[z3_extensions, auto_interpret_for_embedding=false, AoA_interactive_retrieval="no"]]
lemma multiplicity_code [code]:
  "multiplicity p x =
     (if p = 0 \<or> is_unit p \<or> x = 0 then 0
      else if p dvd x then 1 + multiplicity p (x div p) else 0)"
proof (cases "p = 0 \<or> is_unit p \<or> x = 0")
  case True
  then show ?thesis by (auto simp: multiplicity_unit_left)
next
  case False
  then have h: "p \<noteq> 0" "\<not> is_unit p" "x \<noteq> 0" by auto
  show ?thesis
  proof (cases "p dvd x")
    case False
    with h show ?thesis by (simp add: not_dvd_imp_multiplicity_0)
  next
    case True
    with h have eq: "p * (x div p) = x" by simp
    with h have "x div p \<noteq> 0" by auto
    with h have "multiplicity p (p * (x div p)) = Suc (multiplicity p (x div p))"
      by (intro multiplicity_times_same)
    with eq True h show ?thesis by simp
  qed
qed

ML_file \<open>/home/qiyuan/Current/MLML/tasks/MathBench_Prover/eval_simproc.ML\<close>

simproc_setup eval_ord ("ord m n") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_cong ("[a = b] (mod c)") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_coprime ("coprime a b") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_totient ("totient n") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_multiplicity ("multiplicity p n") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_sum ("sum f S") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_prod ("prod f S") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_fib ("fib n") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_fact ("fact n") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_choose ("n choose k") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_gcd ("gcd a b") =
  \<open>K Eval_Simproc.eval_ground\<close>

simproc_setup eval_lcm ("lcm a b") =
  \<open>K Eval_Simproc.eval_ground\<close>

section \<open>Test: do these need simprocs or does simp already handle them?\<close>

lemma \<open>poly [:1, -3, 2::int:] 5 = 36\<close> by simp
lemma \<open>degree [:1, -3, 2::int:] = 2\<close> by simp
lemma \<open>card {2, 3, 5, 7::nat} = 4\<close> by simp
lemma \<open>(\<Sum>i<5. i) = (10::nat)\<close> by simp
lemma \<open>(\<Prod>i=1..4. i) = (24::nat)\<close> by simp
lemma \<open>fib 10 = (55::nat)\<close> by simp
lemma \<open>fact 5 = (120::nat)\<close> by simp
lemma \<open>(10::nat) choose 3 = 120\<close> by simp
lemma \<open>gcd (12::nat) 8 = 4\<close> by simp
lemma \<open>lcm (12::nat) 8 = 24\<close> by simp
lemma \<open>\<lfloor>3.7::real\<rfloor> = 3\<close> by simp
lemma \<open>\<lceil>3.2::real\<rceil> = 4\<close> by simp
lemma \<open>det ((\<chi> i j. if i = j then 2 else 1) :: int^2^2) = 3\<close> by eval
(* det: not executable — no code equations for vec_lambda, vec_nth, Eps *)

end