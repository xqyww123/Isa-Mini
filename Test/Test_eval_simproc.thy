theory Test_eval_simproc
  imports MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
    "Polynomial_Factorization.Prime_Factorization"
    "Catalan_Numbers.Catalan_Numbers"
    "Bernoulli.Bernoulli"
    "Bell_Numbers_Spivey.Bell_Numbers"
begin

(*
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

(*
ML \<open>
val eval_static = Eval_Simproc.eval_ground_with (Code_Simp.static_conv {
  ctxt = \<^context>, simpset = NONE,
  consts = [\<^const_name>\<open>cong\<close>,
            \<^const_name>\<open>coprime\<close>, \<^const_name>\<open>totient\<close>,
            \<^const_name>\<open>multiplicity\<close>,
            \<^const_name>\<open>fib\<close>, \<^const_name>\<open>fact\<close>,
            \<^const_name>\<open>binomial\<close>,
            \<^const_name>\<open>gcd\<close>, \<^const_name>\<open>lcm\<close>]
})
\<close>

ML \<open>
fun time_eval name f ctxt ct =
  let val (timing, result) = Timing.timing (fn () => f ctxt ct) ()
      val elapsed = #elapsed timing
      val status = case result of NONE => "NONE" | SOME _ => "OK"
  in tracing (name ^ " " ^ Syntax.string_of_term ctxt (Thm.term_of ct) ^
              ": " ^ Value.print_time elapsed ^ "s => " ^ status)
  end

val tests = [\<^cterm>\<open>fib 10 :: nat\<close>,
             \<^cterm>\<open>fact 5 :: nat\<close>,
             \<^cterm>\<open>(10::nat) choose 3\<close>,
             \<^cterm>\<open>gcd (12::nat) 8\<close>,
             \<^cterm>\<open>lcm (12::nat) 8\<close>,
             \<^cterm>\<open>coprime (4::nat) 9\<close>,
             \<^cterm>\<open>totient 30\<close>,
             \<^cterm>\<open>multiplicity (2::nat) 24\<close>]

val _ = tracing "=== Code_Simp.static_conv ==="
val _ = app (time_eval "static " eval_static \<^context>) tests

val _ = tracing "=== Nbe.dynamic_conv ==="
val _ = app (time_eval "dynamic" Eval_Simproc.eval_ground \<^context>) tests
\<close>
*)





simproc_setup eval_gcd2 ("gcd a b") = \<open>K Eval_Simproc.eval_ground\<close>
simproc_setup eval_fib2 ("fib n") = \<open>K Eval_Simproc.eval_ground\<close>
simproc_setup eval_coprime2 ("coprime a b") = \<open>K Eval_Simproc.eval_ground\<close>
simproc_setup eval_multiplicity2 ("multiplicity p n") = \<open>K Eval_Simproc.eval_ground\<close>
simproc_setup eval_totient2 ("totient n") = \<open>K Eval_Simproc.eval_ground\<close>
*)
(*
ML \<open>
fun bench_simp name ct =
  let val _ = Eval_Simproc.reset_stats ()
      val (t, thm) = Timing.timing (fn () => Simplifier.rewrite \<^context> ct) ()
  in tracing (name ^ " total=" ^ Value.print_time (#elapsed t) ^ "s" ^
              "  result: " ^ Thm.string_of_thm \<^context> thm);
     Eval_Simproc.print_stats ()
  end

val _ = bench_simp "gcd 12 8   " \<^cterm>\<open>gcd (12::nat) 8\<close>
val _ = bench_simp "gcd 12 10  " \<^cterm>\<open>gcd (12::nat) 10\<close>
val _ = bench_simp "gcd 100 75 " \<^cterm>\<open>gcd (100::nat) 75\<close>
val _ = bench_simp "fib 10     " \<^cterm>\<open>fib 10 :: nat\<close>
val _ = bench_simp "coprime 4 9" \<^cterm>\<open>coprime (4::nat) 9\<close>
val _ = bench_simp "mult 2 24  " \<^cterm>\<open>multiplicity (2::nat) 24\<close>
val _ = bench_simp "totient 30 " \<^cterm>\<open>totient 30\<close>
\<close>
*)
section \<open>Test lemmas\<close>

lemma strip_Trueprop_eq: \<open>(Trueprop P \<equiv> Trueprop Q) \<Longrightarrow> P \<equiv> Q\<close>
unfolding atomize_eq
proof rule
  assume A: \<open>Trueprop P \<equiv> Trueprop Q\<close>
     and B: P
  from B[unfolded A]
  show "Q" .
next
  assume A: \<open>Trueprop P \<equiv> Trueprop Q\<close>
     and B: Q
  show "P"
    unfolding A
    using B .
qed
  











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

lemma \<open>det ((\<chi> i j. if i = j then 2 else 1) :: real^2^2) = 3\<close> by simp

section \<open>prime\_factorization test\<close>

lemma \<open>prime_factorization (12::nat) = {#2, 2, 3#}\<close>
  by simp

lemma \<open>squarefree (30::nat)\<close>
  by simp

lemma \<open>\<not> squarefree (12::nat)\<close>
  by simp

simproc_setup eval_residue_primroot ("residue_primroot n a") =
  \<open>K Eval_Simproc.eval_ground\<close>

lemma \<open>residue_primroot 5 2\<close>
  by simp

lemma \<open>\<not> residue_primroot 7 2\<close>
  by simp

section \<open>Combinatorics\<close>

simproc_setup eval_catalan ("catalan n") =
  \<open>K Eval_Simproc.eval_ground\<close>

lemma \<open>catalan 5 = 42\<close>
  by eval

lemma \<open>catalan 5 = 42\<close>
  by simp


simproc_setup eval_bernoulli ("bernoulli n") =
  \<open>K Eval_Simproc.eval_ground\<close>

lemma \<open>bernoulli 0 = 1\<close>
  by simp

lemma \<open>bernoulli 4 = -1/30\<close>
  by eval

lemma \<open>bernoulli 4 = -1/30\<close>
  by simp

simproc_setup eval_Bell ("Bell n") =
  \<open>K Eval_Simproc.eval_ground\<close>

lemma \<open>Bell 5 = 52\<close>
  by eval

lemma \<open>Bell 5 = 52\<close>
  by simp

simproc_setup eval_Stirling ("Stirling n k") =
  \<open>K Eval_Simproc.eval_ground\<close>

lemma \<open>Stirling 5 3 = 25\<close>
  by simp

end