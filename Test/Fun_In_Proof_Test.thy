theory Fun_In_Proof_Test
  imports Main Minilang.Minilang
begin

section \<open>Recursive functions (fun path)\<close>

text \<open>Basic recursion\<close>
lemma "P \<Longrightarrow> \<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc 0))) = 6"
  by (min_script \<open>
  INTRO
  FUN my_fact :: "nat \<Rightarrow> nat"
    where "my_fact 0 = 1"
        | "my_fact (Suc n) = (Suc n) * my_fact n"
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc 0))) = 6"
  CHOOSE my_fact
  END
  END
\<close>)

text \<open>Fibonacci\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f 3 = 2"
  by (min_script \<open>
  FUN fib :: "nat \<Rightarrow> nat"
    where "fib 0 = 0"
        | "fib (Suc 0) = 1"
        | "fib (Suc (Suc n)) = fib n + fib (Suc n)"
  CHOOSE fib
  END
\<close>)

text \<open>Mutual-style single function with accumulator\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 4 0 = 10"
  by (min_script \<open>
  FUN sum_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where "sum_acc 0 a = a"
        | "sum_acc (Suc n) a = sum_acc n (a + Suc n)"
  CHOOSE sum_acc
  END
\<close>)


section \<open>Non-recursive with simple args (definition path)\<close>

text \<open>Simple arithmetic\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f 3 = 6"
  by (min_script \<open>
  FUN double :: "nat \<Rightarrow> nat"
    where "double n = n + n"
  CHOOSE double
  END WITH double_def
\<close>)

section \<open>Non-recursive with patterns (fun path, not definition)\<close>


text \<open>Boolean pattern matching\<close>
lemma "\<exists>f :: bool \<Rightarrow> nat. f True = 1 \<and> f False = 0"
  by (min_script \<open>
  FUN bool_to_nat :: "bool \<Rightarrow> nat"
    where "bool_to_nat True = 1"
        | "bool_to_nat False = 0"
  CHOOSE bool_to_nat
  END
\<close>)


section \<open>List functions\<close>

text \<open>Recursive list function\<close>
lemma "\<exists>f :: nat list \<Rightarrow> nat. f [1,2,3] = 6"
  by (min_script \<open>
  FUN my_sum :: "nat list \<Rightarrow> nat"
    where "my_sum [] = 0"
        | "my_sum (x # xs) = x + my_sum xs"
  CHOOSE my_sum
  END
\<close>)

text \<open>Non-recursive list pattern (fun path due to patterns)\<close>
lemma "\<exists>f :: nat list \<Rightarrow> nat. f [] = 0 \<and> f [5] = 5"
  by (min_script \<open>
  FUN my_head :: "nat list \<Rightarrow> nat"
    where "my_head [] = 0"
        | "my_head (x # xs) = x"
  CHOOSE my_head
  END
\<close>)


section \<open>Function used in subsequent proof steps\<close>

text \<open>Define function then use its simp rules\<close>
lemma "1 + 1 = (2 :: nat)"
  by (min_script \<open>
  FUN inc :: "nat \<Rightarrow> nat"
    where "inc n = Suc n"
  HAVE "inc 1 = 2" END
  HAVE "1 + 1 = (2 :: nat)" END
  END
\<close>)


section \<open>Edge cases\<close>

text \<open>Constant function (no arguments besides the fixed one)\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f 20 = 0"
  by (min_script \<open>
  FUN always_zero :: "nat \<Rightarrow> nat"
    where "always_zero n = 0"
  CHOOSE always_zero
  END WITH always_zero_def
\<close>)

text \<open>Higher-order result\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 3 4 = 7"
  by (min_script \<open>
  FUN mk_adder :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where "mk_adder x y = x + y"
  CHOOSE mk_adder
  END WITH mk_adder_def
\<close>)


section \<open>Interleaving and nesting\<close>

text \<open>Two FUNs back-to-back in the same block where both functions are used
  (tests FUN scope reuse with two distinct witnesses in the same goal).
  dbl: n -> 2n, trip: n -> 3n.\<close>
lemma "(\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc 0))) = Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<and>
       (\<exists>g :: nat \<Rightarrow> nat. g (Suc (Suc 0)) = Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
  by (min_script \<open>
  FUN dbl :: "nat \<Rightarrow> nat"
    where "dbl 0 = 0"
        | "dbl (Suc n) = Suc (Suc (dbl n))"
  FUN trip :: "nat \<Rightarrow> nat"
    where "trip 0 = 0"
        | "trip (Suc n) = Suc (Suc (Suc (trip n)))"
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc 0))) = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
    CHOOSE dbl
    END
  HAVE "\<exists>g :: nat \<Rightarrow> nat. g (Suc (Suc 0)) = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
    CHOOSE trip
    END
  END
\<close>)

text \<open>A later FUN uses the simp rules of an earlier FUN (tests scope-reuse visibility).
  `quad` calls `dbl`, so the two functions must coexist in the same FUN scope.
  quad 2 = dbl (dbl 2) = dbl 4 = 8.\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc 0)) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
  by (min_script \<open>
  FUN dbl :: "nat \<Rightarrow> nat"
    where "dbl 0 = 0"
        | "dbl (Suc n) = Suc (Suc (dbl n))"
  FUN quad :: "nat \<Rightarrow> nat"
    where "quad n = dbl (dbl n)"
  CHOOSE quad
  END
\<close>)

text \<open>FUN nested inside a HAVE block — the inner FUN must open its own
  scope tied to the HAVE's subgoal, so the HAVE's END discharges its hyps.\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f 3 = 9"
  by (min_script \<open>
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc 0))) = 9"
    FUN trip :: "nat \<Rightarrow> nat"
      where "trip 0 = 0"
          | "trip (Suc n) = Suc (Suc (Suc (trip n)))"
    CHOOSE trip
    END
  END
\<close>)

text \<open>INTRO then FUN then HAVE-with-FUN — nested FUN scopes across an
  assumption introduction and a subgoal. Tests that a FUN inside a HAVE
  block opens its own inner FUN_SCOPE below the HAVE's MAGIC, and that
  the outer FUN's scope is NOT reused across the HAVE boundary.\<close>
lemma "P \<Longrightarrow> \<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc 0)) = Suc (Suc (Suc (Suc 0)))"
  by (min_script \<open>
  INTRO
  FUN dbl :: "nat \<Rightarrow> nat"
    where "dbl 0 = 0"
        | "dbl (Suc n) = Suc (Suc (dbl n))"
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc 0)) = Suc (Suc (Suc (Suc 0)))"
    CHOOSE dbl
    END
  END
\<close>)

text \<open>Three FUNs where each depends on the previous (chain of scope-reuse).
  oct 1 = dbl (quad 1) = dbl (dbl (dbl 1)) = dbl (dbl 2) = dbl 4 = 8.\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f (Suc 0) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
  by (min_script \<open>
  FUN dbl :: "nat \<Rightarrow> nat"
    where "dbl 0 = 0"
        | "dbl (Suc n) = Suc (Suc (dbl n))"
  BY_METRIC "\<lambda>n::nat. n"
  FUN quad :: "nat \<Rightarrow> nat"
    where "quad n = dbl (dbl n)"
  BY_METRIC "\<lambda>n::nat. n"
  FUN oct :: "nat \<Rightarrow> nat"
    where "oct n = dbl (quad n)"
  BY_METRIC "\<lambda>n::nat. n"
  CHOOSE oct
  END
\<close>)

setup \<open>
   Config.put_global Minilang.fun_fake_automatic_failure true
#> Config.put_global Minilang.strict_end true
(* #> Config.put_global Minilang.fun_fake_pat_completeness_failure true *)
\<close>

section \<open>BY_METRIC clause\<close>

text \<open>Singleton measure via @{const Wellfounded.measure}. With the
  default prover forced to fail via the internal debug config
  @{ML Minilang.fun_fake_automatic_failure}, BY_METRIC is the only
  way to close termination.\<close>

  
lemma "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc (Suc 0)))) = Suc (Suc 0)"
  by (min_script \<open>
  FUN_DEBUG halve :: "nat \<Rightarrow> nat"
    where "halve 0 = 0"
        | "halve (Suc 0) = 0"
        | "halve (Suc (Suc n)) = Suc (halve n)"
  BY_METRIC "\<lambda>n. n"
  HAMMER NEXT HAMMER PRINT
  END PRINT
  CHOOSE halve PRINT
  HAMMER PRINT
  END
\<close>)

term Cons

text \<open>Lexicographic product of two measures via @{const List.measures}.
  Ackermann is the classic example — no single-measure argument works,
  but `measures [fst, snd]` does.\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 0 0 = Suc 0"
  by (min_script \<open>
  FUN_DEBUG my_ack :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where "my_ack 0 n = Suc n"
        | "my_ack (Suc m) 0 = my_ack m (Suc 0)"
        | "my_ack (Suc m) (Suc n) = my_ack m (my_ack (Suc m) n)"
    BY_METRIC "\<lambda>(m::nat, n::nat). m" AND "\<lambda>(m::nat, n::nat). n"
    SORRY
    SORRY
    SORRY
  SORRY
    PRINT
  HAMMER
  END
\<close>)

setup \<open>Config.put_global Minilang.fun_fake_automatic_failure false\<close>


section \<open>Functions where Isabelle's default termination prover genuinely fails\<close>

text \<open>List padding to a target length — each recursive call \<^emph>\<open>grows\<close>
  \<open>xs\<close> by one element, so \<open>length xs\<close> is strictly \<^emph>\<open>increasing\<close>, and
  \<open>n\<close> stays constant. Neither \<open>length xs\<close> nor \<open>n\<close> is a valid
  termination measure on its own, nor are any of their lexicographic
  products. The measure that works is \<open>n - length xs\<close>, which
  \<open>lexicographic_order_tac\<close> cannot guess because its search space is
  limited to the theorems tagged with \<open>[measure_function]\<close> (just
  \<open>size\<close>/\<open>length\<close>/\<open>id\<close> and their lex products — not arbitrary
  arithmetic expressions on them). Without \<open>BY_METRIC\<close>, plain \<open>FUN\<close>
  fails with an error asking the user to supply a metric.\<close>

lemma "\<exists>f :: nat list \<Rightarrow> nat \<Rightarrow> nat list. f [0, 0] 4 = [0, 0, 0, 0]"
  by (min_script \<open>
  FUN_DEBUG pad :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"
    where "pad xs n = (if length xs \<ge> n then xs else pad (xs @ [0]) n)"
    BY_METRIC "\<lambda>(xs, n::nat). n - length xs"
  CHOOSE pad
  HAMMER
  END
\<close>)

text \<open>Sanity check: the same function \<^emph>\<open>without\<close> \<open>BY_METRIC\<close> should
  error out at the termination phase with a clear "please provide
  BY_METRIC" message. (Commented out — uncomment to see the error
  interactively.)\<close>

(*
lemma "\<exists>f :: nat list \<Rightarrow> nat \<Rightarrow> nat list. f [0, 0] 4 = [0, 0, 0, 0]"
  by (min_script \<open>
  FUN pad :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"
    where "pad xs n = (if length xs \<ge> n then xs else pad (xs @ [0]) n)"
  CHOOSE pad
  END
\<close>)
*)


text \<open>Merge sort — a classic case where \<open>lexicographic_order_tac\<close>
  is unable to discharge termination on its own. The recursion
  pattern is
    \<open>msort xs = merge (msort (take (length xs div 2) xs))
                      (msort (drop (length xs div 2) xs))\<close>
  so the measure \<^emph>\<open>is\<close> \<open>length\<close>, but proving
  \<open>length (take (length xs div 2) xs) < length xs\<close> and
  \<open>length (drop (length xs div 2) xs) < length xs\<close> (when
  \<open>length xs \<ge> 2\<close>) requires unfolding \<open>length_take\<close> /
  \<open>length_drop\<close> together with arithmetic about \<open>div\<close>, which the
  default prover's \<open>termination_simp\<close>-based \<open>auto\<close> can't do on its
  own. Supplying \<open>BY_METRIC "\<lambda>xs. length xs"\<close> makes the metric path
  fire, and \<open>Phi_Sledgehammer_Solver.all_auto\<close> closes the decrease
  obligations.

  \<open>merge\<close>, by contrast, terminates via ordinary lex order on
  \<open>(length xs, length ys)\<close> which the default prover handles
  without any metric hint.\<close>

lemma "\<exists>f :: nat list \<Rightarrow> nat list. f [] = []"
  by (min_script \<open>
  FUN merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list"
    where "merge [] ys = ys"
        | "merge xs [] = xs"
        | "merge (x # xs) (y # ys) =
             (if x \<le> y then x # merge xs (y # ys) else y # merge (x # xs) ys)"
  FUN msort :: "nat list \<Rightarrow> nat list"
    where "msort [] = []"
        | "msort [x] = [x]"
        | "msort xs = merge (msort (take (length xs div 2) xs))
                            (msort (drop (length xs div 2) xs))"
    BY_METRIC "\<lambda>xs::nat list. length xs"
  CHOOSE msort
  HAMMER
  END
\<close>)


section \<open>Unit tests for @{ML Minilang.check_looping_simp_rules}\<close>

text \<open>Helper: build fixes and specs from a name, optional type, and
  equation strings, then call the checker.\<close>
ML \<open>
fun test_check ctxt name ty_opt eqs =
  let
    val fixes = [(Binding.name name, ty_opt, NoSyn)]
    val specs = map (fn eq => ((Binding.empty_atts, eq), [], [])) eqs
  in Minilang.check_looping_simp_rules ctxt fixes specs end

fun should_not_loop ctxt name ty_opt eqs =
  if not (test_check ctxt name ty_opt eqs)
  then writeln ("PASS (no loop): " ^ name)
  else error ("FAIL: " ^ name ^ " was flagged as looping but should not be")

fun should_loop ctxt name ty_opt eqs =
  if test_check ctxt name ty_opt eqs
  then writeln ("PASS (looping): " ^ name)
  else error ("FAIL: " ^ name ^ " was not flagged as looping but should be")
\<close>

text \<open>Good definitions: constructor-pattern LHS, not flagged.\<close>
ML \<open>
let val ctxt = \<^context> in
  should_not_loop ctxt "my_fact" (SOME "nat \<Rightarrow> nat")
    ["my_fact 0 = 1",
     "my_fact (Suc n) = (Suc n) * my_fact n"];

  should_not_loop ctxt "fib" (SOME "nat \<Rightarrow> nat")
    ["fib 0 = 0",
     "fib (Suc 0) = 1",
     "fib (Suc (Suc n)) = fib n + fib (Suc n)"];

  should_not_loop ctxt "clamp" (SOME "nat \<Rightarrow> nat")
    ["clamp n = (if n > 10 then 10 else n)"];

  should_not_loop ctxt "mrg" (SOME "nat list \<Rightarrow> nat list \<Rightarrow> nat list")
    ["mrg [] ys = ys",
     "mrg xs [] = xs",
     "mrg (x # xs) (y # ys) = (if x \<le> y then x # mrg xs (y # ys) else y # mrg (x # xs) ys)"];

  should_not_loop ctxt "ack" (SOME "nat \<Rightarrow> nat \<Rightarrow> nat")
    ["ack 0 n = Suc n",
     "ack (Suc m) 0 = ack m (Suc 0)",
     "ack (Suc m) (Suc n) = ack m (ack (Suc m) n)"];

  should_not_loop ctxt "rev_acc" (SOME "nat list \<Rightarrow> nat list \<Rightarrow> nat list")
    ["rev_acc [] acc = acc",
     "rev_acc (x # xs) acc = rev_acc xs (x # acc)"];

  should_not_loop ctxt "double" (SOME "nat \<Rightarrow> nat")
    ["double n = n + n"]
end
\<close>

text \<open>Looping definitions: catch-all LHS with recursive calls in RHS.
  These are allowed but their simps will be removed from the simpset.\<close>
ML \<open>
let val ctxt = \<^context> in
  should_loop ctxt "bad_f" (SOME "nat \<Rightarrow> nat")
    ["bad_f n = (if n = 0 then 0 else bad_f (n - 1))"];

  should_loop ctxt "zs" (SOME "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat")
    ["zs a b n = (if n = 0 then 0 else if n < b then b + zs 1 2 (n - a) else zs b (a + b) n)"];

  should_loop ctxt "bad_pad" (SOME "nat list \<Rightarrow> nat \<Rightarrow> nat list")
    ["bad_pad xs n = (if length xs \<ge> n then xs else bad_pad (xs @ [0]) n)"]
end
\<close>

end
