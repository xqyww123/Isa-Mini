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
  FUN quad :: "nat \<Rightarrow> nat"
    where "quad n = dbl (dbl n)"
  FUN oct :: "nat \<Rightarrow> nat"
    where "oct n = dbl (quad n)"
  CHOOSE oct
  END
\<close>)


end
