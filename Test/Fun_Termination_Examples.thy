theory Fun_Termination_Examples
  imports Main
begin

text \<open>Standard Isabelle/HOL termination proof templates.

  This file demonstrates the common `termination` proof patterns, ordered
  from most to least frequently used. Almost all `termination` proofs
  begin with a `(relation "...")` clause that names a well-founded
  relation; the residual subgoals say "each recursive call strictly
  decreases under this relation".\<close>


section \<open>Template 0: no `termination` needed — `fun` succeeds automatically\<close>

text \<open>Most simple structural recursions are handled by `fun`'s built-in
  `lexicographic_order_tac`. No manual termination proof is required.\<close>

fun fact :: "nat \<Rightarrow> nat" where
  "fact 0 = 1"
| "fact (Suc n) = Suc n * fact n"


section \<open>Template 1: `by (relation "measure f") auto`  (~60% of cases)\<close>

subsection \<open>Single-argument measure\<close>

function halve :: "nat \<Rightarrow> nat" where
  "halve 0 = 0"
| "halve (Suc 0) = 0"
| "halve (Suc (Suc n)) = Suc (halve n)"
  by pat_completeness auto

termination by (relation "measure (\<lambda>n. n)") auto


subsection \<open>Multi-argument function: pick one arg with a lambda\<close>

function gcd' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd' x 0 = x"
| "y \<noteq> 0 \<Longrightarrow> gcd' x y = gcd' y (x mod y)"
  by pat_completeness auto

termination by (relation "measure (\<lambda>(x, y). y)") (auto simp: mod_less_divisor)

text \<open>Equivalent shorthand using the standard projection \<open>snd\<close>:\<close>

fun gcd'' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "gcd'' x 0 = x"
| "gcd'' x y = gcd'' y (x mod y)"

thm gcd''.simps

  by pat_completeness auto

termination by (relation "measure snd") (auto simp: mod_less_divisor)


subsection \<open>List recursion via `length`\<close>

function rev_acc :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "rev_acc [] acc = acc"
| "rev_acc (x # xs) acc = rev_acc xs (x # acc)"
  by pat_completeness auto

termination by (relation "measure (\<lambda>(xs, _). length xs)") auto


section \<open>Template 2: `measures [f1, f2]` — lexicographic product  (~20%)\<close>

text \<open>When the recursion needs two (or more) measures combined in
  lexicographic order: the first must be non-increasing, and either
  strictly decreasing or equal with the next measure strictly decreasing.
  The classic example is Ackermann.\<close>

function ack :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ack 0 n = Suc n"
| "ack (Suc m) 0 = ack m (Suc 0)"
| "ack (Suc m) (Suc n) = ack m (ack (Suc m) n)"
  by pat_completeness auto

termination by (relation "measures [fst, snd]") auto

text \<open>A three-way lex product — contrived but illustrative.\<close>

function triple_rec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "triple_rec 0 0 0 = 0"
| "triple_rec (Suc a) b c = triple_rec a (Suc b) c"
| "triple_rec 0 (Suc b) c = triple_rec 0 b (Suc c)"
| "triple_rec 0 0 (Suc c) = triple_rec 0 0 c"
  by pat_completeness auto

termination
  by (relation "measures [\<lambda>(a, _, _). a, \<lambda>(_, b, _). b, \<lambda>(_, _, c). c]") auto


section \<open>Template 3: `relation` + `auto` with helper simp rules  (~10%)\<close>

text \<open>When `auto` is close but needs an extra fact. Add it via
  `simp:`, `intro:`, `elim:`, or `dest:` in the `auto` clause.\<close>

fun shrink :: "nat \<Rightarrow> nat" where
  "shrink n = (if n > 10 then n - 5 else 0)"

lemma shrink_le: "shrink n \<le> n"
  by (simp add: shrink.simps)

function iter :: "nat \<Rightarrow> nat" where
  "iter 0 = 0"
| "iter (Suc n) = Suc (iter (shrink n))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>n. n)") (auto simp: shrink_le le_imp_less_Suc)

text \<open>Another example: termination via a non-trivial arithmetic fact.\<close>

function div_iter :: "nat \<Rightarrow> nat" where
  "div_iter 0 = 0"
| "div_iter (Suc 0) = 0"
| "div_iter (Suc (Suc n)) = Suc (div_iter (Suc (Suc n) div 2))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>n. n)") (auto simp: div_less_dividend)


section \<open>Template 4: interactive Isar proof  (~5%)\<close>

text \<open>When `auto` isn't enough, structure the termination proof with
  `proof (relation "...")` and handle each obligation by hand. The
  first case is the well-foundedness check (usually trivial); subsequent
  cases are the decrease obligations, one per recursive call.\<close>

function collatz_steps :: "nat \<Rightarrow> nat" where
  "collatz_steps n = (if n \<le> 1 then 0
                      else if even n then Suc (collatz_steps (n div 2))
                      else Suc (collatz_steps (Suc (3 * n))))"
  by pat_completeness auto

text \<open>Proving collatz termination in general is open, so this is not a
  real example. A simpler interactive template:\<close>

function even_pred :: "nat \<Rightarrow> nat" where
  "even_pred 0 = 0"
| "even_pred (Suc 0) = 0"
| "even_pred (Suc (Suc n)) = Suc (even_pred n)"
  by pat_completeness auto

termination
proof (relation "measure (\<lambda>n. n)", goal_cases)
  case 1 \<comment> \<open>well-foundedness of measure\<close>
  show ?case by simp
next
  case (2 n) \<comment> \<open>decrease: (n, Suc (Suc n)) \<in> measure id\<close>
  then show ?case by simp
qed

text \<open>Apply-style equivalent — same thing, different syntax:\<close>

function even_pred' :: "nat \<Rightarrow> nat" where
  "even_pred' 0 = 0"
| "even_pred' (Suc 0) = 0"
| "even_pred' (Suc (Suc n)) = Suc (even_pred' n)"
  by pat_completeness auto

termination
  apply (relation "measure (\<lambda>n. n)")
   apply simp
  apply simp
  done


section \<open>Template 5: custom WF combinators  (~3%)\<close>

subsection \<open>\<open>inv_image\<close>: pull back a WF relation through a function\<close>

text \<open>Useful when the arguments aren't directly comparable but can be
  mapped to something that is.\<close>

function encode_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "encode_pair 0 n = n"
| "encode_pair (Suc m) n = encode_pair m (Suc n)"
  by pat_completeness auto

termination
  by (relation "inv_image (measure (\<lambda>m. m)) fst") auto


subsection \<open>\<open><*lex*>\<close>: explicit lex product of two WF relations\<close>

text \<open>Equivalent to `measures` in most cases, but useful when the
  underlying relations aren't both `measure` expressions.\<close>

function pair_rec :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_rec 0 _ = 0"
| "pair_rec (Suc m) 0 = pair_rec m 0"
| "pair_rec (Suc m) (Suc n) = pair_rec (Suc m) n"
  by pat_completeness auto

termination
  by (relation "measure fst <*lex*> measure snd") auto


subsection \<open>\<open>finite_psubset\<close>: recursion on strictly shrinking finite sets\<close>

function set_iter :: "nat set \<Rightarrow> nat" where
  "set_iter A = (if finite A \<and> A \<noteq> {} then Suc (set_iter (A - {Min A})) else 0)"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>A. if finite A then card A else 0)")
     (auto simp: card_Diff1_less)


section \<open>Template 6: `by size_change` — a different terminator  (rare)\<close>

text \<open>When lex_order can't find a good measure combination but the
  recursion IS size-decreasing by the size-change-termination principle.
  `size_change` doesn't start with `relation` — it's a distinct tactic.\<close>

function pairs :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pairs 0 _ = 0"
| "pairs _ 0 = 0"
| "pairs (Suc m) (Suc n) = Suc (pairs m n)"
  by pat_completeness auto

termination by size_change


section \<open>Decision tree: which template to try\<close>

text \<open>When writing a `termination` proof, try the templates in this order:

  1. \<^bold>\<open>Single measure with `auto`\<close>:
     @{text "termination by (relation \"measure f\") auto"}
     Pick the argument that shrinks most obviously. 60% of real functions
     are done here.

  2. \<^bold>\<open>Single measure with helper simp rules\<close>:
     @{text "termination by (relation \"measure f\") (auto simp: ...)"}
     When `auto` is close but needs an extra fact (a library lemma about
     `div`, `mod`, `length`, etc., or a custom helper).

  3. \<^bold>\<open>Lex product via `measures`\<close>:
     @{text "termination by (relation \"measures [f1, f2]\") auto"}
     When no single measure works but lex order of two does.

  4. \<^bold>\<open>Interactive Isar proof\<close>:
     @{text "termination proof (relation \"measure f\", goal_cases) ... qed"}
     When the decrease obligations require case analysis or induction.

  5. \<^bold>\<open>Custom WF combinators\<close>: @{term inv_image}, @{term "(<*lex*>)"},
     @{term finite_psubset}, @{term wfP}, ... For unusual recursion
     structures that don't fit the `measure`/`measures` shape.

  6. \<^bold>\<open>`by size_change`\<close>: alternative terminator, useful for multi-arg
     structural recursions that lex_order misses.

  7. \<^bold>\<open>`partial_function`\<close> or \<^bold>\<open>`function (domintros)` + manual
     domain proof\<close>: last resort for non-total or very complex cases.

  Rule of thumb: start with @{text "(relation \"measure f\") auto"} and
  only escalate when it fails. Almost every `termination` proof you'll
  write begins with `relation "..."` — the exception is `size_change`,
  which is the only common alternative.\<close>


fun f :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "even n \<Longrightarrow> f n m = m"
  | "odd n \<Longrightarrow> f n m = Suc m"
  by (pat_completeness?, auto)


fun merge :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
    "merge [] ys = ys"
  | "merge xs [] = xs"
  | "merge (x # xs) (y # ys) =
       (if x \<le> y then x # merge xs (y # ys)
                 else y # merge (x # xs) ys)"
    by pat_completeness auto

  termination by size_change

end
