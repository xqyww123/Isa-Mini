theory Inductive_Cases_Simps_Demo
  imports Main
begin

section \<open>Demo of inductive_cases and inductive_simps\<close>

text \<open>A toy inductive predicate: even numbers.\<close>

inductive is_even :: "nat \<Rightarrow> bool" where
  zero: "is_even 0"
| step: "is_even n \<Longrightarrow> is_even (Suc (Suc n))"


subsection \<open>The raw \<open>cases\<close> rule is general but clumsy\<close>

text \<open>Isabelle auto-generates \<open>is_even.cases\<close> from the introduction rules:
  \<^prop>\<open>\<lbrakk>is_even a; a = 0 \<Longrightarrow> P; \<And>n. \<lbrakk>a = Suc (Suc n); is_even n\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>

  Using it requires manually discharging the impossible cases when you
  know something about \<open>a\<close>.\<close>

lemma "is_even (Suc 0) \<Longrightarrow> False"
  apply (erule is_even.cases)
   apply simp        \<comment> \<open>case a=0: contradiction Suc 0 = 0\<close>
  apply simp         \<comment> \<open>case a=Suc(Suc n): contradiction Suc 0 = Suc(Suc n)\<close>
  done


subsection \<open>\<open>inductive_cases\<close>: a simplified, specialized elimination rule\<close>

text \<open>\<open>inductive_cases\<close> pre-analyses the introduction rules and builds a
  rule specialized to a particular form of the predicate argument.\<close>

inductive_cases is_even_Suc0E: "is_even (Suc 0)"

text \<open>This produces the theorem (printed via \<open>thm\<close>):
  @{thm is_even_Suc0E}

  i.e.  \<^prop>\<open>is_even (Suc 0) \<Longrightarrow> P\<close>.  The command has automatically
  proved that neither intro rule can produce \<open>is_even (Suc 0)\<close>, so the
  rule has no surviving cases — applying it immediately closes any goal.\<close>

thm is_even_Suc0E

lemma "is_even (Suc 0) \<Longrightarrow> False"
  by (erule is_even_Suc0E)     \<comment> \<open>one-liner now\<close>


text \<open>For a more interesting case, specialize at \<open>Suc (Suc n)\<close>:\<close>

inductive_cases is_even_SucSucE: "is_even (Suc (Suc n))"

text \<open>Equivalent ML-level construction using the function \<open>Inductive.mk_cases\<close>
  directly (this is what the \<open>inductive_cases\<close> command calls underneath):\<close>

ML \<open>
val is_even_SucSucE_via_ML =
  Inductive.mk_cases \<^context> \<^prop>\<open>is_even (Suc (Suc n))\<close>
\<close>


text \<open>What about the cleanup tactic \<open>Inductive.mk_cases_tac\<close> by itself?
  It is NOT a "do case analysis" tactic — it only \emph{cleans up} the
  goal state \emph{after} the raw \<open>cases\<close> rule has been applied. To use
  it in an apply-script, you must first apply \<open>is_even.cases\<close> to set up
  the case obligations, then \<open>mk_cases_tac\<close> discharges the dead branches:\<close>

lemma is_even_SucSucE_manual:
  assumes prem: "is_even (Suc (Suc n))"
  shows "(is_even n \<Longrightarrow> P) \<Longrightarrow> P"
  thm is_even.cases[OF prem]
  apply (rule is_even.cases [OF prem])
  \<comment> \<open>two subgoals from the raw cases rule:
        1. \<open>Suc (Suc n) = 0 \<Longrightarrow> (is_even n \<Longrightarrow> P) \<Longrightarrow> P\<close>      (impossible)
        2. \<open>\<And>na. Suc (Suc n) = Suc (Suc na) \<Longrightarrow> is_even na \<Longrightarrow>
                  (is_even n \<Longrightarrow> P) \<Longrightarrow> P\<close>      (specializes to na = n)\<close>
  by (tactic \<open>Inductive.mk_cases_tac \<^context>\<close>)
  \<comment> \<open>after \<open>mk_cases_tac\<close>: subgoal 1 is gone (Suc(Suc n) = 0 is False),
       subgoal 2 has its equation substituted (na := n), leaving just
       \<open>is_even n \<Longrightarrow> (is_even n \<Longrightarrow> P) \<Longrightarrow> P\<close>\<close>

thm is_even_SucSucE
text \<open>produces: \<^prop>\<open>is_even (Suc (Suc n)) \<Longrightarrow> (is_even n \<Longrightarrow> P) \<Longrightarrow> P\<close>

  i.e. the first intro rule (zero) was discarded as impossible, and the
  second was specialized so that the n's match — so the rule has exactly
  one surviving premise: \<^prop>\<open>is_even n \<Longrightarrow> P\<close>.\<close>

lemma "is_even (Suc (Suc (Suc (Suc 0)))) \<Longrightarrow> is_even 0"
  apply (erule is_even_SucSucE)
  apply (erule is_even_SucSucE)
  apply assumption
  done


subsection \<open>\<open>inductive_simps\<close>: a biconditional rewrite for simp\<close>

text \<open>\<open>inductive_simps\<close> turns the same case analysis into an \<open>iff\<close>
  equation that \<open>simp\<close> can use to unfold the predicate at a specific form.\<close>

inductive_simps is_even_0_iff: "is_even 0"
inductive_simps is_even_Suc0_iff: "is_even (Suc 0)"
inductive_simps is_even_SucSuc_iff: "is_even (Suc (Suc n))"

thm is_even_0_iff
text \<open>produces: \<^prop>\<open>is_even 0 = True\<close>\<close>

thm is_even_Suc0_iff
text \<open>produces: \<^prop>\<open>is_even (Suc 0) = False\<close>\<close>

thm is_even_SucSuc_iff
text \<open>produces: \<^prop>\<open>is_even (Suc (Suc n)) = is_even n\<close>\<close>


text \<open>Now \<open>simp\<close> can evaluate \<open>is_even\<close> on any concrete-ish argument:\<close>

lemma "is_even (Suc (Suc (Suc (Suc 0))))"
  by (simp add: is_even_0_iff is_even_SucSuc_iff)

lemma "\<not> is_even (Suc (Suc (Suc 0)))"
  by (simp add: is_even_Suc0_iff is_even_SucSuc_iff)


subsection \<open>Contrast: why it matters\<close>

text \<open>Without \<open>inductive_simps\<close>, asking \<open>simp\<close> to unfold \<open>is_even (Suc (Suc n))\<close>
  directly wouldn't work — the raw definition is a least fixed point and is
  not a rewrite rule. You'd have to do manual case analysis each time, or
  use the full \<open>is_even.cases\<close> and discharge impossible cases by hand.

  \<open>inductive_cases\<close>/\<open>inductive_simps\<close> automate that once, producing rules
  you can then use throughout the proof script.\<close>

end
