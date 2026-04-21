theory Induct_HO_Unif_Probe
  imports Minilang.Minilang
begin

declare [[quick_and_dirty]]

section \<open>Deterministic reproduction: degenerate IH when the induction target
  appears in \<open>arbitrary:\<close>\<close>

text \<open>Reproduces the HO-unification pathology observed in the AoA agent
  log \<^file>\<open>/tmp/t1\<close> (snapshot after \<open>amend\<close> of step 2 at 2026-04-21
  17:46:31; full proof tree in
  \<open>$ISABELLE_HOME_USER/log/AoA/DAF690E06_168BB2A/proofs.yaml\<close>).

  \<^bold>\<open>Trigger:\<close> pass the induction target variable (here \<open>i\<close>) in the
  \<open>arbitrary:\<close> clause, together with \<open>induct_auto_insert_facts = true\<close>
  and a local fact \<open>ile\<close> mentioning \<open>i\<close>. The resulting IH contains
  schematic variables disconnected from the induction case variable,
  making it logically vacuous as an induction hypothesis.

  \<^bold>\<open>Root cause in the agent's path:\<close> \<^file>\<open>../IsaMini_Agent_AoA/model.py\<close>
  line 6235 strips the target variable from \<open>self.variables\<close> only
  inside \<open>if is_init:\<close>. On \<open>amend\<close> (\<open>is_init = False\<close>) the target
  \<open>i\<close> stays in \<open>self.variables\<close> with status \<open>generalized\<close>, so
  \<open>beginning_opr()\<close> at line 6301 emits \<open>arbitrary = [i, ile]\<close> to the
  ML side. The exact ML call logged at 17:46:31 is
  \<open>INDUCT(('i', None, ['i', 'ile'], 'less_induct'))\<close>.\<close>


ML \<open>
fun print_state_tac label ctxt : tactic =
  fn st => (
    tracing ("=== " ^ label ^ " ===");
    tracing (Pretty.string_of
      (Pretty.chunks (Goal_Display.pretty_goals ctxt st)));
    all_tac st
  )
\<close>


subsection \<open>Baseline: well-formed IHs\<close>

text \<open>All of these produce the canonical IH
  \<open>\<And>y. y < x \<Longrightarrow> y \<le> p - 2 \<Longrightarrow> Q (f y)\<close>, demonstrating that the
  pathology is not intrinsic to \<open>less_induct\<close>, to \<open>induct_auto_insert_facts\<close>,
  or to having a premise that mentions the target.\<close>

context
  fixes p :: nat
    and f :: "nat \<Rightarrow> nat"
    and Q :: "nat \<Rightarrow> bool"
begin

lemma baseline_raw_isabelle_using:
  assumes ile: "i \<le> p - 2"
  shows "Q (f i)"
  using ile
  apply (induction i rule: less_induct)
  apply (tactic \<open>print_state_tac "baseline: raw induct + using" @{context}\<close>)
  sorry

declare [[induct_auto_insert_facts]]

lemma baseline_minilang_no_arbitrary:
  assumes ile: "i \<le> p - 2"
  shows "Q (f i)"
  apply (min_script \<open>INDUCT i rule: less_induct PRINT SORRY\<close>)
  done

lemma baseline_minilang_arbitrary_just_ile:
  assumes ile: "i \<le> p - 2"
  shows "Q (f i)"
  apply (min_script \<open>INDUCT i arbitrary: ile rule: less_induct PRINT SORRY\<close>)
  done

end


subsection \<open>Pathology: target variable in \<open>arbitrary:\<close>\<close>

text \<open>Adding the target \<open>i\<close> to \<open>arbitrary:\<close> flips the IH into a
  degenerate shape. Reproduces byte-for-byte the IH from the agent log.\<close>

context
  fixes p :: nat
    and f :: "nat \<Rightarrow> nat"
    and Q :: "nat \<Rightarrow> bool"
begin

declare [[induct_auto_insert_facts]]

text \<open>Minimal form: target + fact name, matching the exact ML call logged
  at agent 17:46:31. Expected IH (observed):
  \<open>less.IH : \<lbrakk>?y < x; ?i \<le> p - 2\<rbrakk> \<Longrightarrow> Q (f ?i)\<close>
  --- note the two independent schematics \<open>?y\<close> and \<open>?i\<close>.\<close>

lemma pathology_minimal_less_induct:
  assumes ile: "i \<le> p - 2"
  shows "Q (f i)"
  apply (min_script \<open>INDUCT i arbitrary: i ile rule: less_induct PRINT SORRY\<close>)
  done

text \<open>Full agent shape: Rabinowitz outer context + Intro unpacking +
  \<open>arbitrary: i\<close> (even without the extra \<open>ile\<close> name). Still degenerate
  --- confirming that the pathology is triggered by the target-in-arbitrary
  alone, independent of the fact-name being in the list.\<close>

lemma pathology_rabinowitz_less_induct:
  shows "(\<forall>x. f x = x * x + x + p) \<longrightarrow>
         (\<forall>k. k \<le> p div 3 \<longrightarrow> Q (f k)) \<longrightarrow>
         (\<forall>i. i \<le> p - 2 \<longrightarrow> Q (f i))"
  apply (min_script \<open>INTRO INTRO INTRO
    INDUCT i arbitrary: i rule: less_induct PRINT SORRY\<close>)
  done

text \<open>Same shape but with monomorphic \<open>nat_less_induct\<close>. Observed IH:
  \<open>1.IH : \<forall>m<n. \<forall>x\<le>p - 2. Q (f x)\<close>
  --- the \<open>\<forall>x\<le>p-2. Q (f x)\<close> subformula is \<^emph>\<open>the original goal's
  conclusion verbatim\<close>, quantified under an \<open>m < n\<close> antecedent that it
  does not depend on. Still vacuous. So the trigger is not
  polymorphic-rule-specific --- my earlier claim that
  \<open>nat_less_induct\<close> sidesteps the issue was wrong.\<close>

lemma pathology_rabinowitz_nat_less_induct:
  shows "(\<forall>x. f x = x * x + x + p) \<longrightarrow>
         (\<forall>k. k \<le> p div 3 \<longrightarrow> Q (f k)) \<longrightarrow>
         (\<forall>i. i \<le> p - 2 \<longrightarrow> Q (f i))"
  apply (min_script \<open>INTRO INTRO INTRO
    INDUCT i arbitrary: i rule: nat_less_induct PRINT SORRY\<close>)
  done

end

end
