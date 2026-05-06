theory Test_Rewrite_QuantifiedGoal imports
  Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_QuantifiedGoal"]]

text \<open>
  Regression test for fastype_of: Bound crash when a looping rewrite
  rule is applied to a goal containing quantifiers.

  The rule @{text "my_wrap"} rewrites @{text "f x \<equiv> g (f x)"}, which is
  self-looping. @{text "check_looping_rules"} calls @{text "find_matching_subterms"}
  which descends into the body of the @{text "\<exists>"}-binder via the
  @{text "Abs"} case. Inside that body, subterms contain dangling
  @{text "Bound"} indices. When @{text "Pattern.match"} is called on
  these subterms, it invokes @{text "fastype_of"} which crashes on
  the loose @{text "Bound"}.
\<close>

definition "g (x::nat) \<equiv> x"
consts f :: \<open>'a \<Rightarrow> 'a\<close>

lemma my_wrap: "f x = g (f (x::nat))"
  by (simp add: g_def)

lemma quantified_rewrite_test:
  shows "\<exists>y::nat. f y = (0::nat)"
  by  aoa

end
