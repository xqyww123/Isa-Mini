theory Test_Rewrite_NO_SIMP_Leak imports
  Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_NO_SIMP_Leak"]]

text \<open>
  Bug reproduction: Rewrite on a premise with conclusion False leaks NO_SIMP
  into new premises.

  SIMPLIFY_GOAL_AND_PREMISES' wraps the conclusion inside Trueprop as
  @{text "Trueprop(NO_SIMP(False))"} when simplify_goal=false.
  @{text "clear_simpset"} preserves the classical wrapper (including any
  @{text "[dest!]"} rules) but clears simp rules. When the classical reasoner
  (via clarsimp) interacts with the @{text "NO_SIMP(False)"} conclusion,
  it can leak @{text "\<not> NO_SIMP False"} into new premises.

  The @{text "notnotD [dest!]"} declaration is standard in many AFP and
  verification projects (e.g. seL4) and is required to trigger the bug:
  it enables clarify to resolve double negation, after which impCE on the
  resulting goal can create @{text "\<not> NO_SIMP False"} as a premise.
\<close>

definition "is_nonzero (x::nat) \<equiv> (x \<noteq> 0)"

\<comment> \<open>This declaration is standard in many AFP entries and seL4. It enables
    the classical reasoner to resolve double negation during clarify.\<close>
declare notnotD [dest!]

lemma no_simp_leak_test:
  assumes h: "\<not> is_nonzero (f (a::nat))"
  shows "False"
  by aoa

end
