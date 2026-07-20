theory Test_HOL_TAG_Leak
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.HOL_TAG_Leak"]]

text \<open>
  Reproducer for the HOL.TAG leak in induction hypotheses.

  The auto-insert-facts mechanism (enabled per-session in
  Agent/agent_server.ML; see library/proof.ML's
  `induct_auto_insert_facts`) wraps local facts mentioning the
  inducted/generalized variables in `HOL.TAG` and inserts them as goal
  premises before induction so they get generalized along with the
  arbitrary variables. After induction, `update_tampered` reconstitutes
  the per-case top-level facts under their original names, but the
  `HOL.TAG` wrap inside the IH proposition itself is never removed --
  the agent sees `HOL.TAG (...)` literally.

  Triggering conditions:
    1. A local hypothesis mentioning a variable being generalized.
    2. An induction rule whose IH quantifies the inducted variable
       (e.g. `nat_less_induct`).

  Observed in interaction logs:
    DA348EF63_14FD684 (IMO 1988 P6, Vieta jumping)
    DA36C4FF0_17E38C8 (`prime (f i)` strong induction)
\<close>

lemma "(i::nat) \<le> p \<Longrightarrow> P i"
  by aoa

end
