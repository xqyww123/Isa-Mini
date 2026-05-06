theory Test_Induction_IHFactRef
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_IHFactRef"]]

text \<open>
  Reproducer: referencing the induction hypothesis by its displayed
  name ``1.IH`` fails to parse.

  After ``Induction n`` via ``nat_less_induct`` the case's hyp is
  bound as ``1.IH`` (``Binding.qualify_name true binding`` in
  ``library/proof.ML:2320``), and Minilang's ``Consider_Case`` hands
  that qualified name verbatim to the Python side, which prints::

    assuming premises:
      - 1.IH: \<forall>m<n. ...

  When the agent echoes ``1.IH`` back as a fact reference,
  ``agent.ML`` / ``read_fact`` calls ``Parse.thm`` which tokenizes
  ``1.IH`` as three separate tokens ``[1, ., IH]`` (because
  ``long_ident`` requires both segments to be identifiers, and ``1``
  is a ``Nat`` token). ``Parse.thm`` then consumes only the leading
  ``1`` and leaves ``.IH`` unconsumed, so ``Scan.read`` returns
  ``NONE`` and the call errors out with::

    Cannot parse "1.IH" as a fact reference

  Observed live at session DABBC86F4_165BA82 (Isabelle RPC log,
  2026-04-21 00:47:07).
\<close>

lemma
  fixes p :: nat
  shows "True"
  by aoa

end
