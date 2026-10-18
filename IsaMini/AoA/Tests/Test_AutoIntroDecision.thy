theory Test_AutoIntroDecision
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AutoIntroDecision"]]

(* docs/AUTO_INTRO_DECISION.md section 7: the three layers of the automatic
   Intro decision through a real AoA call. The hook, declared on the theory,
   forces the automatic Intro on any goal mentioning Suc, over the exemption;
   the exemption, declared on the proof context of the one call as TAT
   declares, keeps it from goals concluding 0 \<le> _; every other goal gets the
   default. *)
setup \<open>Context.theory_map (Auto_Intro.add_hook ("Suc", fn _ => fn goal =>
  if Term.exists_Const (fn (c, _) => c = \<^const_name>\<open>Suc\<close>) goal then SOME Auto_Intro.Intro else NONE))\<close>

lemma auto_intro_decision:
  shows "\<forall>x::nat. 0 \<le> x"
  using [[aoa_no_auto_intro whole_prop "0 \<le> (_::nat)"]]
  by   aoa

end
