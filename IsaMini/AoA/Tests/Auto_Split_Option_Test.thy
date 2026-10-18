theory Auto_Split_Option_Test
  imports User_Operation_Test_Base
begin

text \<open>
  The configuration option \<open>AoA_auto_split\<close> (AUTO_INTRO_DECISION.md, section 8):
  true, the default, leaves the split segment as it is; false keeps it from
  running whatever the goal's size, and records "" so that a replay skips it too.
\<close>

ML \<open>
local
open User_Operation_Test
val ctxt = \<^context>
(*a goal large enough to set the segment off: a conjunction of 300 propositions*)
val goal =
  HOLogic.mk_Trueprop
    (foldr1 HOLogic.mk_conj (map (fn i => Free ("p" ^ string_of_int i, \<^typ>\<open>bool\<close>)) (1 upto 300)))
val st = Goal.init (Thm.cterm_of ctxt goal)
val _ = assert "the goal exceeds the threshold"
          (Infra_Filter.smart_size_of_term goal > Goal_Preprocess.preprocess_size_threshold)
in

val _ = assert "the option defaults to true" (Config.get ctxt AoA_auto_split)

(*1: on, the segment acts on the goal and records its branch*)
val (st_on, script_on) = Goal_Preprocess.preprocess_split_recorded ctxt st
val _ = assert "on: the state changes" (not (Thm.eq_thm_prop (st, st_on)))
val _ = assert "on: a branch is recorded" (script_on <> "")

(*2: off, the state is the one given and nothing is recorded*)
val ctxt_off = Config.put AoA_auto_split false ctxt
val (st_off, script_off) = Goal_Preprocess.preprocess_split_recorded ctxt_off st
val _ = assert "off: the state is the one given" (Thm.eq_thm_prop (st, st_off))
val _ = assert "off: nothing recorded, so a replay skips the segment" (script_off = "")
val _ = assert "off: the tactic form answers the state itself"
          (case Seq.pull (Goal_Preprocess.preprocess_split_tac ctxt_off st) of
             SOME (st', _) => Thm.eq_thm_prop (st, st')
           | NONE => false)

val _ = writeln "ALL PASS: Auto_Split_Option_Test"
end
\<close>

end
