theory Tactic_Replay_Test
  imports User_Operation_Test_Base
begin

text \<open>
  \<open>TACTIC\<close> in \<open>interpret_i\<close> (docs/TACTIC_DESIGN.md, section 5.2), in a theory
  with NO \<open>AoA_tactics\<close> declaration: ML checks no whitelist, so a recorded
  \<open>TACTIC\<close> replays and a live one runs whatever the whitelist; a LIVE run
  reports its times and is never capped by a record; a REPLAY with a record is
  limited by \<open>embedded_replay_limits\<close> alone ("Tactic replay timed out"), the
  inner \<open>mini_single_cmd_timeout\<close> -- which reads "Timeout" on an uncapped run
  -- not applying to it.
\<close>

(*a method that takes four seconds, leaving the goal as it is*)
method_setup sleep_4s = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (fn st =>
  (Time.sleep (seconds 4.0); Seq.single st)))\<close>
(*a method that never returns; sleeping, so that it is interruptible*)
method_setup spin = \<open>Scan.succeed (fn _ => SIMPLE_METHOD (fn _ =>
  let fun loop () = (Time.sleep (seconds 0.05); loop ()) in loop () end))\<close>

ML \<open>
local
open User_Operation_Test MiniLang_Agent
val ctxt = Named_Target.theory_init \<^theory>
fun config mode : MiniLang_Agent.config =
  (fst default_cfg, snd default_cfg, {prem_counter = Synchronized.var "Tactic_Replay_Test" 0}, mode)
fun run mode cmd s = Minilang.record_reporter (interpret_i (config mode) cmd) s
fun tactic name recorded = TACTIC (name, "", [], [], recorded)
val tiny = Phi_Proof_Store.times_of_ms (1, 1)
val generous = Phi_Proof_Store.times_of_ms (60000, 60000)
fun goals_messages msgs = map_filter (fn Minilang.Goals gs => SOME gs | _ => NONE) msgs
fun reported_times msgs = exists (fn Minilang.Internal (TACTIC_TIMES _) => true | _ => false) msgs
fun refused text f =
  (case Exn.result f () of
      Exn.Exn (Minilang.OPR_FAIL (_, msg)) =>
        assert ("expected " ^ quote text ^ ", got " ^ quote msg) (msg = text)
    | Exn.Exn exn => error ("expected OPR_FAIL, got " ^ Runtime.exn_message exn)
    | Exn.Res _ => error ("expected the refusal " ^ quote text))
val simp = Method.check_name ctxt ("simp", Position.none)
val trivial = "(1::nat) + 1 = 2"
in

(*1: LIVE, no record: the goal closes (one Goals, of no subgoal) and the times are reported*)
val (_, msgs1) = run LIVE (tactic simp NONE) (state_of ctxt trivial)
val _ = assert "LIVE: the goal is closed" (goals_messages msgs1 = [[]])
val _ = assert "LIVE: TACTIC_TIMES reported" (reported_times msgs1)

(*2: REPLAY with a record, the whitelist empty: accepted and closed; a capped run reports no times*)
val (_, msgs2) = run REPLAY (tactic simp (SOME generous)) (state_of ctxt trivial)
val _ = assert "REPLAY: the goal is closed" (goals_messages msgs2 = [[]])
val _ = assert "REPLAY: no TACTIC_TIMES" (not (reported_times msgs2))

(*3: REPLAY with a tiny record caps a method that never returns*)
val _ = refused "Tactic replay timed out"
          (fn () => run REPLAY (tactic \<^method>\<open>spin\<close> (SOME tiny)) (state_of ctxt trivial))

(*4: LIVE never caps: the same tiny record, a method of four seconds (beyond the 3 s cap) runs*)
val (_, msgs4) = run LIVE (tactic \<^method>\<open>sleep_4s\<close> (SOME tiny)) (state_of ctxt trivial)
val _ = assert "LIVE with a record: the method ran (the goal stays)" (length (goals_messages msgs4) = 1)
val _ = assert "LIVE with a record: the times are measured anew" (reported_times msgs4)

(*5: the inner timeout, mini_single_cmd_timeout, on an uncapped run; a capped
  REPLAY is limited by the cap alone -- under a 1 s inner limit, a method of
  four seconds with a generous record runs through*)
val ctxt1s = Config.put Minilang.mini_single_cmd_timeout 1000 ctxt
val _ = refused "Timeout" (fn () => run LIVE (tactic \<^method>\<open>spin\<close> NONE) (state_of ctxt1s trivial))
val (_, msgs5) = run REPLAY (tactic \<^method>\<open>sleep_4s\<close> (SOME generous)) (state_of ctxt1s trivial)
val _ = assert "capped REPLAY: the inner limit does not apply" (length (goals_messages msgs5) = 1)

val _ = writeln "ALL PASS: Tactic_Replay_Test"
end
\<close>

end
