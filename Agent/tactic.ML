signature MINILANG_AGENT = sig
include MINILANG_AGENT

val method : Method.method

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

val driver = Attrib.setup_config_string \<^binding>\<open>agent_driver\<close> (K "Gemini")
val step_limit = Attrib.setup_config_int \<^binding>\<open>agent_step_limit\<close> (K 20)

fun cfg_of ctxt = {
      driver = Config.get ctxt driver,
      step_limit = Config.get ctxt step_limit
    }

fun is_dummy th =
  let fun chk (Const(\<^const_name>\<open>Pure.term\<close>, _) $ _) = true
        | chk (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X) = chk X
        | chk _ = false
   in Thm.is_dummy th orelse chk (Thm.prop_of th)
  end

fun method _ (*using*) (ctxt, sequent) = Seq.make (fn () =>
  if is_dummy sequent
  then NONE
  else let val cfg = cfg_of ctxt
      val state' = run_agent cfg (ctxt, sequent)
      val sequent' = conclude ctxt state'
   in SOME ((Seq.Result (ctxt, sequent')), Seq.empty)
  end)

end