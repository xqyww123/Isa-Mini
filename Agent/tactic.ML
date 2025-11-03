signature MINILANG_AGENT = sig
include MINILANG_AGENT

val method : Method.method

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

val driver = Attrib.setup_config_string \<^binding>\<open>agent_driver\<close> (K "Gemini")
val step_limit = Attrib.setup_config_int \<^binding>\<open>agent_step_limit\<close> (K 20)
val parallel_runs = Attrib.setup_config_int \<^binding>\<open>agent_parallel_runs\<close> (K 1)

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
(*
fun method _ (*using*) (ctxt, sequent) = Seq.make (fn () =>
  if is_dummy sequent
  then NONE
  else let val cfg = cfg_of ctxt
      val state' = Runtime.exn_trace (fn () => run_agent cfg (ctxt, sequent))
      val sequent' = conclude ctxt state'
   in SOME ((Seq.Result (ctxt, sequent')), Seq.empty)
  end)
*)
fun method _ (*using*) (ctxt, sequent) = Seq.make (fn () =>
  if is_dummy sequent then NONE
  else let val cfg = cfg_of ctxt
         val drv = #driver cfg
         val n_runs =  Config.get ctxt parallel_runs
         val drivers = List.tabulate (n_runs, fn _ => drv)
         fun attempt drv = let
            val cfg' = { driver = drv, step_limit = #step_limit cfg }
            val state' = Runtime.exn_trace (fn () => run_agent cfg' (ctxt, sequent))
            val sequent' = conclude ctxt state'
          in
            if Thm.nprems_of sequent' = 0 then SOME sequent' else NONE
          end
          handle exn as Exn.EXCEPTIONS [ERROR _] => if Exn.is_interrupt exn then Exn.reraise exn else NONE

         val winner =
          (case drivers of
              [] => NONE
            | [d] => attempt d
            | ds => Par_List.get_some attempt ds)
    in Option.map(fn sequent' => (Seq.Result (ctxt, sequent'), Seq.empty)) winner
  end)

end