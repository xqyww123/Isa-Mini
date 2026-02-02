signature MINILANG_AGENT = sig
include MINILANG_AGENT

val apply : context_state -> thm option
val method : Method.method

val Agent_App : REPL_Server.App

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

val driver = Attrib.setup_config_string \<^binding>\<open>agent_driver\<close> (K "Gemini")
val step_limit = Attrib.setup_config_int \<^binding>\<open>agent_step_limit\<close> (K 20)
val total_time_limit = Attrib.setup_config_int \<^binding>\<open>agent_total_time_limit\<close> (K 120)
val parallel_runs = Attrib.setup_config_int \<^binding>\<open>agent_parallel_runs\<close> (K 1)

fun cfg_of ctxt = {
      driver = Config.get ctxt driver,
      budget = {
          step_limit = Config.get ctxt step_limit,
          total_timeout = SOME (Time.fromSeconds (Config.get ctxt total_time_limit)),
          parallel_runs = Config.get ctxt parallel_runs,
          QUERY_RET_LIMIT = SOME 30
        }
    }

local open MessagePackBinIO.Unpack in
val unpackBudget = unpackTuple4
              (unpackInt, unpackOption unpackInt, unpackInt, unpackOption unpackInt)
        #> apfst (fn (sl, tt, pN, QRL) => ({
              step_limit = sl,
              total_timeout = Option.map Time.fromSeconds tt,
              parallel_runs = pN,
              QUERY_RET_LIMIT = QRL
           } : budget))
val unpackCfg = unpackPair (unpackString, unpackBudget)
        #> apfst (fn (driver, b) => ({
              driver = driver, budget = b
           } : top_cfg))
end

fun is_dummy th =
  let fun chk (Const(\<^const_name>\<open>Pure.term\<close>, _) $ _) = true
        | chk (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X) = chk X
        | chk _ = false
   in Thm.is_dummy th orelse chk (Thm.prop_of th)
  end

fun apply' cfg (ctxt, sequent) =
  let
    exception Prf_Search_Fail
    fun evaluator time prf_str (ctxt, sequent) =
      let val (drv,prf) = deserialize prf_str
          val cfg = cfg_of_driver drv
          val budget = {
                    QUERY_RET_LIMIT = NONE,
                    parallel_runs = 1,
                    total_timeout = SOME time,
                    step_limit = ~1
                }
       in SOME (ctxt, run (cfg,budget) prf (ctxt, sequent))
       handle Minilang.OPR_FAIL _ => NONE
      end
    fun search_proof _ =
       let val drv = #driver cfg
           val n_runs =  Config.get ctxt parallel_runs
           val drivers = List.tabulate (n_runs, fn _ => drv)
           fun attempt drv = let
              val cfg' = { driver = drv, budget = #budget cfg }
              val state' = Runtime.exn_trace (fn () => run_agent cfg' (ctxt, sequent))
              val sequent' = conclude ctxt state'
            in
              if Thm.nprems_of sequent' = 0
              then SOME (serialize (drv, effective_cmds state'),
                         sequent')
              else NONE
            end
            handle exn as Exn.EXCEPTIONS [ERROR _] => if Exn.is_interrupt exn then Exn.reraise exn else NONE
  
           val start = Timing.start ()
           val winner =
            (case drivers of
                [] => NONE
              | [d] => attempt d
              | ds => Par_List.get_some attempt ds)
           val time = Timing.result start
        in case winner
             of SOME (prf, th) => ((#cpu time, prf), (ctxt, th))
              | NONE => raise Prf_Search_Fail
      end
     in let
      val (_, (_, sequent')) =
              Phi_Cache_DB.try_cached_proof_by_hash
                    evaluator search_proof (ctxt, sequent)
       in SOME sequent'
      end handle Prf_Search_Fail => NONE
   end

fun apply (ctxt, sequent) = apply' (cfg_of ctxt) (ctxt, sequent)

fun method _ (*using*) (ctxt, sequent) = Seq.make (fn () =>
  if is_dummy sequent then NONE
  else apply (ctxt, sequent)
    |> Option.map (fn sequent' => (Seq.Result (ctxt, sequent'), Seq.empty)) )

(*Run the agent under the current REPL proof state,
  and respond evaluation statistics (succeeded or not)*)
fun Agent_App (cin, cout, toplevel) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end

      val cfg = read unpackCfg
      val transition = Toplevel.empty
            |> Toplevel.proof (
                  Proof.refine_primitive (fn ctxt => fn sequent =>
                    \<^try>\<open>
                    let val (time, ret) = Timing.timing (apply' cfg) (ctxt, sequent)
                     in REPL_Server.output cout (packTuple3 (packBool, packInt, packInt))
                             ( is_some ret,
                               Time.toMilliseconds (#elapsed time),
                               Time.toMilliseconds (#cpu time)
                             )
                      ; BinIO.StreamIO.flushOut cout
                      ; the_default sequent ret
                    end
                    catch E as Minilang.OPR_FAIL (typ, msg) =>
                        let val typs = case typ of Minilang.INVALID_OPR => "INVALID_OPR : "
                                                 | Minilang.PROOF_FAIL  => "PROOF FAIL : "
                         in REPL_Server.output_err cout (typs ^ msg)
                          ; BinIO.StreamIO.flushOut cout
                          ; raise E
                        end
                      | E => (
                            REPL_Server.output_err cout (Runtime.exn_message E)
                          ; BinIO.StreamIO.flushOut cout
                          ; raise E )\<close> )
                  )
      val (_, toplevel') = Toplevel.command_errors false transition toplevel
   in the_default toplevel toplevel'
  end

val _ = REPL_Server.register_app "MiniLang_Agent" Agent_App

end