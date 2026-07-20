(* The AoA REPL-server app: registers "Minilang.AoA". Moved here out of
   Agent/agent_server.ML so that the Minilang_AoA session no longer depends on
   Isa_REPL. This session (Minilang_AoA_REPL) imports Minilang_AoA + Isa_REPL;
   the app just delegates to MiniLang_Agent_AoA.AoA_RPC (the same RPC core that
   `by aoa` uses), so no proof logic lives here. *)

local open MessagePackBinIO.Unpack
val unpackBudget = unpackTuple3 (unpackInt, unpackInt, unpackInt)
        #> apfst (fn (ts, mtc, mr) => ({
              timeout_seconds = ts,
              max_tool_calls = mtc,
              max_retries = mr
           } : MiniLang_Agent.budget))
val unpackCfg = unpackOption unpackBool
        #> apfst (fn aie => {auto_interpret_for_embedding = aie} : MiniLang_Agent.cfg)
 in

fun AoA_REPL_App (cin, cout, toplevel) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end

      val (invocation_id, driver, cfg, log_dir_override,
           retrieval_forking_override, interactive_retrieval_override) =
            read (unpackTuple6 (unpackString, unpackString,
                    unpackPair (unpackCfg, unpackBudget), unpackOption unpackString,
                    unpackOption unpackString, unpackOption unpackString))
      val transition = Toplevel.empty
            |> Toplevel.proof (
                  Proof.refine_primitive (fn ctxt => fn sequent =>
                    let val ctxt = case log_dir_override
                                    of SOME dir => Config.put MiniLang_Agent_AoA.AoA_log_dir dir ctxt
                                     | NONE => ctxt
                        val ctxt = case retrieval_forking_override
                                    of SOME v => Config.put MiniLang_Agent_AoA.AoA_retrieval_forking v ctxt
                                     | NONE => ctxt
                        val ctxt = case interactive_retrieval_override
                                    of SOME v => Config.put MiniLang_Agent_AoA.AoA_interactive_retrieval v ctxt
                                     | NONE => ctxt
                        val start_time = Timing.start ()
                        fun cost_tuple ({input, cache_write, cache_read, output,
                                         cost, tool_calls, isabelle_time, model_time,
                                         quota_wait_time} : MiniLang_Agent_AoA.agent_cost) =
                            (input, cache_write, cache_read, output, cost, tool_calls, isabelle_time, model_time, quota_wait_time)
                        val pack_result =
                              packTuple5 (packString, packInt, packInt,
                                          packOption packString,
                                          packTuple9 (packInt, packInt, packInt, packInt,
                                                      packReal, packInt, packReal, packReal, packReal))
                     in \<^try>\<open>
                        let val (_, seq, aoa_cost) = MiniLang_Agent_AoA.AoA_RPC (driver, cfg, invocation_id) MiniLang_Agent_AoA.usual_task (ctxt, sequent)
                            val time = Timing.result start_time
                         in REPL_Server.output cout pack_result
                                 ( "success",
                                   Time.toMilliseconds (#elapsed time),
                                   Time.toMilliseconds (#cpu time),
                                   NONE,
                                   cost_tuple aoa_cost
                                 )
                          ; BinIO.StreamIO.flushOut cout
                          ; seq
                        end
                        catch E as Minilang.OPR_FAIL (typ, msg) =>
                            let val typs = case typ of Minilang.INVALID_OPR => "INVALID_OPR : "
                                                     | Minilang.PROOF_FAIL  => "PROOF FAIL : "
                                                     | _ => ""
                             in REPL_Server.output_err cout (typs ^ msg)
                              ; BinIO.StreamIO.flushOut cout
                              ; raise E
                            end
                          | Remote_Procedure_Calling.Remote_Calling_Failure {message, ...} =>
                            let val time = Timing.result start_time
                             in REPL_Server.output cout pack_result
                                   ( "remote_error",
                                     Time.toMilliseconds (#elapsed time),
                                     Time.toMilliseconds (#cpu time),
                                     SOME message,
                                     cost_tuple MiniLang_Agent_AoA.zero_cost
                                   )
                              ; BinIO.StreamIO.flushOut cout
                              ; sequent
                            end
                          | MiniLang_Agent_AoA.Agent_Give_Up (reason, detail, aoa_cost) =>
                            let val time = Timing.result start_time
                                val det = if detail = "" then NONE
                                          else SOME detail
                             in REPL_Server.output cout pack_result
                                   ( reason,
                                     Time.toMilliseconds (#elapsed time),
                                     Time.toMilliseconds (#cpu time),
                                     det,
                                     cost_tuple aoa_cost
                                   )
                              ; BinIO.StreamIO.flushOut cout
                              ; sequent
                            end
                          | ERROR msg =>
                            ( REPL_Server.output_err cout msg
                            ; BinIO.StreamIO.flushOut cout
                            ; raise (ERROR msg) )
                          | E => (
                                REPL_Server.output_err cout (Runtime.exn_message E)
                              ; BinIO.StreamIO.flushOut cout
                              ; raise E )\<close>
                    end)
                  )
      val (_, toplevel') = Toplevel.command_errors false transition toplevel
   in the_default toplevel toplevel'
  end
end

val _ = REPL_Server.register_app "Minilang.AoA" AoA_REPL_App
