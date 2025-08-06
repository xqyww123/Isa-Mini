signature MINILANG_AGENT = sig
include MINILANG_AGENT

val REPL : BinIO.StreamIO.instream Unsynchronized.ref
        -> BinIO.StreamIO.outstream
        -> Proof.state
        -> unit

val REPL_App : REPL_Server.App

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

fun REPL cin cout proof_state =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end
      val msgs = Unsynchronized.ref []
      val continue = Unsynchronized.ref true

      fun reporter msg = msgs := msg :: !msgs

      fun iteration s =
        let val ctxt = context_of s
            val cmd = read unpacker
                   |> check_command ctxt
            val (printer, s') = interpret cmd s
            val ret = printer ()

            fun prt (Minilang.Goals (SOME goals)) =
                  if length goals <= 1
                  then []
                  else "The operation derives " :: string_of_int (length goals) :: " subgoals:\n"
                    :: maps (fn goal => ["- " ^ Syntax.string_of_term ctxt goal ^ "\n"] ) goals
                     @ ["\n"]
              | prt _ = []
            val msg_ret = maps prt (!msgs)
            val _ = msgs := []

            val ret = ret @ "\n" :: msg_ret @ print_goal s'
            val finished = is_finished s'
         in REPL_Server.output cout (packPair (packBool, packString))
                                    (finished, String.concat ret)
          ; continue := not finished
          ; s'
        end
      val init_state = MiniLang_Agent.init proof_state
      val state = Unsynchronized.ref init_state
   in Minilang.set_reporter reporter
    ; while !continue do \<^try>\<open> (
        state := iteration (!state)
      ; BinIO.StreamIO.flushOut cout )
      catch REPL.REPL_fail E => (
                   REPL_Server.output_err cout E
                 ; BinIO.StreamIO.flushOut cout)
          | Minilang.OPR_FAIL (typ, msg) =>
              let val typs = case typ of Minilang.INVALID_OPR => "Invalid operation: "
                                       | Minilang.PROOF_FAIL  => "Operation fails: "
               in REPL_Server.output_err cout (typs ^ msg)
                ; BinIO.StreamIO.flushOut cout
              end
          | E => ( REPL_Server.output_err cout (Runtime.exn_message E)
                 ; BinIO.StreamIO.flushOut cout) \<close>
  end

fun REPL_App (cin, cout) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end

      val is = REPL.get_toplevel_state ()
   in if Toplevel.is_proof is
    then \<^try>\<open>let
      val (hasty, SH_params) =
              read (unpackPair (unpackBool, unpackOption unpackString))
      val ps = Toplevel.proof_of is
            |> Proof.map_context (
                  Config.put Printer.show_markup false
            (* #> Config.put Phi_Sledgehammer_Solver.hasty_mode hasty *)
               #> Config.put Phi_Sledgehammer_Solver.sledgehammer_params (the_default "" SH_params))
       in REPL_Server.output cout packString "0.3.5"
        ; BinIO.StreamIO.flushOut cout
        ; REPL cin cout ps
      end
      catch E => ( REPL_Server.output_err cout (Runtime.exn_message E)
                 ; BinIO.StreamIO.flushOut cout)\<close>
    else (
      REPL_Server.output_err cout "Not in a proof"
    ; BinIO.StreamIO.flushOut cout )
  end

end
