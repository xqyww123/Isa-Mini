signature MINILANG_AGENT = sig
include MINILANG_AGENT

type cfg = {
     driver : string,
     step_limit : int
  }

val REPL : cfg
        -> BinIO.StreamIO.instream Unsynchronized.ref
        -> BinIO.StreamIO.outstream
        -> context_state
        -> state

val REPL_App : cfg -> REPL_Server.App

val run_agent : cfg
             -> context_state
             -> MiniLang_Agent.state

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

type cfg = {
     driver : string,
     step_limit : int
  }

val VERSION = "0.1"

fun REPL {driver, step_limit} cin cout proof_state =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end

      val continue = Unsynchronized.ref true

      val step = Unsynchronized.ref 0
      exception Step_Limit_Exceed

      fun iteration s =
        let val cmd = read unpacker
            val _ = step := !step + 1
            val _ = if !step > step_limit then raise Step_Limit_Exceed else ()

            val (printer, s') = interpret cmd s
            val ret = printer ()

            val finished = is_finished s'
            val status = if finished then 1 else 0
         in REPL_Server.output cout (packPair (packInt, packString))
                                    (status, String.concat ret)
          ; BinIO.StreamIO.flushOut cout
          ; continue := not finished
          ; s'
        end

      val proof_state = proof_state
            |> apfst (
                   Config.put Printer.show_markup false
                #> Config.put Printer.show_type_emphasis false)
      val init_state = MiniLang_Agent.init proof_state
      val state = Unsynchronized.ref init_state

      val version = read unpackString
      val _ = if version = VERSION then ()
              else error ( "Client version mismatches. Except version " ^ VERSION
                         ^ ", but " ^ version ^ "is given.")
      val initial_printing = String.concat (print_goal init_state)

   in REPL_Server.output cout
            (packPair (packString, packString))
            (driver, initial_printing)
    ; BinIO.StreamIO.flushOut cout
    ; while !continue do \<^try>\<open>
        state := iteration (!state)
        catch
            Step_Limit_Exceed => (
                REPL_Server.output cout (packPair (packInt, packString)) (2, "")
              ; BinIO.StreamIO.flushOut cout
              ; continue := false )
          | REPL.REPL_fail E => (
                REPL_Server.output_err cout E
              ; BinIO.StreamIO.flushOut cout)
          | Minilang.OPR_FAIL (typ, msg) =>
              let val typs = case typ of Minilang.INVALID_OPR => "Invalid operation: "
                                       | Minilang.PROOF_FAIL  => ""
               in REPL_Server.output_err cout (typs ^ msg)
                ; BinIO.StreamIO.flushOut cout
              end
          | E => ( REPL_Server.output_err cout (Runtime.exn_message E)
                 ; BinIO.StreamIO.flushOut cout) \<close>
    ; BinIO.StreamIO.flushOut cout
    ; !state
  end

fun REPL_App cfg (cin, cout) =
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
        ; REPL cfg cin cout (Proof.context_of ps, #goal (Proof.simple_goal ps))
        ; ()
      end
      catch E => ( REPL_Server.output_err cout (Runtime.exn_message E)
                 ; BinIO.StreamIO.flushOut cout)\<close>
    else (
      REPL_Server.output_err cout "Not in a proof"
    ; BinIO.StreamIO.flushOut cout )
  end


fun launch_manager log_file =
  let open Posix.Process
   in case fork ()
   of NONE => (
        Posix.ProcEnv.setsid ()
      ; execp ("python3", ["-c",
            "import IsaMini_Agent; IsaMini_Agent.Manager('127.0.0.1:2357', \"" ^
            Bash.string log_file ^
            "\").start_server()"]))
    | SOME pid => (
        sleep (Time.fromSeconds 2)
      ; pid )
  end

fun get_agent_socket can_launch =
  let val addr = getenv "AGENT_MANAGER_ADDR"
      val addr = if addr = "" then "127.0.0.1:2357" else addr

      val log_name = Date.fmt "%Y-%m-%d-%H-%m-%d" (Date.fromTimeLocal (Time.now ())) ^ ".log"
      val log_path = Path.appends [ Resources.master_directory \<^theory>,
                                    Path.basic "logs",
                                    Path.basic log_name ]
                  |> Path.implode
      fun err() = error ("Failed to launch the Agent Manager. You may check the log " ^
                         log_path ^ " for more information.")

      val sock = INetSock.TCP.socket ()

      fun parse_addr address =
         let fun err () = error ("Bad address: " ^ quote address)
             val (host, port) =
                   (case space_explode ":" address of [h, p] =>
                           (case NetHostDB.getByName h of SOME host => host | NONE => err (),
                            case Int.fromString p of SOME port => port | NONE => err ())
                       | _ => err ())
          in INetSock.toAddr (NetHostDB.addr host, port)
         end

      val addr' = parse_addr addr
   in if Socket.connectNB (sock, addr')
    then sock
    else let
      val timeout = SOME (Time.fromSeconds 5)
      val {wrs, exs, ...} = Socket.select {
          rds = [],
          wrs = [Socket.sockDesc sock],
          exs = [Socket.sockDesc sock],
          timeout = timeout
      }
      fun handle_err () = (
          Socket.close sock;
          if can_launch
          then ( launch_manager log_path
               ; get_agent_socket false )
          else err () )
     in case (wrs, exs)
          of (_::_, []) => (* Ready for writing - check for errors *)
              let val errorOccurred = Socket.Ctl.getERROR sock
               in if errorOccurred
                  then handle_err ()
                  else sock
              end
           | _ => handle_err ()
    end
  end

fun run_agent cfg proof_state =
  let val socket = get_agent_socket true
      val (cin, cout) = REPL_Server.make_streams socket
      val cin = Unsynchronized.ref cin
   in REPL cfg cin cout proof_state
  end

end
