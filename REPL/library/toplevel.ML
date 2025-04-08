signature MINILANG_TOP = sig

val REPL_App : REPL_Server.App

end

structure Minilang_Top : MINILANG_TOP = struct
open Minilang_Aux

type code = string (*head*) * string (*full code*)
type state = Minilang.state * code list
type history = state Symtab.table
val minlang_of = #1 o #1

(* val state_data = Thread_Data.var () : (state * history) Unsynchronized.ref Thread_Data.var *)

fun record_state name (state, history) = (state, Symtab.update (name, state) history)
fun rollback name (_, history) =
      case Symtab.lookup history name
        of SOME s' => (s', history)
         | NONE => raise REPL.REPL_fail ("Snapshot named " ^ name ^ " is not found")

local open MessagePackBinIO.Pack
in
fun pack_typ ctxt ty = packString (trim_markup (Syntax.string_of_typ  ctxt ty))
fun pack_term ctxt tm = packString (trim_markup (Syntax.string_of_term ctxt tm))
fun pack_items ctxt =
  let val pack_variables = packPairList (packString, pack_typ ctxt)
      val pack_facts     = packPairList (packString, packList (pack_term ctxt))
   in packPair (pack_variables, pack_facts)
  end
fun pack_tree ctxt =
  let open Minilang
      fun pack (PROP  (a,b)) = packTuple3 (packInt, pack_items ctxt, pack_term ctxt) (0,a,b)
        | pack (BUNDL (a,b)) = packTuple3 (packInt, pack_items ctxt, packList pack)  (1,a,b)
        | pack (BLOCK tree) = packPair   (packInt, pack) (2, tree)
   in pack
  end
fun pack_response' (ctxt, items, ccase, tree) =
      packTuple3 (pack_items ctxt, packOption packString, pack_tree ctxt)
                 (items, ccase, tree) 
val pack_response = packPair (packList pack_response', packBool)
end


fun RE cout msgs src s =
  let val toks = Minilang.lex_cmds src
      val oprs = map (` (Minilang.parse_cmds o single)) toks
      val code = Unsynchronized.ref []
      val items = Unsynchronized.ref Minilang.empty_items
      val consider_case = Unsynchronized.ref NONE
   in fold_map (fn (opr, toks) => fn (s, codes) =>
        let val cmd = Token.content_of (hd toks)
            val _ = msgs := []
            val s' = opr s
            val ctxt' = Minilang.context_of s'
            val _ = code := []
            val _ = items := Minilang.empty_items
            val _ = consider_case := NONE

            fun handle_msg (Minilang.New_Items items') =
                  items := Minilang.cat_items items' (!items)
              | handle_msg (Minilang.Consider_Case name) =
                  consider_case := SOME name
              | handle_msg (Minilang.Internal (Minilang.REPLACE_CMD cmd)) =
                  code := cmd :: !code
              | handle_msg (Minilang.Internal (Minilang.SH_PRF prfs)) =
                  if cmd = "END" orelse cmd = "NEXT"
                  then code := ("APPLY", "APPLY " ^ prfs) :: !code
                  else ()
              | handle_msg _ = ()

            val _ = List.app handle_msg (!msgs)
            val code' = case !code
                          of [] => [(cmd, String.concat (Minilang_Aux.print_toks toks))]
                           | L => L
            
            val tree = Minilang.print_state s'
                    |> Minilang.atomize_tree ctxt'
         in ((ctxt', !items, !consider_case, tree), (s', code' @ codes))
        end
      ) oprs s
    |> (fn (data, s') => (
        REPL_Server.output cout pack_response (data, Minilang.is_finished (fst s'))
      ; BinIO.StreamIO.flushOut cout
      ; s'))
  end

fun REPL cout cin msgs init_state =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end
      exception Termination
      fun iteration s =
        let val cmd = read unpackString
         in if String.isPrefix "\\" cmd
           then case cmd
             of "\\stamp" => let
                     val name = read unpackString
                     val s' = record_state name s
                  in REPL_Server.output cout packUnit ()
                   ; s'
                 end
              | "\\rollback" => let
                     val name = read unpackString
                     val s' = rollback name s
                  in REPL_Server.output cout packUnit ()
                   ; s'
                 end
              | "\\conclude" => let
                     val ctxt = Minilang.context_of (minlang_of s)
                     val ret = Minilang.conclude (Minilang.context_of (minlang_of init_state)) (minlang_of s)
                  in REPL_Server.output cout (packPair (pack_term ctxt, packString)) (Thm.prop_of ret, "")
                   ; s
                 end
              | "\\close" => ( REPL_Server.output cout packUnit ()
                             ; raise Termination )
              | "\\print" => let
                    val s0 = minlang_of s
                    val ctxt' = Minilang.context_of s0
                    val tree = Minilang.print_state s0
                 in REPL_Server.output cout pack_response
                            ([(ctxt', Minilang.empty_items, NONE, tree)],
                             Minilang.is_finished s0)
                  ; s
                end
              | "\\eval" => let
                    val (timeout, src) = read (unpackPair (unpackOption unpackInt, unpackString))
                    val timeout = Option.map Time.fromMilliseconds timeout
                 in case timeout
                      of SOME time => Timeout.apply time (apfst (RE cout msgs src)) s
                       | NONE      => apfst (RE cout msgs src) s
                end
              | "\\END_mode" => let
                    val mode = read unpackString
                    val _ = if member (op =) ["RELAXED", "COMPLETE_NEXT", "STRICT"] mode 
                            then ()
                            else raise REPL.REPL_fail "END_mode must be either STRICT, RELAXED or COMPLETE_NEXT"
                 in REPL_Server.output cout packUnit ()
                  ; s
                 |> apfst (apfst (
                      Minilang.map_context (Config.put Minilang.END_behavior mode)))
                end
              | bad => raise REPL.REPL_fail (
                  "Command " ^ String.substring (bad, 1, size bad - 1)
                             ^ " is unsupported in Minilang mode")
           else if String.isPrefix "\005" cmd
           then raise REPL.REPL_fail (
                  "Command " ^ String.substring (cmd, 1, size cmd - 1)
                             ^ " is only available in REPL mode, but \
                  \you are at Minilang mode.")
           else s
             |> apfst (RE cout msgs cmd)
        end
      val state = Unsynchronized.ref init_state
      val continue = Unsynchronized.ref true
   in while !continue do \<^try>\<open> (
        state := iteration (!state)
      ; BinIO.StreamIO.flushOut cout )
      catch REPL.REPL_fail E => (
                   REPL_Server.output_err cout E
                 ; BinIO.StreamIO.flushOut cout)
          | Termination => (
                   continue := false
                 ; BinIO.StreamIO.flushOut cout)
          | Minilang.OPR_FAIL (typ, msg) =>
              let val typs = case typ of Minilang.INVALID_OPR => "INVALID_OPR : "
                                       | Minilang.PROOF_FAIL  => "PROOF FAIL : "
               in REPL_Server.output_err cout (typs ^ msg)
                ; BinIO.StreamIO.flushOut cout
              end
          | E => ( REPL_Server.output_err cout (Runtime.exn_message E)
                 ; BinIO.StreamIO.flushOut cout) \<close>
  end


fun REPL_App (cin, cout) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val is = REPL.get_toplevel_state ()
   in if Toplevel.is_proof is
    then let
      val _ = REPL_Server.output cout packString ""
      val _ = BinIO.StreamIO.flushOut cout
      val ps = Toplevel.proof_of is
            |> Proof.map_context (Config.put Printer.show_markup false)
      val ms = Minilang.INIT' ps
      val s  = ((ms,[]), Symtab.empty)
      val msgs = Unsynchronized.ref []
      fun reporter msg = msgs := msg :: !msgs
       in Minilang.set_reporter reporter
        ; REPL cout cin msgs s
      end
    else (
      REPL_Server.output_err cout "Not in a proof"
    ; BinIO.StreamIO.flushOut cout )
  end


end