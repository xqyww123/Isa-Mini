(*TODO: name anounymous hyps ""*)

signature MINILANG_AGENT_AoA = sig

type driver = string
val default_driver: driver
val agent_aoa_driver: string Config.T

type state_id = string
type states = Minilang.state Symtab.table

datatype acmd = Proof_Opr of {from: state_id, to: state_id, opr: MiniLang_Agent.xcmd}
              | Lookup_Fact of { state: state_id
                               , criterions: (bool * string Find_Theorems.criterion) list list}
              | Compute_Bindings of {state: state_id, var_names: string list, fact_names: string list}
              | Need_Intro of {state: state_id}
              | Exit

val AoA_RPC : driver * (MiniLang_Agent.cfg * MiniLang_Agent.budget)
           -> Proof.context * thm
           -> MiniLang_Agent.xcmd list * thm (*acomplished proof sequent*)

val method : thm list -> context_state -> context_state Seq.result Seq.seq

end

structure MiniLang_Agent_AoA : MINILANG_AGENT_AoA = struct

type driver = string
val default_driver = "ClaudeCode"

(* Config for driver selection *)
val agent_aoa_driver = Attrib.setup_config_string \<^binding>\<open>agent_AoA_driver\<close> (K default_driver)

type state_id = string
type states = Minilang.state Symtab.table
type cfg = MiniLang_Agent.cfg * MiniLang_Agent.budget

datatype acmd = Proof_Opr of {from: state_id, to: state_id, opr: MiniLang_Agent.xcmd}
              | Lookup_Fact of { state: state_id
                               , criterions: (bool * string Find_Theorems.criterion) list list}
              | Compute_Bindings of {state: state_id, var_names: string list, fact_names: string list}
              | Need_Intro of {state: state_id}
              | Exit

type context = {
    vars: (string * typ) list,
    hyps: (string * term list) list
  }
type goal = {context: context, goal: term}
type goals = {context: context, goals: goal list}

fun chk_initial_state (states:states) =
  if Symtab.size states = 1
  then case Symtab.lookup states "$init"
    of SOME state => state
     | NONE => error "Not an initial state"
  else error "Not an initial state"

fun general_vars_of (Abs (name,typ,X)) rets = general_vars_of X (insert (op =) (name,typ) rets)
  | general_vars_of (A $ B) rets = general_vars_of B (general_vars_of A rets)
  | general_vars_of (Free (name,typ)) rets = insert (op =) (name,typ) rets
  | general_vars_of (Var ((name,0),typ)) rets = insert (op =) (name,typ) rets
  | general_vars_of (Var ((name,i),typ)) rets = insert (op =) (name^"."^string_of_int i,typ) rets
  | general_vars_of _ rets = rets

(*
fun goals_of_term (seen_vars:(string * typ) list) (hhf:term) : goal =
      let val (vs,hs,cl) = Minilang.strip_meta_and_hol_hhf hhf
       in {context = {vars = filter_out (member (op =) seen_vars) vs,
                      hyps = map (pair "" o single) hs},
           goal=cl}
      end
*)

fun global_context_of (ctxt, goal_sequent) : context =
  let val local_facts = Facts.dest_static false
                            [(Proof_Context.facts_of (Local_Theory.target_of ctxt))]
                            (Proof_Context.facts_of ctxt)
                     |> filter (fn ("local.this", _) => false | _ => true)
                     |> map (apfst (fn s =>
                          if String.isPrefix "local." s
                          then String.substring (s, 6, size s - 6)
                          else s ) o
                          apsnd (map Thm.prop_of))
      val other_than_that = fold (fn (name, facts) =>
                                if name = "that"
                                then I
                                else fold (insert (op aconv)) facts) local_facts []
      val local_facts = local_facts
            |> map_filter (fn ("that", facts) =>
                                let val facts' = subtract (op aconv) other_than_that facts
                                 in if null facts'
                                  then NONE
                                  else SOME ("that", facts')
                                end
                            | (_, []) => NONE
                            | x => SOME x)
      val vs = Term.add_frees (Thm.prop_of goal_sequent) []
   in {vars=vs, hyps=local_facts}
  end

local open Find_Theorems in
fun map_criterion _ (Name s) = Name s
  | map_criterion _ Intro = Intro
  | map_criterion _ Elim = Elim
  | map_criterion _ Dest = Dest
  | map_criterion _ Solves = Solves
  | map_criterion F (Simp term) = Simp (F term)
  | map_criterion F (Pattern pat) = Pattern (F pat)
fun check_criterion ctxt =
  let val ctxt' = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
   in map_criterion (Syntax.read_term ctxt')
  end
fun uncheck_criterion ctxt = map_criterion (MiniLang_Agent.string_of_term ctxt)
end

local open MessagePackBinIO.Pack MessagePackBinIO.Unpack Remote_Procedure_Calling
in

fun context_packer ctxt =
  let val SOT  = MiniLang_Agent.string_of_term ctxt
      val SOTT = MiniLang_Agent.string_of_type ctxt
   in fn {vars, hyps}:context =>
        packPair (packPairList (packString, packString o SOTT),
                  packPairList (packString, packList packString o map SOT))
                 (vars, hyps)
  end

fun goal_packer ctxt =
  let val SOT  = MiniLang_Agent.string_of_term ctxt
      val context_packer = context_packer ctxt
   in fn {context,goal}:goal =>
        packPair (context_packer, packString o SOT) (context,goal)
  end

local open Find_Theorems in
fun pack_criterion (Name s) = packPair (packInt, packString) (0, s)
  | pack_criterion Intro  = packPair (packInt, packUnit) (1, ())
  | pack_criterion Elim   = packPair (packInt, packUnit) (2, ())
  | pack_criterion Dest   = packPair (packInt, packUnit) (3, ())
  | pack_criterion Solves = packPair (packInt, packUnit) (4, ())
  | pack_criterion (Simp term)   = packPair (packInt, packString) (5, term)
  | pack_criterion (Pattern pat) = packPair (packInt, packString) (6, pat)
val unpack_criterion =
  unpackPair_dep' unpackInt (
    fn 0 => unpackString #> apfst Name
     | 1 => unpackUnit   #> apfst (K Intro)
     | 2 => unpackUnit   #> apfst (K Elim)
     | 3 => unpackUnit   #> apfst (K Dest)
     | 4 => unpackUnit   #> apfst (K Solves)
     | 5 => unpackString #> apfst Simp
     | 6 => unpackString #> apfst Pattern
     | _ => raise Unpack
  )
end

val acmd_unpacker =
  unpackPair_dep' unpackInt (
    fn 1 => unpackTuple3 (unpackString, unpackString, MiniLang_Agent.xcmd_unpacker)
         #> apfst (fn (f,t,opr) => Proof_Opr {from=f, to=t, opr=opr})
     | 0 => unpackUnit
         #> apfst (K Exit)
     | 2 => unpackPair (unpackString, unpackList (unpackList (unpackPair (unpackBool, unpack_criterion))))
         #> apfst (fn (state, criterions) =>
            Lookup_Fact {state=state, criterions=criterions})
     | 3 => unpackTuple3 (unpackString, unpackList unpackString, unpackList unpackString)
         #> apfst (fn (state, var_names, fact_names) =>
            Compute_Bindings {state=state, var_names=var_names, fact_names=fact_names})
     | 4 => unpackString
         #> apfst (fn state => Need_Intro {state=state})
     | _ => raise Unpack)

fun acmd_packer (Proof_Opr {from, to, opr}) =
      packPair (packInt, packTuple3 (packString, packString, MiniLang_Agent.xcmd_packer))
               (1, (from,to,opr))
  | acmd_packer (Lookup_Fact {state, criterions}) =
      packPair (packInt, packPair (packString, packList (packList (packPair (packBool, pack_criterion)))))
               (2, (state, criterions))
  | acmd_packer (Compute_Bindings {state, var_names, fact_names}) =
      packPair (packInt, packTuple3 (packString, packList packString, packList packString))
               (3, (state, var_names, fact_names))
  | acmd_packer (Need_Intro {state}) =
      packPair (packInt, packString) (4, state)
  | acmd_packer Exit =
      packPair (packInt, packUnit) (0, ())

fun minilang_items_packer ctxt =
      context_packer ctxt o (fn (items:Minilang.items) => {vars = #1 items, hyps = #2 items})
fun minilang_tree_packer ctxt =
  let val term_packer = packString o MiniLang_Agent.string_of_term ctxt
      val item_packer = minilang_items_packer ctxt
      fun pack (Minilang.PROP (items, goal)) =
            packPair (packInt, packPair (item_packer, term_packer)) (0, (items, goal))
        | pack (Minilang.BUNDL (items, trees)) =
            packPair (packInt, packPair (item_packer, packList pack)) (1, (items, trees))
        | pack (Minilang.BLOCK tree) =
            packPair (packInt, pack) (2, tree)
   in pack
  end

fun minilang_message_packer ctxt =
  let val minilang_items_packer = minilang_items_packer ctxt
      fun pack (Minilang.New_Items items) =
            packPair (packInt, minilang_items_packer) (0, items)
        | pack (Minilang.Goals _) =
            packPair (packInt, packUnit) (1, ())
     (* | pack (Minilang.Goals goals) =
            packPair (packInt, packOption (packList goal_packer))
                     (1, Option.map (map (goals_of_term [])) goals) *)
        | pack (Minilang.Consider_Case (kase, items)) =
            packPair (packInt, packPair (packString, minilang_items_packer)) (2, (kase, items))
        | pack (Minilang.Internal exn) =
            (case exn of
               MiniLang_Agent.INTRO_BINDINGS {missing, auto_introduced, final} =>
                 packPair (packInt, packTuple3 (
                   MiniLang_Agent.pack_bindings,
                   MiniLang_Agent.pack_bindings,
                   MiniLang_Agent.pack_bindings
                 )) (3, (missing, auto_introduced, final))
             | _ => error "BUG #adli: unexpected Internal message")
   in packList pack o filter (fn Minilang.Internal (MiniLang_Agent.INTRO_BINDINGS _) => true
                                 | Minilang.Internal _ => false
                                 | _ => true)
  end

local open Facts Minilang_Helper in
fun interval_to_string (FromTo (i,j)) = [string_of_int i, "-", string_of_int j]
  | interval_to_string (From i) = [string_of_int i, "-"]
  | interval_to_string (Single i) = [string_of_int i]
fun intervals_to_string ivs = "(" :: implode_with "," (map interval_to_string ivs) @ [")"]
fun FactRef_to_string (Named ((name, _), NONE)) = name
  | FactRef_to_string (Named ((name, _), SOME [])) = name
  | FactRef_to_string (Named ((name, _), SOME ivs)) = String.concat (name :: intervals_to_string ivs)
  | FactRef_to_string (Fact s) = String.concat ["\<open>", REPL.trim_makrup s, "\<close>"]
val pack_FactRef = packString o FactRef_to_string
end

fun callback (cfg:cfg) (states:states Unsynchronized.ref) (conn:connection) =
  let exception EXIT
      exception ERR of string list
      val messages = Unsynchronized.ref []
      (* Global counters - persist across RPC calls *)
      val counters = {
        prem_counter = Synchronized.var "prem_counter" 0,
        fact_counter = Synchronized.var "fact_counter" 0
      } : MiniLang_Agent.counters
      fun listen_report msg =
            messages := msg :: !messages
      fun clean_report () =
            let val ret = rev (!messages)
             in messages := []
              ; ret
            end
   in Minilang.set_reporter listen_report
    ;(while true do
      case read conn acmd_unpacker
        of Exit => raise EXIT
         | Proof_Opr {from, to, opr} => (
            let val s0 = case Symtab.lookup (!states) from
                           of SOME s => s
                            | NONE => raise ERR ["beginning_state_not_found"]
                val (cfg', budget) = cfg
                val full_config = (cfg', budget, counters) : MiniLang_Agent.config
                val s1 = MiniLang_Agent.interpret full_config opr s0
                val ctxt' = Minilang.context_of s1
                val msgs = clean_report ()
             in states := Symtab.update (to, s1) (!states)
              ; write conn (packPair (minilang_message_packer ctxt', minilang_tree_packer ctxt'))
                           (msgs, Minilang.print_state s1)
            end handle Minilang.OPR_FAIL (Minilang.PROOF_FAIL, msg) =>
                write_error' conn packUnit
                  {message=[String.concat ["Proof failure: ", REPL.trim_makrup msg]], errobj=()}
              | Minilang.OPR_FAIL (Minilang.INVALID_OPR, msg) =>
                write_error' conn packUnit
                  {message=[String.concat ["Bad proof operation: ", REPL.trim_makrup msg]], errobj=()}
              | Minilang.OPR_FAIL (Minilang.TERMLANG, msg) =>
                write_error' conn packUnit
                  {message=[String.concat ["Syntax Error in Term Language: ", REPL.trim_makrup msg]], errobj=()}
           )
         | Lookup_Fact {state, criterions} =>
            let val s0 = case Symtab.lookup (!states) state
                           of SOME s => s
                            | NONE => raise ERR ["beginning_state_not_found"]
                val ctxt = Minilang.context_of s0
                val check_criterion = check_criterion ctxt
                val rets =
                    maps (fn criterion =>
                          Find_Theorems.find_theorems ctxt
                              (SOME (Minilang.leading_proof_sequent_of s0))
                              (SOME 31) false
                              (map (apsnd check_criterion) criterion)
                       |> snd) criterions
                 |> distinct (Thm.equiv_thm (Proof_Context.theory_of ctxt) o apply2 snd)
                val SOT  = MiniLang_Agent.string_of_term ctxt
             in write conn (packList (packPair (pack_FactRef, packString o SOT o Thm.prop_of))) rets
            end
         | Compute_Bindings {state, var_names, fact_names} => (
            let val s0 = case Symtab.lookup (!states) state
                           of SOME s => s
                            | NONE => raise ERR ["beginning_state_not_found"]
                val bindings = MiniLang_Agent.compute_bindings s0 var_names fact_names
             in write conn MiniLang_Agent.pack_bindings bindings
            end handle Minilang.OPR_FAIL (Minilang.INVALID_OPR, msg) =>
                write_error' conn packUnit
                  {message=[String.concat ["Bad operation: ", REPL.trim_makrup msg]], errobj=()}
           )
         | Need_Intro {state} =>
            let val s0 = case Symtab.lookup (!states) state
                           of SOME s => s
                            | NONE => raise ERR ["beginning_state_not_found"]
                val result = MiniLang_Agent.check_need_intro s0
             in write conn packBool result
            end
    ) handle EXIT => ()
           | ERR msgs => write_error' conn packUnit {message=msgs, errobj=()}
  end

val AoA_timeout = Time.fromSeconds 10
fun AoA_cmd (cfg:cfg) (states:states Unsynchronized.ref) : (context * driver, MiniLang_Agent.xcmd list * string option) command =
  let val s0 = chk_initial_state (!states)
      val ctxt = Minilang.context_of s0
      val s0_ptree = Minilang.print_state s0
   in {
      name = "IsaMini.AoA",
      arg_schema = (fn (global_context, driver) =>
          packTuple3 (context_packer ctxt, minilang_tree_packer ctxt, packString)
                     (global_context, s0_ptree, driver)),
      ret_schema = unpackPair (unpackList MiniLang_Agent.xcmd_unpacker, unpackOption unpackString),
      timeout = NONE (*SOME AoA_timeout*),
      callback = SOME (callback cfg states)
  }
  end

end

fun AoA_RPC (driver, cfg:cfg) (ctxt, sequent) =
  let val global_context = global_context_of (ctxt, sequent)
      val s0 = Minilang.INIT ctxt sequent
            |> Minilang.map_context ( Config.put Minilang.strict_end true
                                   #> Config.put Minilang.counter_mode "none"
                                   #> Config.put Minilang.INTRO_split_conj true
                                   #> Config.put Minilang.INTRO_mk_block true)
      val state = Unsynchronized.ref (Symtab.make [("$init", s0)])
      val (xcmds, s1o) =
            Remote_Procedure_Calling.call_command (AoA_cmd cfg state) (global_context, driver)
   in case s1o
   of SOME s1 => (
   case Symtab.lookup (!state) s1
   of SOME s1' =>
        if Minilang.is_finished s1'
        then let
          in if exists (fn MiniLang_Agent.SORRY _ => true | _ => false) xcmds
           then error "Internal Error: the returned proofs contains axiomatic sorry."
           else ()
           ; (xcmds, Minilang.conclude ctxt s1')
         end
        else error "Internal Error: the proof state returned by the Agent is not finished"
    | NONE => error "Internal Error: the state returned by the Agent is not found"
  ) | NONE => error "Agent gives up"
  end


(*** REPL App ***)

local open MessagePackBinIO.Unpack
val unpackBudget = unpackTuple4
              (unpackInt, unpackOption unpackInt, unpackInt, unpackOption unpackInt)
        #> apfst (fn (sl, tt, pN, QRL) => ({
              step_limit = sl,
              total_timeout = Option.map Time.fromSeconds tt,
              parallel_runs = pN,
              QUERY_RET_LIMIT = QRL
           } : MiniLang_Agent.budget))
val unpackCfg = unpackPair (unpackBool, unpackBool)
        #> apfst (fn (drafting, gussing_num_typ) => ({
              drafting = drafting,
              gussing_num_typ = gussing_num_typ
           } : MiniLang_Agent.cfg))
 in

fun AoA_REPL_App (cin, cout, toplevel) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end

      val (driver, cfg) = read (unpackPair (unpackString, unpackPair (unpackCfg, unpackBudget)))
      val transition = Toplevel.empty
            |> Toplevel.proof (
                  Proof.refine_primitive (fn ctxt => fn sequent =>
                    \<^try>\<open>
                    let val (time, (_, seq)) = Timing.timing (AoA_RPC (driver, cfg)) (ctxt, sequent)
                     in REPL_Server.output cout (packTuple3 (packBool, packInt, packInt))
                             ( true,
                               Time.toMilliseconds (#elapsed time),
                               Time.toMilliseconds (#cpu time)
                             )
                      ; BinIO.StreamIO.flushOut cout
                      ; seq
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
                          ; raise E )\<close>
                    )
                  )
      val (_, toplevel') = Toplevel.command_errors false transition toplevel
   in the_default toplevel toplevel'
  end
end

val _ = REPL_Server.register_app "Minilang.AoA" AoA_REPL_App

(*** The tactic ***)

fun is_dummy th =
  let fun chk (Const(\<^const_name>\<open>Pure.term\<close>, _) $ _) = true
        | chk (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X) = chk X
        | chk _ = false
   in Thm.is_dummy th orelse chk (Thm.prop_of th)
  end

fun method _ (*using*) (ctxt, sequent) = Seq.make (fn () =>
  if is_dummy sequent then NONE
  else let val driver = Config.get ctxt agent_aoa_driver
        in AoA_RPC (driver, MiniLang_Agent.default_cfg) (ctxt, sequent)
           |> (fn (_, sequent') => SOME (Seq.Result (ctxt, sequent'), Seq.empty))
       end )


end
