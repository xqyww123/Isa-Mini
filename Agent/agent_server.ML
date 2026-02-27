(*TODO: name anounymous hyps ""*)

signature MINILANG_AGENT_AoA = sig

type driver = string
val default_driver: driver

type state_id = string
type states = Minilang.state Symtab.table

datatype acmd = Proof_Opr of {from: state_id, to: state_id, opr: MiniLang_Agent.xcmd}
              | Lookup_Fact of { state: state_id
                               , criterions: (bool * string Find_Theorems.criterion) list list}
              | Exit

val AoA_RPC : driver * (MiniLang_Agent.cfg * MiniLang_Agent.budget)
           -> Proof.context * thm
           -> MiniLang_Agent.xcmd list * thm (*acomplished proof sequent*)

val method : thm list -> context_state -> context_state Seq.result Seq.seq

end

structure MiniLang_Agent_AoA : MINILANG_AGENT_AoA = struct

type driver = string
val default_driver = "ClaudeCode"

type state_id = string
type states = Minilang.state Symtab.table
type cfg = MiniLang_Agent.cfg * MiniLang_Agent.budget

datatype acmd = Proof_Opr of {from: state_id, to: state_id, opr: MiniLang_Agent.xcmd}
              | Lookup_Fact of { state: state_id
                               , criterions: (bool * string Find_Theorems.criterion) list list}
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

fun strip_HHF (vs, hs) (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (name, typ, X))
      = strip_HHF ((name,typ)::vs, hs) X
  | strip_HHF (vs, hs) (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ H $ X)
      = strip_HHF (vs, H :: hs) X
  | strip_HHF (vs, hs) (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = strip_HHF (vs, hs) X
  | strip_HHF (vs, hs) (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, typ, X))
      = strip_HHF ((name,typ)::vs, hs) X
  | strip_HHF (vs, hs) (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ H $ X)
      = strip_HHF (vs, H :: hs) X
  | strip_HHF (vs, hs) X = (rev vs, rev hs, X)

fun general_vars_of (Abs (name,typ,X)) rets = general_vars_of X (insert (op =) (name,typ) rets)
  | general_vars_of (A $ B) rets = general_vars_of B (general_vars_of A rets)
  | general_vars_of (Free (name,typ)) rets = insert (op =) (name,typ) rets
  | general_vars_of (Var ((name,0),typ)) rets = insert (op =) (name,typ) rets
  | general_vars_of (Var ((name,i),typ)) rets = insert (op =) (name^"."^string_of_int i,typ) rets
  | general_vars_of _ rets = rets

fun goals_of_term (seen_vars:(string * typ) list) (hhf:term) : goal =
      let val (vs,hs,cl) = strip_HHF ([],[]) hhf
       in {context = {vars = filter_out (member (op =) seen_vars) vs,
                      hyps = map (pair "" o single) hs},
           goal=cl}
      end

fun goals_of (seen_vars:(string * typ) list) (goal_sequent:thm) : goal list =
  Thm.prems_of goal_sequent
    |> map (goals_of_term seen_vars)

fun top_goals_of (ctxt, goal_sequent) : goals =
  let (* val global_assms = Assumption.local_assms_of context (Local_Theory.target_of context) *)
      val local_facts = Facts.dest_static false
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
         (* |> maps (fn (name, [x]) => [(name, x)]
                      | (name, xs) => map_index (fn (i,x) =>
                          (String.concat [name, "(", string_of_int i, ")"], x)) xs) *)
      val vs = general_vars_of (Thm.prop_of goal_sequent) []
      (* val (vars, _) = Variable.constraints_of context *)
      
   in {context = {vars=vs, hyps=local_facts},
       goals = goals_of vs goal_sequent}
  end


fun string_of_term ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types false
              |> Config.put Printer.show_sorts false
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks true
              |> Config.put Printer.show_brackets false
     in Object_Logic.atomize_term ctxt'
     #> Syntax.string_of_term ctxt'
     #> REPL.trim_makrup
    end

fun string_of_type_full_sort ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types true
              |> Config.put Printer.show_sorts true
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks true
              |> Config.put Printer.show_brackets false
     in Syntax.string_of_typ ctxt'
     #> REPL.trim_makrup
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
fun uncheck_criterion ctxt = map_criterion (string_of_term ctxt)
end

local open MessagePackBinIO.Pack MessagePackBinIO.Unpack Remote_Procedure_Calling
in

fun context_packer ctxt =
  let val SOT  = string_of_term ctxt
      val SOTT = string_of_type_full_sort ctxt
   in fn {vars, hyps}:context =>
        packPair (packPairList (packString, packString o SOTT),
                  packPairList (packString, packList packString o map SOT))
                 (vars, hyps)
  end

fun goal_packer ctxt =
  let val SOT  = string_of_term ctxt
      val context_packer = context_packer ctxt
   in fn {context,goal}:goal =>
        packPair (context_packer, packString o SOT) (context,goal)
  end

fun goals_packer ctxt =
  let val goal_packer = goal_packer ctxt
      val context_packer = context_packer ctxt
   in fn {context,goals}:goals =>
        packPair (context_packer, packList goal_packer) (context,goals)
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
     | _ => raise Unpack)

fun acmd_packer (Proof_Opr {from, to, opr}) =
      packPair (packInt, packTuple3 (packString, packString, MiniLang_Agent.xcmd_packer))
               (1, (from,to,opr))
  | acmd_packer (Lookup_Fact {state, criterions}) =
      packPair (packInt, packPair (packString, packList (packList (packPair (packBool, pack_criterion)))))
               (2, (state, criterions))
  | acmd_packer Exit =
      packPair (packInt, packUnit) (0, ())

fun minilang_items_packer ctxt =
      context_packer ctxt o (fn (items:Minilang.items) => {vars = #1 items, hyps = #2 items})
fun minilang_tree_packer ctxt =
  let val term_packer = packString o string_of_term ctxt
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
      val goal_packer = goal_packer ctxt
      fun pack (Minilang.New_Items items) =
            packPair (packInt, minilang_items_packer) (0, items)
        | pack (Minilang.Goals goals) =
            packPair (packInt, packOption (packList goal_packer))
                     (1, Option.map (map (goals_of_term [])) goals)
        | pack (Minilang.Consider_Case kase) =
            packPair (packInt, packString) (2, kase)
        | pack (Minilang.Internal _) = error "BUG #adli"
   in packList pack o filter (fn Minilang.Internal _ => false | _ => true)
  end

fun bindings_packer ctxt =
  let open MessagePackBinIO.Pack
      fun pack_var_name {internal_name, external_name, typ_pretty} =
            packTuple3 (packString, packString, packString) (internal_name, external_name, typ_pretty)
      fun pack_prem_name {internal_term, external_name, pretty} =
            packTuple3 (REPL_Serialize.pack_raw_term, packString, packString)
                       (internal_term, external_name, pretty)
   in fn (var_names, prem_names) =>
        packPair (packList pack_var_name, packList pack_prem_name) (var_names, prem_names)
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
                val ctxt = Minilang.context_of s0
                val (cfg', budget) = cfg
                val full_config = (cfg', budget, counters) : MiniLang_Agent.config
                val (bindings1, s1) = MiniLang_Agent.interpret full_config opr s0
                val msgs = clean_report ()
             in states := Symtab.update (to, s1) (!states)
              ; write conn (packTuple3 (minilang_message_packer ctxt, minilang_tree_packer ctxt, bindings_packer ctxt))
                           (msgs, Minilang.print_state s1, bindings1)
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
                val SOT  = string_of_term ctxt
             in write conn (packList (packPair (pack_FactRef, packString o SOT o Thm.prop_of))) rets
            end
    ) handle EXIT => ()
           | ERR msgs => write_error' conn packUnit {message=msgs, errobj=()}
  end

val AoA_timeout = Time.fromSeconds 10
fun AoA_cmd (cfg:cfg) (states:states Unsynchronized.ref) : (goals * driver, MiniLang_Agent.xcmd list * string option) command =
  let val s0 = chk_initial_state (!states)
      val ctxt = Minilang.context_of s0
      val s0_ptree = Minilang.print_state s0
   in {
      name = "IsaMini.AoA",
      arg_schema = (fn (goals, driver) =>
          packTuple3 (goals_packer ctxt, minilang_tree_packer ctxt, packString)
                     (goals, s0_ptree, driver)),
      ret_schema = unpackPair (unpackList MiniLang_Agent.xcmd_unpacker, unpackOption unpackString),
      timeout = NONE (*SOME AoA_timeout*),
      callback = SOME (callback cfg states)
  }
  end

end

fun AoA_RPC (driver, cfg:cfg) (ctxt, sequent) =
  let val top_goals = top_goals_of (ctxt, sequent)
      val s0 = Minilang.INIT ctxt sequent
            |> Minilang.map_context ( Config.put Minilang.strict_end true
                                   #> Config.put Minilang.counter_mode "none" )
      val state = Unsynchronized.ref (Symtab.make [("$init", s0)])
      val (xcmds, s1o) =
            Remote_Procedure_Calling.call_command (AoA_cmd cfg state) (top_goals, driver)
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
  else AoA_RPC (default_driver, MiniLang_Agent.default_cfg) (ctxt, sequent)
    |> (fn (_, sequent') => SOME (Seq.Result (ctxt, sequent'), Seq.empty)) )


end
