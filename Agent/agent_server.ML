(*TODO: name anounymous hyps ""*)

signature MINILANG_AGENT_AoA = sig

type state_id = string
type states = Minilang.state Symtab.table

datatype acmd = Proof_Opr of {from: state_id, to: state_id, opr: MiniLang_Agent.xcmd}
              | Exit

val AoA_RPC : MiniLang_Agent.cfg * MiniLang_Agent.budget
           -> Proof.state
           -> MiniLang_Agent.xcmd list
end

structure MiniLang_Agent_AoA : MINILANG_AGENT_AoA = struct

type state_id = string
type states = Minilang.state Symtab.table
type cfg = MiniLang_Agent.cfg * MiniLang_Agent.budget

datatype acmd = Proof_Opr of {from: state_id, to: state_id, opr: MiniLang_Agent.xcmd}
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

fun top_goals_of (s:Proof.state) : goals =
  let val {goal=goal_sequent, ...} = Proof.goal s
   (* val global_assms = Assumption.local_assms_of context (Local_Theory.target_of context) *)
      val local_facts = Facts.dest_static false [(Proof_Context.facts_of (Local_Theory.target_of \<^context>))]
                            (Proof_Context.facts_of \<^context>)
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

val acmd_unpacker =
  unpackPair_dep' unpackInt (
    fn 1 => unpackTuple3 (unpackString, unpackString, MiniLang_Agent.xcmd_unpacker)
         #> apfst (fn (f,t,opr) => Proof_Opr {from=f, to=t, opr=opr})
     | 0 => unpackUnit
         #> apfst (K Exit)
     | _ => raise Unpack)

fun acmd_packer (Proof_Opr {from, to, opr}) =
      packPair (packInt, packTuple3 (packString, packString, MiniLang_Agent.xcmd_packer))
               (1, (from,to,opr))
  | acmd_packer Exit =
      packPair (packInt, packUnit) (0, ())

fun minilang_items_packer ctxt =
      context_packer ctxt o (fn (items:Minilang.items) => {vars = #1 items, hyps = #2 items})
fun minilang_tree_packer ctxt =
  let val term_packer = packString o string_of_term ctxt
      val item_packer = minilang_items_packer ctxt
      fun pack (Minilang.PROP (items, goal)) =
            packTuple3 (packInt, item_packer, term_packer) (0, items, goal)
        | pack (Minilang.BUNDL (items, trees)) =
            packTuple3 (packInt, item_packer, packList pack) (1, items, trees)
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

fun callback (cfg:cfg) (states:states Unsynchronized.ref) (conn:connection) =
  let exception EXIT
      exception ERR of string list
      val messages = Unsynchronized.ref []
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
         | Proof_Opr {from, to, opr} =>
            let val s0 = case Symtab.lookup (!states) from
                           of SOME s => s
                            | NONE => raise ERR ["beginning_state_not_found"]
                val ctxt = Minilang.context_of s0
                val s1 = MiniLang_Agent.interpret cfg opr s0
                val msgs = clean_report ()
             in states := Symtab.update (to, s1) (!states)
              ; write conn (packPair (minilang_message_packer ctxt, minilang_tree_packer ctxt))
                           (msgs, Minilang.print_state s1)
            end
    ) handle EXIT => ()
           | ERR msgs => write_error' conn packUnit {message=msgs, errobj=()}
  end

val AoA_timeout = Time.fromSeconds 10
fun AoA_cmd (cfg:cfg) (states:states Unsynchronized.ref) : (goals, MiniLang_Agent.xcmd list) command =
  let val s0 = chk_initial_state (!states)
      val ctxt = Minilang.context_of s0
      val s0_ptree = Minilang.print_state s0
   in {
      name = "IsaMini.AoA",
      arg_schema = (fn goals => packPair (goals_packer ctxt, minilang_tree_packer ctxt) (goals, s0_ptree)),
      ret_schema = unpackList MiniLang_Agent.xcmd_unpacker,
      timeout = SOME AoA_timeout,
      callback = SOME (callback cfg states)
  }
  end

end

fun AoA_RPC (cfg:cfg) (s : Proof.state) =
  let val top_goals = top_goals_of s
      val s0 = Minilang.INIT' s
      val state = Unsynchronized.ref (Symtab.make [("$init", s0)])
   in Remote_Procedure_Calling.call_command (AoA_cmd cfg state) top_goals
  end

end
