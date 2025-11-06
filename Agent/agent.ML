signature MINILANG_AGENT = sig

type budget = {
      QUERY_RET_LIMIT: int option,
      parallel_runs: int,
      total_timeout: Time.time option,
      step_limit: int
  }

type cfg = {
      auto_end : bool,
      gussing_num_typ : bool
  }

val default_cfg : cfg

datatype ('term, 'thm, 'fact) command =
    RETRIEVE of 'term list (*patterns*)
              * 'term list (*negative patterns*)
              * string list (*names*)
  | SIMPLIFY of 'fact list (*simp rules*)
  | UNFOLD   of string list
  | WITNESS  of 'term list
  | RULE     of 'fact list
  | CASE_SPLIT of 'term (*target*) * 'thm option (*rule*)
  | INDUCT   of 'term (*target*) * 'term list (*arbitrary*) * 'thm option (*rule*)
  | ATP      of 'fact list (*add lemmas*)
  | BRANCH   of string list
  | HAVE     of 'term list
  | OBTAIN   of (string * string option) list (*vars*) * string list (*constraints*)
  | ROLLBACK of int

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command

val check_command : Proof.context -> xcmd -> icmd

val interpret' : cfg * budget -> icmd -> Minilang.state -> (unit -> string list) option * Minilang.state
val interpret'' : cfg * budget -> xcmd -> Minilang.state -> (unit -> string list) option * Minilang.state
val replay_proof : cfg * budget -> xcmd list -> Minilang.state -> Minilang.state

type opr_records = {
    accumulative: xcmd list,
    effective: xcmd list
  }
type state = (Minilang.state * opr_records)
           * (Minilang.state * opr_records) Inttab.table
           * Minilang.message list Unsynchronized.ref

val step_of : state -> int
val context_of : state -> Proof.context

val print_goal' : int -> Minilang.state -> string list
val print_goal  : state -> string list
val is_finished : state -> bool
val init : cfg -> context_state -> state
val conclude : Proof.context -> state -> thm
val effective_cmds : state -> xcmd list

val proof_of : state -> xcmd list

val interpret : cfg * budget -> xcmd -> state -> (unit -> string list) * state
val run : cfg * budget -> xcmd list -> context_state -> thm

(* Driver *)

type driver = string
val register_driver : string -> cfg -> unit
val cfg_of_driver : driver -> cfg

end

structure MiniLang_Agent : MINILANG_AGENT = struct

(* ready_to_finish *)
type budget = {
      QUERY_RET_LIMIT: int option,
      parallel_runs: int,
      total_timeout: Time.time option,
      step_limit: int
  }

type cfg = {
      auto_end : bool,
      gussing_num_typ : bool
  }

val default_cfg = {
      auto_end = true,
      gussing_num_typ = true
  }

type driver = string

val driver_cfg = Synchronized.var "driver_cfg" Symtab.empty
               : cfg Symtab.table Synchronized.var

fun register_driver name cfg =
  Synchronized.change driver_cfg (Symtab.update_new (name, cfg))

fun cfg_of_driver driver =
      Symtab.lookup (Synchronized.value driver_cfg) driver
        |> the_default default_cfg

datatype ('term, 'thm, 'fact) command =
    RETRIEVE of 'term list (*patterns*)
              * 'term list (*negative patterns*)
              * string list (*names*)
  | SIMPLIFY of 'fact list (*simp rules*)
  | UNFOLD   of string list
  | WITNESS  of 'term list
  | RULE     of 'fact list
  | CASE_SPLIT of 'term (*target*) * 'thm option (*rule*)
  | INDUCT   of 'term (*target*) * 'term list (*arbitrary*) * 'thm option (*rule*)
  | ATP      of 'fact list (*add lemmas*)
  | BRANCH   of string list
  | HAVE     of 'term list
  | OBTAIN   of (string * string option) list (*vars*) * string list (*constraints*)
  | ROLLBACK of int

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command

type opr_records = {
    accumulative: xcmd list,
    effective: xcmd list
  }

type state = (Minilang.state * opr_records)
           * (Minilang.state * opr_records) Inttab.table
           * Minilang.message list Unsynchronized.ref

val printing_cfg = {all_typ=false, bv_typ=true, constant_typ=false, free_typ=false, num_typ=true, sorting=false}
val string_of_term = REPL.print_term printing_cfg
fun string_of_thm ctxt th = string_of_term ctxt (Thm.prop_of th)
val string_of_typ  = REPL.print_typ printing_cfg

val keywords = Thy_Header.get_keywords @{theory Pure}
fun read_fact src =
  let val symbols = Input.source_explode (Input.string src)
      val toks = Token.tokenize keywords {strict = true} symbols
              |> filter Token.is_proper
   in case Scan.read Token.stopper Parse.thm toks
        of SOME fact => fact
         | NONE => error ("Cannot parse \"" ^ src ^ "\" as a fact reference")
  end

fun read_thms ctxt src =
  let val fact = read_fact src
   in Attrib.eval_thms ctxt [fact]
  end

fun read_terms_w_var ctxt terms =
  let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
      val terms' = Syntax.read_terms ctxt terms
      val ctxt' = fold Proof_Context.augment terms' ctxt
   in Variable.export_terms ctxt' (Proof_Context.init_global (Proof_Context.theory_of ctxt)) terms'
  end

local fun chk_single _ _ [x] = x
        | chk_single ctxt rule lst = error ("Expect exact one rule but \"" ^ the rule
              ^ "\" refers to the following facts:\n"
              ^ String.concat (map (fn th => "- " ^ string_of_thm ctxt th ^ "\n") lst)
              ^ "You may select the i-th rule by using \"" ^ the rule ^ "(i)\".")
in
fun check_command ctxt (RETRIEVE (patterns, neg_pats, names)) =
      let val terms' = read_terms_w_var ctxt (patterns @ neg_pats)
          val (patterns', neg_pats') = chop (length patterns) terms'
       in RETRIEVE (patterns', neg_pats', names)
      end
  | check_command _ (SIMPLIFY facts) = SIMPLIFY (map read_fact facts)
  | check_command _ (RULE facts) = RULE (map read_fact facts)
  | check_command _ (UNFOLD consts) = UNFOLD consts
  | check_command ctxt (WITNESS terms) = WITNESS (Syntax.read_terms ctxt terms)
  | check_command ctxt (CASE_SPLIT (target, rule)) =
      let val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
          val target' = Syntax.read_term ctxt target
       in CASE_SPLIT (target', rule')
      end
  | check_command ctxt (INDUCT (target, arbitrary, rule)) =
      let val (target' :: arbitrary') = Syntax.read_terms ctxt (target :: arbitrary)
          val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
       in INDUCT (target', arbitrary', rule')
      end
  | check_command _ (ATP facts) = ATP (map read_fact facts)
  | check_command _ (BRANCH brs) = BRANCH brs
  | check_command ctxt (HAVE goals) = HAVE (Syntax.read_props ctxt goals)
  | check_command _ (OBTAIN vc) = OBTAIN vc
  | check_command _ (ROLLBACK i) = ROLLBACK i
end

fun find_def ctxt name =
  let fun mkname suffix [th] =
               [(Facts.Named ((name ^ suffix, Position.none), NONE), th)]
        | mkname suffix ths  = map_index (fn (i,th) =>
                (Facts.Named ((name ^ "(" ^ string_of_int i ^ ")" ^ suffix, Position.none), NONE), th)) ths
   in case Proof_Context.lookup_fact ctxt (name ^ ".simps")
   of SOME facts => SOME (mkname ".simps" (#thms facts))
    | NONE => (
      case Proof_Context.lookup_fact ctxt (name ^ "_def")
   of SOME facts => SOME (mkname "_def" (#thms facts))
    | NONE => NONE )
  end

fun find_def_const ctxt (Const (name, _)) = find_def ctxt name
  | find_def_const _ _ = NONE

fun interpret' cfg (RETRIEVE (patterns, neg_pats, names)) (s:Minilang.state) =
      let open Find_Theorems
          val ctxt = Minilang.context_of s
          val _ = if null patterns andalso null neg_pats andalso null names
                  then error ("You must specifiy at least one pattern or one sub-name used to retrieve the facts")
                  else ()

          val criteria =
              map (fn tm => (true , Pattern tm)) patterns
            @ map (fn tm => (false, Pattern tm)) neg_pats
            @ map (fn tm => (true , Name tm)) names
          val (SOME num, thms) =
                  Find_Theorems.find_theorems ctxt NONE (#QUERY_RET_LIMIT (snd cfg))
                                              true criteria

          fun augment_def const =
              case find_def_const ctxt const
                of SOME defs => (num + length defs, defs @ thms)
                 | NONE => (num, thms)
          val (num, thms) =
              case (patterns, neg_pats, names)
                of ([tm], _, _) => augment_def tm
                 | _ => (num, thms)

          fun print_iv [Facts.Single i] = "(" ^ string_of_int i ^ ")"
            | print_iv _ = ""
          fun print_name ((name,_), NONE) = name
            | print_name ((name,_), SOME iv) = name ^ print_iv iv
            
          fun print () =
                (if num > length thms
                 then [string_of_int num, " facts matches. The frist ", string_of_int (length thms),
                       " facts are retrieved:\n"]
                 else ["Retrieved ", string_of_int num, " facts:\n"])
              @ map (fn (Facts.Named named, th) =>
                            "- " ^ print_name named ^ ": " ^ string_of_thm ctxt th ^ "\n"
                      | (Facts.Fact tm, _) =>
                            "- \<open>" ^ REPL.trim_makrup tm ^ "\<close>\n" ) thms
       in (SOME print, s)
      end
  | interpret' cfg (SIMPLIFY simp_thms) s = (
      (NONE, Minilang.SIMP'' (map (pair true) simp_thms) s)
      handle Minilang.OPR_FAIL (PROOF_FAIL, _) =>
        raise Minilang.OPR_FAIL (PROOF_FAIL,
            "Cannot further simplify the goal. You should either apply other operation (e.g., ATP)\
            \ or supply more simplification rules if you believe you should apply SIMPLIFY.\n") )
  | interpret' cfg (UNFOLD origin_consts) s =
      let val _ = if null origin_consts
                  then error "You must specify at least one target to unfold"
                  else ()
          val ctxt = Minilang.context_of s
          val consts = map (Syntax.read_term ctxt) origin_consts
          val defs = map (Option.map (map snd) o find_def_const ctxt) consts
          val not_found = map_filter (fn (NONE, tm) => SOME tm
                                       | _ => NONE
                                     ) (defs ~~ origin_consts)
          val print =
            if null not_found
            then NONE
            else SOME (fn () =>
               case not_found
                 of [x] => error (String.concat [
                            "The definition of ", x, " is not found.\n\
                            \You may use RETRIEVE command to look for the definition and apply SIMPIFY to unfold.\n"])
                  |  _  => error (String.concat [
                            "The definitions of ", String.concatWith ", " not_found, " are not found.\n\
                            \You may use RETRIEVE command to look for the definitions and apply SIMPIFY to unfold.\n"]))
       in (print, Minilang.UNFOLD (flat (map_filter I defs)) s)
      end
  | interpret' cfg (WITNESS terms) s = (NONE, Minilang.CHOOSE terms s)
  | interpret' cfg (RULE thms) s = (NONE, Minilang.RULE thms [] s)
  | interpret' cfg (CASE_SPLIT (target, rule)) s =
      (NONE, Minilang.CASE_SPLIT (false, ([[SOME target]], rule)) NONE [] s)
  | interpret' cfg (INDUCT (target, arbitrary, rule)) s =
      let val ctxt = Minilang.context_of s
          val vs = map (fn Free nt => nt
                         | x => error ("The `arbitrary` argument must be variables, but (" ^
                                       string_of_term ctxt x ^ ") is given.")) arbitrary
       in (NONE, Minilang.INDUCT
              (false, ([[SOME (NONE, (target, false))]], (([vs], []), Option.map single rule))) NONE [] s)
      end
  | interpret' cfg (ATP lemmas) s =
      (NONE, Minilang.END_or_NXT NONE {add=lemmas,del=[],only=false} s)
  | interpret' cfg (BRANCH branches) s =
      let val brs = map (fn br => ([], ([], [], [(Binding.empty_atts, [(br, [])])]))) branches
       in (NONE, Minilang.CONSIDER brs s)
      end
  | interpret' cfg (HAVE goals) s =
      (NONE, Minilang.HAVE'' [] [] (map (fn goal => (Binding.empty_atts, [(goal, [])])) goals) s)
  | interpret' cfg (OBTAIN (vars,constraints)) s =
      let val arg = [(map (fn (v,T) => (Binding.name v, T, NoSyn)) vars,
                     ([], [], map (fn goal => (Binding.empty_atts, [(goal, [])])) constraints))]
       in (NONE, Minilang.CONSIDER arg s)
      end
  | interpret' cfg (ROLLBACK _) _ =
      error "Cannot rollback in interpret'"

val join_output = join_options (fn (f,g) => fn () => f () @ "\n" :: g ())

fun interpret'' cfg xcmd s =
  let val ctxt = Minilang.context_of s
      val icmd = check_command ctxt xcmd
      val (output, s') = interpret' cfg icmd s
      val (output, s') =
            if Minilang.ready_to_finish s'
            then let val (output', s'') = interpret' cfg (ATP []) s'
                  in (join_output (output, output'), s'')
                 end
            else (output, s')
   in (output, s')
  end

fun replay_proof cfg = fold (snd oo interpret'' cfg)

fun step_of (_, history, _) = Inttab.size history
fun context_of ((s,_), _, _) = Minilang.context_of s

fun print_goal' step s =
  if Minilang.is_finished s
  then ["All subgoals are proven. Congratulations!\n"]
  else let
      val ctxt = Minilang.context_of s
      val ((frees, facts), goal) = Minilang.print_state s
                            (* |> Minilang.atomize_tree ctxt *)
                               |> Minilang.context_of_leading_goal
      val tfrees = fold (Term.add_tfreesT o snd) frees []
   in "### STEP " :: string_of_int step :: "\n"
   :: (if step = 0
       then "This is the proof goal you need to prove.\n"
       else "Now you need to prove the following subgoal.\n" )
   :: "TYPE VARIABLES:"
   :: (if null tfrees then " empty" else "") :: "\n"
   :: maps (fn (name, sort) =>
        ["- ", name, " : ", String.concatWith ", " sort, "\n"] ) tfrees
    @ "VARIABLES:"
   :: (if null frees then " empty" else "") :: "\n"
   :: maps (fn (name, ty) =>
        ["- ", name, " : ", string_of_typ ctxt ty, "\n"] ) frees
    @ "LOCAL FACTS:"
   :: (if null facts then " empty" else "") :: "\n"
   :: maps (
        fn (name, [tm]) =>
            ["- ", name, ": ", string_of_term ctxt tm, "\n"]
         | (name, tms) =>
            flat (map_index (fn (i, tm) =>
              ["- ", name, "(", string_of_int i, "): ", string_of_term ctxt tm, "\n"]) tms)
        ) facts
    @ ["GOAL: ", string_of_term ctxt goal, "\n"]
  end

fun print_goal s = print_goal' (step_of s - 1) (#1 (#1 s))
fun is_finished ((s,_), _, _) = Minilang.is_finished s

fun init cfg (ctxt, sequent) =
  let val default_num_typ = Minilang_Helper.guess_default_num_typ (Thm.prop_of sequent)
      val ctxt = ctxt
            |> Config.put Minilang.transparent_intro true
            |> Config.put Minilang.high_auto_mode true
            |> Context.proof_map (Default_Num_Typ.set default_num_typ)
            (* |> Config.put Minilang.auto_end_mode true *)
      val s = (Minilang.INIT ctxt sequent, {accumulative=[], effective=[]})
      val msgs = Unsynchronized.ref []
      fun reporter msg = msgs := msg :: !msgs
   in Minilang.set_reporter reporter
    ; (s, Inttab.update_new (0, s) Inttab.empty, msgs)
  end

fun conclude initial_ctxt ((s,_),_,_) = Minilang.conclude initial_ctxt s
fun effective_cmds ((_,{effective,...}),_,_) = rev effective

fun proof_of ((_, {effective, ...}),_,_) = effective

fun success_print (RETRIEVE _) = (fn () => [])
  | success_print (SIMPLIFY _) = (fn () => ["Operation SIMPLIFY succeeds.\n"])
  | success_print (UNFOLD   _) = (fn () => ["Operation UNFOLD succeeds.\n"])
  | success_print (WITNESS  _) = (fn () => ["Operation WITNESS succeeds.\n"])
  | success_print (RULE     _) = (fn () => ["Operation RULE succeeds.\n"])
  | success_print (CASE_SPLIT _) = (fn () => ["Operation CASE_SPLIT succeeds.\n"])
  | success_print (INDUCT   _) = (fn () => ["Operation INDUCT succeeds.\n"])
  | success_print (ATP      _) = (fn () => ["Operation ATP succeeds.\n"])
  | success_print (BRANCH   _) = (fn () => ["Operation BRANCH succeeds.\n"])
  | success_print (HAVE     _) = (fn () => ["Operation HAVE succeeds.\n"])
  | success_print (OBTAIN   _) = (fn () => ["Operation OBTAIN succeeds.\n"])
  | success_print (ROLLBACK i) = (fn () =>
      ["Succefully rollback to step " ^ string_of_int i ^ ".\n"])

fun interpret cfg (ROLLBACK i) ((_, {accumulative, ...}), history, msgs) =
     (case Inttab.lookup history i
        of SOME (s', {effective, ...}) =>
              ( success_print (ROLLBACK i),
                ((s', { accumulative = ROLLBACK i :: accumulative,
                        effective = effective }),
                 history,
                 msgs) )
         | NONE =>
              error (String.concat
                  ["The proof has not yet reached step ", string_of_int i,
                   "; cannot rollback to step ", string_of_int i]))
  | interpret cfg (xcmd as RETRIEVE _) (s, history, msgs) =
     let val (SOME p, _) = interpret'' cfg xcmd (#1 s)
      in (p, (s, history, msgs))
     end
  | interpret cfg xcmd ((s, {accumulative, effective}), history, msgs) =
     let val i = Inttab.size history
         val ctxt = Minilang.context_of s
         val (p, s') = interpret'' cfg xcmd s

         val records' = {
              accumulative = xcmd :: accumulative,
              effective = xcmd :: effective
           }
         val state' = (s', records')

         val the_msgs = !msgs
         val _ = msgs := []

         val state' = (state', Inttab.update_new (i, state') history, msgs)

         fun print () =
            let val p = case p of SOME p => p | NONE => success_print xcmd
                val ret = p ()
                fun prt_msg (Minilang.Goals (SOME goals)) =
                      if length goals <= 1
                      then []
                      else "The operation derives " :: string_of_int (length goals)
                        :: " subgoals:\n"
                        :: maps (fn goal => ["- " ^ string_of_term ctxt goal ^ "\n"] ) goals
                         @ ["\n"]
                  | prt_msg _ = []
                val msg_ret = maps prt_msg the_msgs
             in ret
              @ "\n" :: msg_ret
              @ print_goal state'
            end

      in (print, state')
     end

fun run (cfg, budget) cmds state =
  let val may_time_out =
        case #total_timeout budget
          of SOME t => Timeout.apply t
           | NONE => I
      val s' = may_time_out (fold (fn cmd => snd o interpret (cfg, budget) cmd) cmds o init cfg) state
   in conclude (fst state) s'
  end


val _ = register_driver "Gemini" {
            auto_end = true,
            gussing_num_typ = false
        }

end