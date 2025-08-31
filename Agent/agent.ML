signature MINILANG_AGENT = sig

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
  | OBTAIN   of string list (*vars*) * string list (*constraints*)
  | ROLLBACK of int

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command

val check_command : Proof.context -> xcmd -> icmd

val interpret' : icmd -> Minilang.state -> (unit -> string list) option * Minilang.state
val interpret'' : xcmd -> Minilang.state -> (unit -> string list) option * Minilang.state
val replay_proof : xcmd list -> Minilang.state -> Minilang.state

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
val init : context_state -> state
val conclude : Proof.context -> state -> thm

val proof_of : state -> xcmd list

val interpret : xcmd -> state -> (unit -> string list) * state

end

structure MiniLang_Agent : MINILANG_AGENT = struct

val QUERY_RET_LIMIT = SOME 20

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
  | OBTAIN   of string list (*vars*) * string list (*constraints*)
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

val string_of_term = REPL.trim_makrup oo Syntax.string_of_term
val string_of_thm  = REPL.trim_makrup oo Thm.string_of_thm
val string_of_typ  = REPL.trim_makrup oo Syntax.string_of_typ

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
  | check_command ctxt (HAVE goals) = HAVE (Syntax.read_terms ctxt goals)
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

fun interpret' (RETRIEVE (patterns, neg_pats, names)) (s:Minilang.state) =
      let open Find_Theorems
          val ctxt = Minilang.context_of s
          val _ = if null patterns andalso null neg_pats andalso null names
                  then error ("You must specifiy at least one pattern or one sub-name used to retrieve the facts")
                  else ()

          val criteria =
              map (fn tm => (true , Pattern tm)) patterns
            @ map (fn tm => (false, Pattern tm)) neg_pats
            @ map (fn tm => (true , Name tm)) names
          val (SOME num, thms) = Find_Theorems.find_theorems ctxt NONE QUERY_RET_LIMIT true criteria

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
                            "- \<open>" ^ REPL.trim_makrup tm ^ "\<close>" ) thms
       in (SOME print, s)
      end
  | interpret' (SIMPLIFY simp_thms) s = (
      (NONE, Minilang.SIMP'' (map (pair true) simp_thms) s)
      handle Minilang.OPR_FAIL (PROOF_FAIL, _) =>
        raise Minilang.OPR_FAIL (PROOF_FAIL,
            "Cannot further simplify the goal. You should either apply other operation (e.g., ATP)\
            \ or supply more simplification rules if you believe you should apply SIMPLIFY.") )
  | interpret' (UNFOLD origin_consts) s =
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
                            \You may use RETRIEVE command to look for the definition and apply SIMPIFY to unfold."])
                  |  _  => error (String.concat [
                            "The definitions of ", String.concatWith ", " not_found, " are not found.\n\
                            \You may use RETRIEVE command to look for the definitions and apply SIMPIFY to unfold."]))
       in (print, Minilang.UNFOLD (flat (map_filter I defs)) s)
      end
  | interpret' (WITNESS terms) s = (NONE, Minilang.CHOOSE terms s)
  | interpret' (RULE thms) s = (NONE, Minilang.RULE thms [] s)
  | interpret' (CASE_SPLIT (target, rule)) s =
      (NONE, Minilang.CASE_SPLIT (false, ([[SOME target]], rule)) NONE [] s)
  | interpret' (INDUCT (target, arbitrary, rule)) s =
      let val ctxt = Minilang.context_of s
          val vs = map (fn Free nt => nt
                         | x => error ("The `arbitrary` argument must be variables, but (" ^
                                       string_of_term ctxt x ^ ") is given.")) arbitrary
       in (NONE, Minilang.INDUCT
              (false, ([[SOME (NONE, (target, false))]], (([vs], []), Option.map single rule))) NONE [] s)
      end
  | interpret' (ATP lemmas) s =
      (NONE, Minilang.END_or_NXT NONE {add=lemmas,del=[],only=false} s)
  | interpret' (BRANCH branches) s =
      let val brs = map (fn br => ([], ([], [], [(Binding.empty_atts, [(br, [])])]))) branches
       in (NONE, Minilang.CONSIDER brs s)
      end
  | interpret' (HAVE goals) s =
      (NONE, Minilang.HAVE'' [] [] (map (fn goal => (Binding.empty_atts, [(goal, [])])) goals) s)
  | interpret' (OBTAIN (vars,constraints)) s =
      let val arg = [([], (map (fn v => (Binding.name v, NONE, NoSyn)) vars, [],
                           map (fn goal => (Binding.empty_atts, [(goal, [])])) constraints))]
       in (NONE, Minilang.CONSIDER arg s)
      end
  | interpret' (ROLLBACK _) _ =
      error "Cannot rollback in interpret'"

fun interpret'' xcmd s =
  let val ctxt = Minilang.context_of s
      val icmd = check_command ctxt xcmd
   in interpret' icmd s
  end

val replay_proof = fold (snd oo interpret'')

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

fun init (ctxt, sequent) =
  let val ctxt = ctxt
            |> Config.put Minilang.transparent_intro true
            |> Config.put Minilang.high_auto_mode true
      val s = (Minilang.INIT ctxt sequent, {accumulative=[], effective=[]})
      val msgs = Unsynchronized.ref []
      fun reporter msg = msgs := msg :: !msgs
   in Minilang.set_reporter reporter
    ; (s, Inttab.update_new (0, s) Inttab.empty, msgs)
  end

fun conclude initial_ctxt ((s,_),_,_) = Minilang.conclude initial_ctxt s

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

fun interpret (ROLLBACK i) ((_, {accumulative, ...}), history, msgs) =
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
  | interpret (xcmd as RETRIEVE _) (s, history, msgs) =
     let val (SOME p, _) = interpret'' xcmd (#1 s)
      in (p, (s, history, msgs))
     end
  | interpret xcmd ((s, {accumulative, effective}), history, msgs) =
     let val i = Inttab.size history
         val ctxt = Minilang.context_of s
         val (p, s') = interpret'' xcmd s

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

end