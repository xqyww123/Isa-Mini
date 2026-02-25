signature MINILANG_AGENT = sig

type budget = {
      QUERY_RET_LIMIT: int option,
      parallel_runs: int,
      total_timeout: Time.time option,
      step_limit: int
  }

type cfg = {
      drafting: bool,
      gussing_num_typ : bool
  }

datatype ('term, 'thm, 'fact) command =
    SIMPLIFY of 'fact list (*simp rules*)
  | UNFOLD   of string list
  | WITNESS  of 'term list
  | RULE     of 'fact list
  | CASE_SPLIT of 'term (*target*) * 'thm option (*rule*)
  | INDUCT   of 'term (*target*) * 'term list (*arbitrary*) * 'thm option (*rule*)
  | NEXT_OR_END of 'fact list (*add lemmas*) * Minilang.opt_var_names
  | NEXT     of 'fact list (*add lemmas*) * Minilang.opt_var_names
  | END      of 'fact list (*add lemmas*)
  | BRANCH   of string list
  | HAVE     of 'term list
  | OBTAIN   of (string * string option) list (*vars*) * string list (*constraints*)
  | SORRY    of Minilang.opt_var_names
  | HAMMER   of 'fact list (*add lemmas*)
  | SKIP

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command
type var_names = {internal_name: string, external_name: string} list
type prem_names = {internal_term: term, external_name: string} list
type counters = {
    prem_counter: int Synchronized.var,
    fact_counter: int Synchronized.var
  }
type config = cfg * budget * counters

val check_command : Proof.context -> xcmd -> icmd
val interpret_i : config -> icmd * opt_var_names * opt_prem_names -> Minilang.state -> Minilang.state
val interpret : config -> xcmd * opt_var_names * opt_prem_names -> Minilang.state -> Minilang.state

val default_cfg : cfg * budget

end

structure MiniLang_Agent : MINILANG_AGENT = struct

type budget = {
      QUERY_RET_LIMIT: int option,
      parallel_runs: int,
      total_timeout: Time.time option,
      step_limit: int
  }

type cfg = {
      drafting: bool,
      gussing_num_typ : bool
  }

val default_cfg : (cfg * budget) = ({
      drafting = true,
      gussing_num_typ = true
    }, {
      QUERY_RET_LIMIT = SOME 30,
      parallel_runs = 1,
      total_timeout = SOME (Time.fromSeconds 600),
      step_limit = 30
    })

type var_names = {internal_name: string, external_name: string} list
type prem_names = {internal_name: string, external_name: string} list

type counters = {
    prem_counter: int Synchronized.var,
    fact_counter: int Synchronized.var
  }
type config = cfg * budget * counters

datatype ('term, 'thm, 'fact) command =
    SIMPLIFY of 'fact list (*simp rules*)
  | UNFOLD   of string list
  | WITNESS  of 'term list
  | RULE     of 'fact list
  | CASE_SPLIT of 'term (*target*) * 'thm option (*rule*)
  | INDUCT   of 'term (*target*) * 'term list (*arbitrary*) * 'thm option (*rule*)
  | NEXT_OR_END of 'fact list (*add lemmas*) * Minilang.opt_var_names
  | NEXT     of 'fact list (*add lemmas*) * Minilang.opt_var_names
  | END      of 'fact list (*add lemmas*)
  | BRANCH   of string list
  | HAVE     of 'term list
  | OBTAIN   of (string * string option) list (*vars*) * string list (*constraints*)
  | SORRY    of Minilang.opt_var_names
  | HAMMER   of 'fact list (*add lemmas*)
  | SKIP

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command

val string_of_term = Syntax.string_of_term
fun string_of_thm ctxt th = string_of_term ctxt (Thm.prop_of th)

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

fun AUTO_INTRO (counters:counters)
               (opt_var_names: var_names option, opt_prem_names: prem_names option)
               (s:Minilang.state)
  = ...

fun interpret_i _ (SIMPLIFY simp_thms) s =
      Minilang.SIMP'' (map (pair true) simp_thms) s
  | interpret_i _ (UNFOLD origin_consts) s =
      let val _ = if null origin_consts
                  then error "You must specify at least one target to unfold"
                  else ()
          val ctxt = Minilang.context_of s
          val consts = map (Syntax.read_term ctxt) origin_consts
          val defs = map (Option.map (map snd) o find_def_const ctxt) consts
       (* val not_found = map_filter (fn (NONE, tm) => SOME tm
                                       | _ => NONE
                                     ) (defs ~~ origin_consts) *)
       in Minilang.UNFOLD (flat (map_filter I defs)) s
      end
  | interpret_i _ (WITNESS terms) s = Minilang.CHOOSE terms s
  | interpret_i _ (RULE thms) s = Minilang.RULE thms [] s
  | interpret_i _ (CASE_SPLIT (target, rule)) s =
      Minilang.CASE_SPLIT (false, ([[SOME target]], rule)) NONE [] s
  | interpret_i _ (INDUCT (target, arbitrary, rule)) s =
      let val ctxt = Minilang.context_of s
          val vs = map (fn Free nt => nt
                         | x => error ("The `arbitrary` argument must be variables, but (" ^
                                       string_of_term ctxt x ^ ") is given.")) arbitrary
       in Minilang.INDUCT
              (false, ([[SOME (NONE, (target, false))]], (([vs], []), Option.map single rule))) NONE [] s
      end
  | interpret_i _ (NEXT_OR_END (lemmas, vars)) s =
      Minilang.END_or_NXT vars {add=lemmas,del=[],only=false} s
  | interpret_i _ (NEXT (lemmas, vars)) s =
      Minilang.NXT vars {add=lemmas,del=[],only=false} s
  | interpret_i _ (END lemmas) s =
      Minilang.END {add=lemmas,del=[],only=false} s
  | interpret_i _ (BRANCH branches) s =
      let val brs = map (fn br => ([], ([], [], [(Binding.empty_atts, [(br, [])])]))) branches
       in Minilang.CONSIDER brs s
      end
  | interpret_i _ (HAVE goals) s =
      Minilang.HAVE'' [] [] (map (fn goal => (Binding.empty_atts, [(goal, [])])) goals) s
  | interpret_i _ (OBTAIN (vars,constraints)) s =
      let val arg = [(map (fn (v,T) => (Binding.name v, T, NoSyn)) vars,
                     ([], [], map (fn goal => (Binding.empty_atts, [(goal, [])])) constraints))]
       in Minilang.CONSIDER arg s
      end
  | interpret_i _ (SORRY vars) s =
      let
       in Minilang.END_or_NXT_by_SORRY vars s
      end
  | interpret_i _ (HAMMER lemmas) s =
      Minilang.HAMMER {add=lemmas,del=[],only=false} s
  | interpret_i _ SKIP s = s

local 
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

fun chk_single _ _ [x] = x
  | chk_single ctxt rule lst = error ("Expect exact one rule but \"" ^ the rule
        ^ "\" refers to the following facts:\n"
        ^ String.concat (map (fn th => "- " ^ string_of_thm ctxt th ^ "\n") lst)
        ^ "You may select the i-th rule by using \"" ^ the rule ^ "(i)\".")
in
fun check_command_i _ (SIMPLIFY facts) = SIMPLIFY (map read_fact facts)
  | check_command_i _ (RULE facts) = RULE (map read_fact facts)
  | check_command_i _ (UNFOLD consts) = UNFOLD consts
  | check_command_i ctxt (WITNESS terms) = WITNESS (Syntax.read_terms ctxt terms)
  | check_command_i ctxt (CASE_SPLIT (target, rule)) =
      let val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
          val target' = Syntax.read_term ctxt target
       in CASE_SPLIT (target', rule')
      end
  | check_command_i ctxt (INDUCT (target, arbitrary, rule)) =
      let val (target' :: arbitrary') = Syntax.read_terms ctxt (target :: arbitrary)
          val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
       in INDUCT (target', arbitrary', rule')
      end
  | check_command_i _ (NEXT_OR_END (facts, vars)) = NEXT_OR_END (map read_fact facts, vars)
  | check_command_i _ (NEXT (facts, vars)) = NEXT (map read_fact facts, vars)
  | check_command_i _ (END facts) = END (map read_fact facts)
  | check_command_i _ (HAMMER facts) = HAMMER (map read_fact facts)
  | check_command_i _ (BRANCH brs) = BRANCH brs
  | check_command_i ctxt (HAVE goals) = HAVE (Syntax.read_props ctxt goals)
  | check_command_i _ (OBTAIN vc) = OBTAIN vc
  | check_command_i _ (SORRY vars) = SORRY vars
  | check_command_i _ SKIP = SKIP

fun check_command ctxt x = check_command_i ctxt x
    handle ERROR msg => raise Minilang.OPR_FAIL (Minilang.TERMLANG, msg)

end

fun interpret cfg xcmd state =
  let val icmd = check_command (Minilang.context_of state) xcmd
   in interpret_i cfg icmd state
  end


end

