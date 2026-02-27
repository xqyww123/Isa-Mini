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

type var_name = {internal_name: string, external_name: string, typ_pretty: string}
type prem_name = {internal_term: term, external_name: string, pretty: string}
type bindings = var_name list * prem_name list

datatype ('term, 'thm, 'fact) command =
    SIMPLIFY of 'fact list (*simp rules*) * bindings
  | UNFOLD   of string list * bindings
  | WITNESS  of 'term list * bindings
  | RULE     of 'fact list * bindings
  | CASE_SPLIT of 'term (*target*) * Minilang.opt_var_names
                * 'thm option (*rule*) * bindings
  | INDUCT   of 'term (*target*) * Minilang.opt_var_names
              * 'term list (*arbitrary*) * 'thm option (*rule*) * bindings
  | NEXT_OR_END of 'fact list (*add lemmas*) * Minilang.opt_var_names * bindings
  | NEXT     of 'fact list (*add lemmas*) * Minilang.opt_var_names * bindings
  | END      of 'fact list (*add lemmas*)
  | BRANCH   of string list
  | HAVE     of 'term list
  | OBTAIN   of (string * string option) list (*vars*) * string list (*constraints*)
  | SORRY    of Minilang.opt_var_names * bindings
  | HAMMER   of 'fact list (*with facts*)
  | INTRO    of bool (*single_goal*) * bindings
  | SKIP

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command

type counters = {
    prem_counter: int Synchronized.var,
    fact_counter: int Synchronized.var
  }
type config = cfg * budget * counters

val check_command : Proof.context -> xcmd -> icmd
val interpret_i : config -> icmd -> Minilang.state -> bindings * Minilang.state
val interpret : config -> xcmd -> Minilang.state -> bindings * Minilang.state

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

type var_name = {internal_name: string, external_name: string, typ_pretty: string}
type prem_name = {internal_term: term, external_name: string, pretty: string}
type bindings = var_name list * prem_name list

type counters = {
    prem_counter: int Synchronized.var,
    fact_counter: int Synchronized.var
  }
type config = cfg * budget * counters

datatype ('term, 'thm, 'fact) command =
    SIMPLIFY of 'fact list (*simp rules*) * bindings
  | UNFOLD   of string list * bindings
  | WITNESS  of 'term list * bindings
  | RULE     of 'fact list * bindings
  | CASE_SPLIT of 'term (*target*) * Minilang.opt_var_names
                * 'thm option (*rule*) * bindings
  | INDUCT   of 'term (*target*) * Minilang.opt_var_names
              * 'term list (*arbitrary*) * 'thm option (*rule*) * bindings
  | NEXT_OR_END of 'fact list (*add lemmas*) * Minilang.opt_var_names * bindings
  | NEXT     of 'fact list (*add lemmas*) * Minilang.opt_var_names * bindings
  | END      of 'fact list (*add lemmas*)
  | BRANCH   of string list
  | HAVE     of 'term list
  | OBTAIN   of (string * string option) list (*vars*) * string list (*constraints*)
  | SORRY    of Minilang.opt_var_names * bindings
  | HAMMER   of 'fact list (*with facts*)
  | INTRO    of bool (*single_goal*) * bindings
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

fun AUTO_INTRO (counters:counters) (bindings: bindings) (s:Minilang.state)
  : bindings * Minilang.state =
  let
    val ctxt = Minilang.context_of s
              |> Config.put Printer.show_markup false
    val st = Minilang.leading_proof_sequent_of s

    (* Destructure bindings into opt_var_names and opt_prem_names *)
    val (var_names, prem_names) = bindings
    val opt_var_names = if null var_names then NONE else SOME var_names
    val opt_prem_names = if null prem_names then NONE else SOME prem_names
  in
    (* Step 1: Check if INTRO is applicable *)
    if not (Minilang.need_intro st) then
      (([], []), s)
    else
      let
        (* Step 2: Extract quantified variables and premises from goal *)
        val goal_term = Thm.prop_of st |> Logic.dest_implies |> fst
        val (vars, prems, _) = Minilang.strip_meta_and_hol_hhf goal_term

        (* Step 3: Process variable names *)
        val (var_bindings, ctxt_with_vars) =
          case opt_var_names of
            NONE =>
              (* Use internal names after variant_fixes *)
              fold_map (fn (name, ty) => fn ctx =>
                let val (names', ctx') = Variable.variant_fixes [name] ctx
                    val actual_name = hd names'
                    val typ_pretty = REPL.trim_makrup (Syntax.string_of_typ ctx' ty)
                in ({internal_name = name, external_name = actual_name, typ_pretty = typ_pretty}, ctx')
                end
              ) vars ctxt
          | SOME provided_var_names =>
              let
                (* Try to match each quantified variable with provided names *)
                fun match_var (var_name, var_ty) ctx =
                  case find_first (fn {internal_name, ...} => internal_name = var_name) provided_var_names of
                    SOME {external_name, ...} =>
                      (* Found match: add the name to context to avoid future conflicts *)
                      let val (names', ctx') = Variable.add_fixes [external_name] ctx
                          val actual_name = hd names'
                          val typ_pretty = REPL.trim_makrup (Syntax.string_of_typ ctx' var_ty)
                      in ({internal_name = var_name, external_name = actual_name, typ_pretty = typ_pretty}, ctx')
                      end
                  | NONE =>
                      (* Use internal name with variant_fixes *)
                      let val (names', ctx') = Variable.variant_fixes [var_name] ctx
                          val actual_name = hd names'
                          val typ_pretty = REPL.trim_makrup (Syntax.string_of_typ ctx' var_ty)
                      in ({internal_name = var_name, external_name = actual_name, typ_pretty = typ_pretty}, ctx')
                      end
              in
                fold_map match_var vars ctxt
              end

        (* Convert var_bindings to opt_var_names for Minilang.INTRO *)
        val minilang_var_names = SOME (map (SOME o #external_name) var_bindings)

        (* Step 4: Process premise names *)
        val prem_counter = #prem_counter counters
        val (prem_bindings, _) =
          case opt_prem_names of
            NONE =>
              (* Auto-generate names using counter: premise0, premise1, ... *)
              fold_map (fn prem_term => fn counter_val =>
                let val name = "premise" ^ string_of_int counter_val
                    val pretty = REPL.trim_makrup (string_of_term ctxt_with_vars prem_term)
                in ({internal_term = prem_term, external_name = name, pretty = pretty}, counter_val + 1)
                end
              ) prems (Synchronized.value prem_counter)
              |> (fn (bindings, final_counter) =>
                   (Synchronized.change prem_counter (K final_counter); (bindings, ())))
          | SOME provided_prem_names =>
              let
                (* Try to match each premise with provided names by term equality *)
                fun match_prem prem_term counter_val =
                  let val pretty = REPL.trim_makrup (string_of_term ctxt_with_vars prem_term)
                   in case find_first (fn {internal_term, ...} =>
                                         internal_term aconv prem_term) provided_prem_names of
                        SOME {external_name, ...} => ({internal_term = prem_term, external_name = external_name, pretty = pretty}, counter_val)
                      | NONE =>
                          (* Auto-generate name *)
                          let val name = "premise" ^ string_of_int counter_val
                          in ({internal_term = prem_term, external_name = name, pretty = pretty}, counter_val + 1)
                          end
                  end
              in
                fold_map match_prem prems (Synchronized.value prem_counter)
                |> (fn (bindings, final_counter) =>
                     (Synchronized.change prem_counter (K final_counter); (bindings, ())))
              end

        (* Convert prem_bindings to opt_prem_names for Minilang.INTRO *)
        val minilang_prem_names = SOME (map (SOME o #external_name) prem_bindings)

        (* Step 5: Call INTRO' with SINGLE_GOAL mode *)
        val s' = Minilang.INTRO Minilang.SINGLE_GOAL minilang_var_names minilang_prem_names s

        (* Step 6: Return results *)
      in
        ((var_bindings, prem_bindings), s')
      end
  end

fun interpret_i (config as (cfg, budget, counters)) cmd s =
  case cmd of
      SIMPLIFY (simp_thms, bindings) =>
        let val s' = Minilang.SIMP'' (map (pair true) simp_thms) s
        in AUTO_INTRO counters bindings s'
        end
    | UNFOLD (origin_consts, bindings) =>
        let val _ = if null origin_consts
                    then error "You must specify at least one target to unfold"
                    else ()
            val ctxt = Minilang.context_of s
            val consts = map (Syntax.read_term ctxt) origin_consts
            val defs = map (Option.map (map snd) o find_def_const ctxt) consts
            val s' = Minilang.UNFOLD (flat (map_filter I defs)) s
        in AUTO_INTRO counters bindings s'
        end
    | WITNESS (terms, bindings) =>
        let val s' = Minilang.CHOOSE terms s
        in AUTO_INTRO counters bindings s'
        end
    | RULE (thms, bindings) =>
        let val s' = Minilang.RULE thms [] s
        in AUTO_INTRO counters bindings s'
        end
    | CASE_SPLIT (target, vars, rule, bindings) =>
        let val s' = Minilang.CASE_SPLIT (false, ([[SOME target]], rule)) vars [] s
        in AUTO_INTRO counters bindings s'
        end
    | INDUCT (target, vars, arbitrary, rule, bindings) =>
        let val ctxt = Minilang.context_of s
            val vs = map (fn Free nt => nt
                           | x => error ("The `arbitrary` argument must be variables, but (" ^
                                         string_of_term ctxt x ^ ") is given.")) arbitrary
            val s' = Minilang.INDUCT
                    (false, ([[SOME (NONE, (target, false))]], (([vs], []), Option.map single rule))) vars [] s
        in AUTO_INTRO counters bindings s'
        end
    | NEXT_OR_END (lemmas, vars, bindings) =>
        let val s' = Minilang.END_or_NXT vars {add=lemmas,del=[],only=false} s
        in AUTO_INTRO counters bindings s'
        end
    | NEXT (lemmas, vars, bindings) =>
        let val s' = Minilang.NXT vars {add=lemmas,del=[],only=false} s
        in AUTO_INTRO counters bindings s'
        end
    | END lemmas =>
        let val s' = Minilang.END {add=lemmas,del=[],only=false} s
        in (([], []), s')
        end
    | BRANCH branches =>
        let val brs = map (fn br => ([], ([], [], [(Binding.empty_atts, [(br, [])])]))) branches
            val s' = Minilang.CONSIDER brs s
        in (([], []), s')
        end
    | HAVE goals =>
        let val s' = Minilang.HAVE'' [] [] (map (fn goal => (Binding.empty_atts, [(goal, [])])) goals) s
        in (([], []), s')
        end
    | OBTAIN (vars, constraints) =>
        let val arg = [(map (fn (v,T) => (Binding.name v, T, NoSyn)) vars,
                       ([], [], map (fn goal => (Binding.empty_atts, [(goal, [])])) constraints))]
            val s' = Minilang.CONSIDER arg s
        in (([], []), s')
        end
    | SORRY (vars, bindings) =>
        let val s' = Minilang.END_or_NXT_by_SORRY vars s
        in AUTO_INTRO counters bindings s'
        end
    | HAMMER facts =>
        let val s' = Minilang.HAMMER {add=facts,del=[],only=false} s
        in (([], []), s')
        end
    | INTRO (single_goal, bindings) =>
        AUTO_INTRO counters bindings s
    | SKIP => (([], []), s)

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
fun check_command_i _ (SIMPLIFY (facts, bindings)) = SIMPLIFY (map read_fact facts, bindings)
  | check_command_i _ (RULE (facts, bindings)) = RULE (map read_fact facts, bindings)
  | check_command_i _ (UNFOLD (consts, bindings)) = UNFOLD (consts, bindings)
  | check_command_i ctxt (WITNESS (terms, bindings)) = WITNESS (Syntax.read_terms ctxt terms, bindings)
  | check_command_i ctxt (CASE_SPLIT (target, vars, rule, bindings)) =
      let val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
          val target' = Syntax.read_term ctxt target
       in CASE_SPLIT (target', vars, rule', bindings)
      end
  | check_command_i ctxt (INDUCT (target, vars, arbitrary, rule, bindings)) =
      let val (target' :: arbitrary') = Syntax.read_terms ctxt (target :: arbitrary)
          val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
       in INDUCT (target', vars, arbitrary', rule', bindings)
      end
  | check_command_i _ (NEXT_OR_END (facts, vars, bindings)) = NEXT_OR_END (map read_fact facts, vars, bindings)
  | check_command_i _ (NEXT (facts, vars, bindings)) = NEXT (map read_fact facts, vars, bindings)
  | check_command_i _ (END facts) = END (map read_fact facts)
  | check_command_i _ (BRANCH brs) = BRANCH brs
  | check_command_i ctxt (HAVE goals) = HAVE (Syntax.read_props ctxt goals)
  | check_command_i _ (OBTAIN vc) = OBTAIN vc
  | check_command_i _ (SORRY (vars, bindings)) = SORRY (vars, bindings)
  | check_command_i _ (HAMMER facts) = HAMMER (map read_fact facts)
  | check_command_i _ (INTRO (single_goal, bindings)) = INTRO (single_goal, bindings)
  | check_command_i _ SKIP = SKIP

fun check_command ctxt x = check_command_i ctxt x
    handle ERROR msg => raise Minilang.OPR_FAIL (Minilang.TERMLANG, msg)

end

fun interpret cfg xcmd state =
  let val icmd = check_command (Minilang.context_of state) xcmd
   in interpret_i cfg icmd state
  end


end

