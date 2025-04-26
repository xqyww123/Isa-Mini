signature MINILANG = sig

type stack
type state
type operation = state -> state
type command = operation parser

type variables = (string * typ) list
type local_facts = (string * term list) list
type items = variables * local_facts
type fact = Facts.ref * Token.src list

val context_of  : state -> Proof.context
val equiv_proof_state : state * state -> bool
val num_goals   : state -> int
val map_context : (Proof.context -> Proof.context) -> state -> state

datatype fail_reason = INVALID_OPR | PROOF_FAIL
exception OPR_FAIL of fail_reason * string

type with_clause = (bool (*with or without*) * string (*name*) * thm) list
type opt_var_names = string option list option

(* options *)

val atomize_goals : bool Config.T
val working_mode : string Config.T
val mini_single_cmd_timeout : int Config.T
val typ_parsing_mode : string Config.T
val install_relaxed_typ_parsing : Context.generic -> Context.generic

(* Operations *)

val INIT : Proof.context -> thm -> state
val INIT': Proof.state -> state
val conclude : Proof.context -> state -> thm
val is_finished : state -> bool

(*Thread local*)
datatype message = New_Items of items
                 | Goals     of term list option
                 | Consider_Case of string
                 | Internal of exn
val set_reporter : (message (*new items*) -> unit) -> unit
val get_reporter : unit -> (message (*new items*) -> unit)

val empty_items : items
val cat_items : items -> items -> items

datatype intros_mode = ALL_SUBGOALS | SINGLE_GOAL
val INTRO : intros_mode -> opt_var_names -> operation
val INTRO_CMD : command

val apply : context_tactic -> Time.time option -> stack -> stack
val apply_method : thm list -> Method.method -> Time.time option -> stack -> stack
val APPLY   : Time.time option -> thm list -> Method.text -> operation
val APPLY'' : Time.time option -> fact list -> Method.text -> operation
val APPLY_CMD : command

val crush_timeout : int Config.T
val CRUSH : opt_var_names * with_clause -> operation
val CRUSH_CMD : command
val SIMP : with_clause -> operation
val SIMP'' : (bool * (Facts.ref * Token.src list)) list -> operation
val SIMP_CMD : command

val UNFOLD : thm list -> operation
val UNFOLD_CMD : command

val INDUCT : bool * ((binding option * (term * bool)) option list list *
              (((string * typ) list list * term option list) * thm list option))
          -> opt_var_names
          -> thm list
          -> operation
val INDUCT'' : Token.src * opt_var_names * fact list -> operation
val INDUCT_CMD : command

val CASE_SPLIT   : bool * (term option list list * thm option)
                -> opt_var_names
                -> thm list
                -> operation
val CASE_SPLIT'' : Token.src * opt_var_names * fact list -> operation
val CASE_SPLIT_CMD : command

val record_history : string -> operation
val restore_history : string -> operation

val HAVE : (binding * string option * mixfix) list
        -> (Attrib.binding * (string * string list) list) list
        -> (Attrib.binding * (string * string list) list) list
        -> operation
val HAVE'' : (binding * typ option * mixfix) list
        -> (Attrib.binding * (term * term list) list) list
        -> (Attrib.binding * (term * term list) list) list
        -> operation
val HAVE_CMD : command

val CONSIDER : (
               (binding * string option * mixfix) list
             * ( (binding * string option * mixfix) list
               * (string * string list) list list
               * (Attrib.binding * (string * string list) list) list )
             ) list
          -> operation
val CONSIDER_CMD : command

val HAMMER : Sledgehammer.fact_override -> operation
val HAMMER_CMD : command
val enable_cache_by_step : bool Config.T

val END : Sledgehammer.fact_override -> operation
val END_CMD : command
datatype endblk_type = T_END | T_NXT
val type_of_end : state -> endblk_type option

val NOTATION   : Syntax.mode -> (term * mixfix) list -> operation
val NOTATION'' : Syntax.mode -> (string * mixfix) list -> operation
val NOTATION_CMD : command

val NXT : opt_var_names -> Sledgehammer.fact_override -> operation
val NXT_CMD : command

val LET   : (term list * term) list -> operation
val LET'' : (string list * string) list -> operation
val LET_CMD : command

datatype tree = PROP  of items * term (*goal*)
              | BUNDL of items * tree list
              | BLOCK of tree
val print_state : state -> tree
val atomize_tree : Proof.context -> tree -> tree
val PRINT : operation
val PRINT_CMD : command

val OPEN_MODULE   : Expression.expression_i -> state -> state
val OPEN_MODULE'' : Expression.expression   -> state -> state
val OPEN_MODULE_CMD : Token.T list -> (state -> state) * Token.T list

datatype config = CFG_NOTE   of Thm.binding * (thm list * attribute list) list
                | CFG_BUNDLE of Bundle.name
val CONFIG : config list -> operation
val CONFIG_FACTS'' : (Attrib.binding * (Facts.ref * Token.src list) list) list -> operation
val CONFIG_BUNDL'' : string list -> operation

val CONFIG_CMD : command

val RULE : (Facts.ref * Token.src list) list (*rule*)
        -> (Facts.ref * Token.src list) list (*with facts*)
        -> operation
val RULE_CMD : command

val CHOOSE : term list -> operation
val CHOOSE'' : (string * (binding * string option * mixfix) list) list -> operation
val CHOOSE_CMD : command

val DEFINE : (binding * typ option * mixfix) list
          -> (Thm.binding * (term * term list) list) list
          -> (binding * typ option * mixfix) list
          -> operation
val DEFINE'' : (binding * string option * mixfix) list
            -> (Attrib.binding * (string * string list) list) list
            -> (binding * string option * mixfix) list
            -> operation
val DEFINE_CMD : command

val STEP   : fact list ->  term  -> operation
val STEP'' : fact list -> string -> operation
val STEP_CMD : command

(* Toplevel *)

val lex_cmds : string -> Token.src list
val parse_cmds : Token.src list -> operation
val PROVE : operation -> Proof.context -> thm -> thm

val METHOD : string -> Method.method
val MP : Proof.context -> thm -> thm -> thm

(* Internal *)

exception IH_MAP of (string * string list) list
exception SH_PRF of string
exception REPLACE_CMD of string * string

end

structure Minilang : MINILANG = struct
open Minilang_Aux

(** Preliminaries **)

val assm_N = "assm"
fun assm_name i = assm_N ^ string_of_int i

(* options *)

val atomize_goals = Attrib.setup_config_bool \<^binding>\<open>min_shell_atomize_goals\<close> (K true)
val working_mode = Attrib.setup_config_string \<^binding>\<open>working_mode\<close> (K "RELAXED")

type variables = (string * typ) list
type local_facts = (string * term list) list
type items = variables * local_facts
type fact = Facts.ref * Token.src list

val empty_items : items = ([],[])
fun join_lstR pr = AList.join (op =) (fn _ => fn (_,x) => x) pr
fun join_lstL pr = AList.join (op =) (fn _ => fn (x,_) => x) pr

(*primary is the newer. The newer is appended to the list*)
fun cat_items (vs',hs') (vs,hs)
      = (join_lstR (vs', vs), join_lstL (hs', hs))

(*only for printing*)
datatype tree = PROP  of items * term (*goal*)
              | BUNDL of items * tree list
              | BLOCK of tree
type param = exn
datatype endblk_type = T_END | T_NXT
datatype frame = HHF   of thm (*a local_facts bundle node, represented as a Hereditary Harrop Formula*)
                        * items
               | MAGIC of (Proof.context -> thm * items * frame list * param -> Proof.context * frame list)
                        * (param -> tree -> tree)
                        * param
               | ENDBLK of endblk_type

type opt_var_names = string option list option
exception NO_PARAM
exception CASE_NAME of opt_var_names

type stack = Proof.context * (frame list)
  (*invariant: the head must be an HHF*)

type state = stack              (*current stack*)
           * stack Symtab.table (*history*)
           * int                (*cache id*)

type operation = state -> state
type command = operation parser

fun context_of (((ctxt,_), _, _) : state) = ctxt
(*only checks state sequent*)
fun equiv_proof_state ( ((ctxt, HHF (st, _) :: _), _, _) , ((_, HHF (st', _) :: _), _, _) )
      = Thm.equiv_thm (Proof_Context.theory_of ctxt) (st, st')
fun map_context F ((ctxt,SK), his, ID) = ((F ctxt,SK), his, ID)

exception BROKEN_INVARIANT

datatype fail_reason = INVALID_OPR | PROOF_FAIL
exception OPR_FAIL of fail_reason * string

(* Helpers *)

fun is_protected (\<^Const>\<open>Pure.prop\<close> $ _) = true
  | is_protected (\<^Const>\<open>Pure.imp\<close> $ _ $ X) = is_protected X
  | is_protected (\<^Const>\<open>Pure.all _\<close> $ Abs (_,_, X)) = is_protected X
  | is_protected _ = false

fun mk_binding long_name =
  let val names = Long_Name.explode long_name
      fun mk [] = error "BUG"
        | mk [x] = Binding.name x
        | mk (q::L) = Binding.qualify_name true (mk L) q
   in case names
   of "local"::L => mk L
    | L => mk L
  end

fun protect_goals th =
  let fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X =>
            (case X
               of Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _ => Conv.all_conv ctm
                | Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _ => Conv.all_conv ctm
                | _ => (Conv.arg_conv (conv then_conv 
                                       Conv.rewr_conv Thms.GOAL_def'sym)) ctm)
           | _ => Conv.all_conv ctm
   in Conv.fconv_rule conv th
  end

fun pop_n_goals n th =
  let open Conv
      fun conv N ctm =
        if N <= 1 then all_conv ctm
        else case Thm.term_of ctm
          of Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _
                $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _ ) =>
             (arg_conv (rewr_conv Thms.GOAL_def) then_conv
              arg_conv (conv (N-1)) then_conv
              rewr_conv Thms.conjunction_imp'sym) ctm
           | _ => raise THM ("pop_n_goals: insufficient goals", n, [th])
   in if n <= 1 then th else fconv_rule (conv n) th
  end

fun init_goal ctxt th = th
      |> Conv.fconv_rule (concl_conv iso_atomize ctxt)
      |> protect_goals

val num_goals_of =
  let fun calc ret (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X))
            = calc (ret+1) X
        | calc ret (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _)) = ret + 1
        | calc ret (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X) = calc (ret+1) X
        | calc _ _ = raise BROKEN_INVARIANT
   in fn Const (\<^const_name>\<open>Pure.prop\<close>, _) $ _ => 0
       | tm => calc 0 tm
  end
val num_goals_of' = num_goals_of o Thm.prop_of
fun num_goals ((_, HHF (st, _) :: _), _, _) = num_goals_of' st
  | num_goals _ = raise BROKEN_INVARIANT

fun no_goal (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _)) = false
  | no_goal (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _)) = false
  | no_goal (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _) = false
  | no_goal _ = true
val no_goal' = no_goal o Thm.prop_of

val goals_of =
  let fun collect (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X))
            = G :: collect X
        | collect (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X)
            = \<^prop>\<open>True\<close> :: collect X
        | collect (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _))
            = [G]
        | collect _ = raise BROKEN_INVARIANT
   in fn Const (\<^const_name>\<open>Pure.prop\<close>, _) $ _ => [\<^prop>\<open>True\<close>]
       | tm => collect tm
  end
val goals_of' = goals_of o Thm.prop_of

fun concl_of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X)) = concl_of X
  | concl_of (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X) = concl_of X
  | concl_of (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X) = X
  | concl_of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X)) = X
  | concl_of _ = raise BROKEN_INVARIANT
  

fun conclude_goal th =
  let fun conv ctm =
        (case Thm.term_of ctm
           of Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _ => Conv.rewr_conv Thms.GOAL_def ctm
            | Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _ => Conv.all_conv ctm
            | _ => raise THM ("conclude_goal", 0, [th]))
   in Conv.fconv_rule conv th
  end

fun finalize_goal ctxt th = th
      |> Conv.fconv_rule (concl_conv iso_rulify ctxt)

(* Printer *)

val SOLVED_TREE = BUNDL (empty_items, [])

fun print_stack [] = SOLVED_TREE
  | print_stack (S::L) =
      let 
          fun prt t [] = t
            | prt t (HHF (st, items) :: L) =
                let val goals = case goals_of' st
                                  of [] => raise BROKEN_INVARIANT
                                   | (_::prems) => prems
    
                    val nodes = map (fn goal => PROP (([],[]), goal)) goals
                 in prt (BUNDL (items, t::nodes)) L
                end
            | prt t (MAGIC (_, PRT, param) :: L) = prt (PRT param t) L
            | prt t (ENDBLK _ :: L) = prt t L
          fun prt0 (HHF (st, items)) =
              if no_goal' st
              then SOLVED_TREE
              else(case goals_of' st
                   of [goal] => PROP (items, goal)
                    | [] => raise BROKEN_INVARIANT
                    | goals => BUNDL (items, map (PROP o pair empty_items) goals) )
            | prt0 _ = raise BROKEN_INVARIANT
       in prt (prt0 S) L
      end

fun print_state ((_,SK),_,_) = print_stack SK

fun cat_tree (PROP (items, goal)) (PROP (items', _)) = PROP (cat_items items items', goal)
  | cat_tree (BUNDL (items, goal)) (PROP (items', _)) = BUNDL (cat_items items items', goal)
  | cat_tree T (BUNDL (items', goals)) = BUNDL (items', cat_tree T (hd goals) :: tl goals)

fun atomize_tree ctxt (PROP (items, goal)) = PROP (items, Object_Logic.atomize_term ctxt goal)
  | atomize_tree ctxt (BUNDL (items, goal)) = BUNDL (items, map (atomize_tree ctxt) goal)
  | atomize_tree ctxt (BLOCK tree) = BLOCK (atomize_tree ctxt tree)


val collect_context =
  let fun collect V F (PROP  ((V',F'),term)) = (V @ V', F @ F', term)
        | collect V F (BUNDL ((V',F'),chil)) = collect (V @ V') (F @ F') (hd chil)
        | collect V F (BLOCK tree) = collect V F tree
   in collect [] []
  end

fun fold_all_names f (PROP ((V,F),_)) x =
      x |> fold (f o fst) V |> fold (f o fst) F
  | fold_all_names f (BUNDL ((V,F), chil)) x =
      x |> fold (f o fst) V |> fold (f o fst) F
        |> fold (fold_all_names f) chil
  | fold_all_names f (BLOCK tree) x = fold_all_names f tree x

fun quanlifiers_of tree =
  let fun merge [] L = L
        | merge [_] L = L
        | merge (h::L') L = merge L' (insert (op =) h L)
   in fold_all_names (merge o Long_Name.explode) tree []
  end

(* Common Syntax *)

type with_clause = (bool (*with or without*) * string (*name*) * thm) list

val WITH_CLAUSE    = Parse.$$$ "WITH"    |-- Scan.repeat Parse.thm
val WITHOUT_CLAUSE = Parse.$$$ "WITHOUT" |-- Scan.repeat Parse.thm
val with_parser =
        Scan.repeat ( WITH_CLAUSE    >> pair true
                   || WITHOUT_CLAUSE >> pair false )
     >> maps (uncurry (map o pair))

val orverride_parser =
        Scan.repeat (   (Parse.$$$ "WITH"    |-- Scan.repeat Parse.thm >> rpair [])
                     || (Parse.$$$ "WITHOUT" |-- Scan.repeat Parse.thm >>  pair []) )
     >> (fn LL => fold_rev (fn (A,D) => fn (A',D') => (A @ A', D @ D') ) LL ([],[])
               |> (fn (A,D) => {add = A, del = D, only = false}))

fun name_of_ref (Facts.Named ((name,_), _)) = name
  | name_of_ref (Facts.Fact _) = ""

fun read_with ctxt with_lems =
      maps (fn (flag, fact) =>
        let val name = name_of_ref (fst fact)
         in Attrib.eval_thms ctxt [fact]
         |> map (fn th => (flag, name, th) )
        end ) with_lems

fun apply_WITH with_lems =
  fold (fn (flag, name, thm) =>
    Context.proof_map (Phi_Sledgehammer_Solver.with_rule flag name thm)) with_lems

(** REPORTER **)

datatype message = New_Items of items
                 | Goals     of term list option
                 | Consider_Case of string
                 | Internal of exn
val reporter = Thread_Data.var () : (message -> unit) Thread_Data.var
val default_reporter = K ()


fun set_reporter r = Thread_Data.put reporter (SOME r)
fun get_reporter () =
  case Thread_Data.get reporter
    of NONE => default_reporter
     | SOME r => r

fun report_goal (ctxt, SK) = (
          (case SK of HHF (st, _) :: _ =>
             (case try Logic.dest_implies (Thm.prop_of st)
                of SOME (goal, _) => get_reporter () (Goals (SOME [goal]))
                 | NONE => get_reporter () (Goals (SOME [])))
              | _ => raise BROKEN_INVARIANT )
          ; (ctxt, SK) )

(** Basic Operations **)

structure IPS_Data = Proof_Data (
  type T = ( int    (*counter for fixed premise*)
           * int    (*facts counter*)
           * string (*hash used for caching proof*) )
  val init = K (0,0,"")
)

fun incr_premise_counter delta ctxt =
  let val (ii,jj,ID) = IPS_Data.get ctxt
   in (ii, IPS_Data.put (ii+delta,jj,ID) ctxt)
  end

fun incr_fact_counter delta ctxt =
  let val (ii,jj,ID) = IPS_Data.get ctxt
   in (jj, IPS_Data.put (ii,jj+delta,ID) ctxt)
  end


fun beta_eta_contract th =
  if Term.could_beta_eta_contract (Thm.prop_of th)
  then Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th
  else th

(* Modus Ponens *)
fun norm_tyenv tyenv
  = TVars.build (Vartab.fold (fn (N,(S,T)) => TVars.add ((N,S), Envir.norm_type tyenv T)) tyenv)

fun norm_tenv tyenv tenv =
  Vars.build (Vartab.fold (fn (N,(TY,TM)) =>
      Vars.add ((N, Envir.norm_type tyenv TY),
                    Envir.norm_term (Envir.Envir {maxidx = ~1, tenv=tenv,tyenv=tyenv}) TM
                                |> Envir.eta_contract)) tenv)

fun norm_env' (TY,TM) = (norm_tyenv TY, norm_tenv TY TM)
fun certify_tyvars ctxt = TVars.map (K (Context.cases Thm.global_ctyp_of Thm.ctyp_of ctxt))
fun certify_tmvars ctxt = Vars.map (K (Context.cases Thm.global_cterm_of Thm.cterm_of ctxt))
fun certify_vars ctxt (ty, tm) = (certify_tyvars ctxt ty, certify_tmvars ctxt tm)
fun norm_env ctxt (Envir.Envir {tenv, tyenv, ...}) = certify_vars ctxt (norm_env' (tyenv, tenv))

local fun protect_prop ctxt ctm = let open Conv
                       in case Thm.term_of ctm
                           of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
                                (arg_conv (abs_conv (protect_prop o snd) ctxt)) ctm
                            | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
                                (combination_conv (arg_conv (rewr_conv Thms.prop_def'sym))
                                                  (protect_prop ctxt) ctm)
                            | _ => Conv.all_conv ctm
                      end
 in
fun MP' ctxt rule thA0 =
                        let val thA = Conv.fconv_rule (protect_prop ctxt) thA0
                         in rule
                            |> Conv.fconv_rule (Conv.arg1_conv (protect_prop ctxt))
                            |> (Thm.biresolution (SOME ctxt) true [(false, thA)]
                                  THEN_ALL_NEW Thm.assumption (SOME ctxt)) 1
                            |> Seq.pull
                            |> (fn SOME (ret, _) => ret
                                 | NONE => error "BUG: CASES' MP")
                       end
end

fun MP ctxt thAB thA =
  \<^try>\<open>
  let val thAB = beta_eta_contract thAB
      val thA  = beta_eta_contract thA
      val LHS = Thm.cprop_of thAB
             |> Thm.dest_arg1

      fun qnum (\<^Const>\<open>Pure.all _\<close> $ Abs (_, _, A)) = 1 + qnum A
        | qnum _ = 0
      val diff = qnum (Thm.term_of LHS) - qnum (Thm.prop_of thA)
      val (thAB', thA') =
          if diff <= 0
          then (Thm.instantiate (Thm.match (LHS, Thm.cprop_of thA)) thAB |> beta_eta_contract,
                thA)
          else let
              val frees = Term.declare_term_frees (Thm.prop_of thA)
                              (Term.declare_term_frees (Thm.term_of LHS) Name.context)
              val names = Name.invent frees "x" diff 
              val (fixes, LHS') = fold_map (fn name => Thm.dest_abs_fresh name o Thm.dest_arg)
                                           names LHS
              val thA = Thm.incr_indexes (Thm.maxidx_of thAB + 1) thA
              val inst = Unify.smash_unifiers (Context.Proof ctxt)
                                              [(Thm.term_of LHS', Thm.prop_of thA)]
                                              (Envir.empty (Thm.maxidx_of thA + 1))
                     |> Seq.pull
                     |> (fn SOME (ret, _) => ret
                          | NONE => raise THM ("unification fail", 1, [thAB, thA]))
                     |> norm_env (Context.Proof ctxt)
              val thAB = Thm.instantiate inst thAB |> beta_eta_contract
              val xxxx = thA
              val thA  = Thm.instantiate inst thA  |> beta_eta_contract
                                                   |> fold_rev Thm.forall_intr fixes

           in (thAB, thA)
          end

   in Thm.implies_elim thAB' thA'
  end
  catch _ => MP' ctxt thAB thA \<close>


(* Helpers II *)

fun elim_conjs ctxt =
  let fun elim thm =
      case Thm.prop_of thm
        of \<^Const>\<open>Pure.conjunction\<close> $ _ $ _ =>
            elim (MP ctxt Thms.conjunctionD1 thm) @
            elim (MP ctxt Thms.conjunctionD2 thm)
         | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.conj\<close> $ _ $ _) =>
            elim (MP ctxt Thms.conjunct1 thm) @
            elim (MP ctxt Thms.conjunct2 thm)
         | _ => [thm]
   in elim
  end

fun wraps ctxt ths = ths
      |> map (Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv Thms.TAG_def'sym)))
      |> foldr1 (fn (A,B) => MP ctxt (MP ctxt Thms.conjI A) B)

val is_tagged =
  let fun chk (\<^Const>\<open>Trueprop\<close> $ X) = chk X
        | chk (\<^Const>\<open>HOL.TAG _\<close> $ _) = true
        | chk (\<^Const>\<open>HOL.conj\<close> $ A $ B) = chk A andalso chk B
        | chk (\<^Const>\<open>Pure.imp\<close> $ A $ B) = chk A orelse chk B
        | chk (\<^Const>\<open>Pure.all _\<close> $ Abs (_, _, X)) = chk X
        | chk _ = false
   in chk
  end

fun is_Trueprop (\<^Const>\<open>Trueprop\<close> $ _) = true
  | is_Trueprop _ = false

fun is_tagged_Trueprop x = is_Trueprop x andalso is_tagged x

fun remove_TAG_premises ctxt th =
  let fun conv ctxt ctm =
        let val tm = Thm.term_of ctm
         in if exists is_tagged (Logic.strip_imp_prems tm)
          then case tm
            of \<^Const>\<open>Pure.imp\<close> $ X $ _ =>
                if is_tagged_Trueprop X
                then (case X
                  of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>conj\<close> $ _ $ _) =>
                      (Conv.rewr_conv Thms.conj_imp_eq_imp_imp
                       then_conv conv ctxt) ctm
                   | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.TAG _\<close> $ _) =>
                      (Conv.arg1_conv (HOLogic.Trueprop_conv (Conv.rewr_conv Thms.TAG_def))
                       then_conv conv ctxt) ctm)
                else Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt) ctm
             | \<^Const>\<open>Pure.all _\<close> $ Abs (_, _, _) =>
                  Conv.abs_conv (fn (_,ctxt) => conv ctxt) ctxt ctm
          else Conv.all_conv ctm
        end
   in if exists is_tagged (Thm.prems_of th)
      then Conv.fconv_rule (conv ctxt) th
      else th
  end

fun unwrap_conjs' ctxt th = th
      |> elim_conjs ctxt
      |> map (Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv Thms.TAG_def)))

fun unwrap_conjs ctxt th =
      if is_Trueprop (Thm.prop_of th) andalso is_tagged (Thm.prop_of th)
      then unwrap_conjs' ctxt th
      else raise THM ("Not tagged", 0, [th])

fun unwrap_tags ctxt th =
  let fun conv ctxt ctm =
        (case Thm.term_of ctm
           of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
                Conv.arg_conv (Conv.abs_conv (conv o snd) ctxt) ctm
            | Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const(\<^const_name>\<open>HOL.Trueprop\<close>, _)
                    $ (Const(\<^const_name>\<open>HOL.conj\<close>, _)
                        $ (Const(\<^const_name>\<open>HOL.TAG\<close>, _) $ _)
                        $ _ ) )
                $ _ =>
              ( Conv.rewr_conv Thms.conj_imp_eq_imp_imp
              then_conv conv ctxt
              ) ctm
            | Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const(\<^const_name>\<open>HOL.Trueprop\<close>, _)
                    $ (Const(\<^const_name>\<open>HOL.TAG\<close>, _) $ _) )
                $ _ =>
              ( Conv.arg1_conv (HOLogic.Trueprop_conv (Conv.rewr_conv Thms.TAG_def))
              then_conv conv ctxt
              ) ctm
            | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
              (Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt)) ctm
            | _ => Conv.all_conv ctm)
      val qchk = Term.exists_Const (fn (\<^const_name>\<open>HOL.TAG\<close>, _) => true | _ => false)
   in if qchk (Thm.prop_of th)
    then Conv.fconv_rule (conv ctxt) th
    else th
  end

(*
fun unwrap ctxt th = th
      |> unwrap_conjs ctxt
      |> map (remove_TAG_premises ctxt)
*)

(* Maintain *)

(*
fun append_print items' (PROP (items, goal))
      = (PROP  (cat_items items' items, goal))
  | append_print items' (BUNDL (items, goal))
      = (BUNDL (cat_items items' items, goal))
*)
fun prepend_print items' (PROP (items, goal))
      = (PROP  (cat_items items items', goal))
  | prepend_print items' (BUNDL (items, goal))
      = (BUNDL (cat_items items items', goal))
  | prepend_print items' (BLOCK tree)
      = BLOCK (prepend_print items' tree)

fun maintain (c,[]) = (c,[])
  | maintain (origin as (ctxt, HHF (st, items) :: L)) =
      if no_goal' st
      then (case L
              of [] => origin
               | (HHF _ :: _) => raise BROKEN_INVARIANT
                    (* maintain (ctxt, HHF (MP ctxt st1 st, cat_items items items') :: L') *)
               | (MAGIC (cb,_,param) :: L') =>
                    (case cb ctxt (st, items, L', param) of (ctxt', S) => maintain (ctxt', S) )
               | ENDBLK _ :: _ => origin )
      else origin
  | maintain (_, MAGIC _ :: _) = raise BROKEN_INVARIANT
  | maintain (_, ENDBLK _ :: _) = raise BROKEN_INVARIANT


fun need_intro st =
  let fun need' (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _) = true
        | need' (Const(\<^const_name>\<open>Pure.all\<close>, _) $ _) = true
        | need' (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = need' X
        | need' (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) = true
        | need' (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) = true
        | need' _ = false
   in case Thm.prop_of st
        of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ _) => need' G
         | _ => false
  end

fun simp_name name =
  if String.isPrefix "local." name
  then String.substring (name, 6, size name - 6)
  else name


(* Hacks *)

fun remove_typ str =
  let datatype state = MARK of state | USUAL | TYP1 | TYP of int
      fun auto _ [] = []
        | auto s (#"\127" :: L) = auto s L
        | auto (MARK s) (#"\005" :: L) = auto s L
        | auto (MARK s) (_ :: L) = auto (MARK s) L
        | auto s (#"\005" :: L) = auto (MARK s) L
        | auto USUAL (#":" :: L) = auto TYP1 L
        | auto USUAL (x :: L) = x :: auto USUAL L
        | auto TYP1 (#":" :: L) = auto (TYP 0) L
        | auto TYP1 L = #":" :: auto USUAL L
        | auto (TYP i) (#"(" :: L) = auto (TYP (i+1)) L
        | auto (TYP 0) (#")" :: L) = #")" :: auto USUAL L
        | auto (TYP i) (#")" :: L) = auto (TYP (i-1)) L
        | auto (TYP i) (_ :: L) = auto (TYP i) L
   in String.implode (auto USUAL (String.explode str))
  end

fun remove_typ_ass x = map (apsnd (map (apfst remove_typ #> apsnd (map remove_typ)))) x
fun remove_typ_ss x = map (map (apfst remove_typ #> apsnd (map remove_typ))) x

val typ_parsing_mode = Attrib.setup_config_string \<^binding>\<open>mini_typ_mode\<close> (K "flexible")

fun tolerate_typ tr fix s =
  tr s handle E as Exn.EXCEPTIONS [ERROR msg] =>
    if String.isPrefix "Undefined type name: " msg
    then let val ctxt = context_of s
      in if Config.get ctxt typ_parsing_mode = "flexible"
       then fix s
       else Exn.reraise E
     end
    else Exn.reraise E

(*** COMMANDS ***)

(** INTRO **)

fun map2_opt _ [] [] = []
  | map2_opt f [] (y :: ys) = f NONE y :: map2_opt f [] ys
  | map2_opt f (x :: xs) (y :: ys) = f x y :: map2_opt f xs ys
  | map2_opt _ _ _ = raise ListPair.UnequalLengths


datatype intros_mode = ALL_SUBGOALS | SINGLE_GOAL

fun strip_meta_hhf term =
  let fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,H::P) B
        | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
        | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ X) =
            strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | strip (V,P) X = (rev V, rev P, X)
   in strip ([],[]) term end

fun INTRO'' F mode bs (origin as (ctxt, HHF (st0, items) :: L)) =
    if Thm.no_prems st0 then origin
    else if need_intro st0
      then let val st = st0
                     |> Seq.REPEAT (Thm.biresolution NONE true
                              [(false, Thms.allI), (false, Thms.impI)] 1)
                     |> Seq.hd

               val default_binds = Thm.prop_of st
                                |> Logic.dest_implies |> fst
                                |> strip_meta_hhf
                                |> #1 |> map #1
                                |> (fn L => fold_map Name.variant L
                                                  (Variable.names_of ctxt))
                                |> #1
               val binds = case bs
                             of NONE => default_binds
                              | SOME bs'0 =>
                                  let val bs' = if member (op =) ["COMPLETE_NEXT", "RELAXED"]
                                                                 (Config.get ctxt working_mode)
                                                then take (length default_binds) bs'0
                                                else bs'0
                                   in map2_opt (fn NONE => I
                                                 | SOME b => K b) bs' default_binds
                                      handle ListPair.UnequalLengths =>
                                        raise OPR_FAIL (INVALID_OPR, "Incorrect number of VARS")
                                  end
               val (foc, st') = Subgoal.focus_prems ctxt 1 (SOME (map Binding.name binds)) st
               val (st'', (items', ctxt')) = F (st', foc)
               val _ = get_reporter () (New_Items items')
               fun PRT _ t =
                    let 
                     in case print_stack [(HHF (st0, items))]
                     of BUNDL (items, goals) =>
                        BUNDL (items, t :: tl goals)
                      | PROP  (items, _) => t
                          |> prepend_print items
                      | _ => raise BROKEN_INVARIANT
                    end
               fun CB ctxt'' (st'',_,S, CASE_NAME bs) =
                let val st'3 = singleton (Proof_Context.export ctxt'' ctxt') st''
                 in (ctxt, HHF (
                           Subgoal.retrofit ctxt'' ctxt (#params foc) (#asms foc) 1 st'3 st
                        |> Seq.hd
                        |> conclude_goal,
                      ([],[])) :: S)
                 |> mode = ALL_SUBGOALS ? INTRO'' F mode bs
                end
                 | CB _ _ = raise BROKEN_INVARIANT
            in if num_goals_of' st0 > 1
            then (ctxt', HHF (st'', items') :: ENDBLK T_NXT :: MAGIC (CB,PRT,CASE_NAME NONE) :: L)
            else (ctxt', HHF (st'', items') :: MAGIC (CB,PRT,CASE_NAME NONE) :: L)
           end
      else (ctxt, HHF (st0, items) :: L)
  | INTRO'' _ _ _ _ = raise BROKEN_INVARIANT

val INTRO' = INTRO'' (fn (st, foc) =>
  let val (i,ctxt) = #context foc
                  |> incr_premise_counter (length (#prems foc))
   in ctxt
   |> Proof_Context.note_thmss "" (map_index (fn (d,th) =>
        ((Binding.name (assm_name (i+d)), []), [([th], [])])
      ) (#prems foc))
   |> apfst (map ( apsnd (map Thm.prop_of)
                #> apfst simp_name )
          #> pair (#params foc |> map ( apsnd Thm.typ_of_cterm )))
   |> pair st
  end )

fun raw_apply report tac timeout (ctxt, HHF (st, facts) :: L) =
    ( case (case timeout
              of SOME time => Timeout.apply time (Seq.pull o tac) (ctxt, st)
               | NONE      => Seq.pull (tac (ctxt, st)) )
        of NONE => raise OPR_FAIL (PROOF_FAIL, "Fail to apply the tactic")
         | SOME (Seq.Result (ctxt', st'), _) =>
            let val new_goals = Thm.prems_of st'
             in report (Goals (SOME new_goals))
              ; (ctxt', HHF (protect_goals st', facts) :: L)
            end
         | SOME (Seq.Error E, _) => raise OPR_FAIL (PROOF_FAIL, E ()) )
  | raw_apply _ _ _ _ = raise BROKEN_INVARIANT

fun apply' report tac timeout s = maintain (raw_apply report tac timeout s)

fun apply tac time s = apply' (get_reporter()) tac time s
      handle Timeout.TIMEOUT _ => raise OPR_FAIL (PROOF_FAIL, "Timeout")

fun apply_method using meth timeout s = apply (meth using) timeout s


fun record_history name (s,his,ID) = (s, Symtab.update (name,s) his,ID)
fun restore_history name (_,his,ID) =
    case Symtab.lookup his name
      of NONE => raise OPR_FAIL (INVALID_OPR, "history " ^ name ^ " not found")
       | SOME s => (s, his,ID)

fun SKIP_SUCCESS F (SK as (_, HHF (st,_) :: _)) =
        if Thm.no_prems st then SK else F SK
  | SKIP_SUCCESS F SK = F SK

fun OPR_NO_INCR (f : stack -> stack) ((S,TAB,ID) : state) : state
  = (f S, TAB, ID)
fun OPR (f : stack -> stack) ((S,TAB,ID) : state) : state
  = (f S, TAB, ID+1)
fun OPR_ID (f : int -> stack -> stack) ((S,TAB,ID) : state) : state
  = (f ID S, TAB, ID+1)

fun CONTEXTUAL_CMD (parser : Proof.context -> command)
                   (toks : Token.src)
  = ((fn (s:state) => fst (parser (#1 (#1 s)) toks) s), [])


val VARS_KWD = (Parse.$$$ "VARS" || Parse.$$$ "vars")
val OPT_VARS = Scan.option (VARS_KWD |-- Parse.and_list (Scan.repeat1 (Parse.maybe Parse.name)) >> flat)
val VARS = VARS_KWD |-- Parse.and_list (Scan.repeat1 Parse.binding) >> flat
val IN = (Parse.$$$ "IN" || Parse.$$$ "in")




(*fun INTRO_ALL (ctxt, HHF (st, facts) :: L) = *)


(** APPLY **)

val mini_single_cmd_timeout = Attrib.setup_config_int \<^binding>\<open>mini_single_cmd_timeout\<close> (K 15000)

fun gen_APPLY prep_thms timeout using text =
      OPR (fn SK as (ctxt, _) =>
        apply_method (prep_thms ctxt using) (Method.evaluate text ctxt) timeout SK)
val APPLY   = gen_APPLY (K I)
val APPLY'' = gen_APPLY Attrib.eval_thms

val APPLY_CMD = (Method.parse -- Scan.optional WITH_CLAUSE [])
             >> (fn ((m,_),using) => fn s =>
                let val timeout = Config.get (context_of s) mini_single_cmd_timeout
                               |> Time.fromMilliseconds
                 in APPLY'' (SOME timeout) using m s
                end )

(** UNFOLD **)

fun UNFOLD' prep_thms raw_defs (ctxt, HHF (st, items) :: S) =
  let val defs = prep_thms ctxt raw_defs
      val st' = Local_Defs.unfold_goals ctxt defs st
   in (ctxt, HHF (st', items) :: S)
   |> report_goal
  end
  | UNFOLD' _ _ _ = raise BROKEN_INVARIANT

fun UNFOLD_FACT' prep_thms raw_defs fact_names (ctxt, SK as HHF (st, items) :: S) =
  let val defs = prep_thms ctxt raw_defs
      val fact_names = if member (op =) fact_names "*"
                       then collect_context (print_stack SK)
                         |> #2
                         |> map (#1 #> simp_name)
                       else fact_names
      val facts = map ( Proof_Context.get_thms ctxt
                     #> map ( Local_Defs.unfold ctxt defs ) ) fact_names
   in ctxt
   |> Proof_Context.note_thmss "" ( map (rpair [] o Binding.name) fact_names
                                      ~~ map (single o rpair []) facts)
   |-> (fn new_facts =>
     rpair (HHF (st, cat_items ([], map (apsnd (map Thm.prop_of)) new_facts) items) :: S))
  end
  | UNFOLD_FACT' _ _ _ _ = raise BROKEN_INVARIANT

val UNFOLD = OPR o UNFOLD' (K I)
val UNFOLD_CMD = Parse.thms1 -- Scan.option (IN |-- Scan.repeat1 Parse.name) >> (
      fn (defs, NONE)       => OPR (UNFOLD' Attrib.eval_thms defs)
       | (defs, SOME facts) => OPR (UNFOLD_FACT' Attrib.eval_thms defs facts) )


(** INITIATION PROCESS **)

(* Flexible Type *)

(*either ["", "no_typ", "flexible"]*)

fun typ_parsing ctxt terms =
  let fun filter_out_typ (Const ("_type_constraint_", _) $ X) = X
        | filter_out_typ (origin as (A $ B)) =
            let val A' = filter_out_typ A
                val B' = filter_out_typ B
             in if pointer_eq (A, A') andalso pointer_eq (B, B')
              then origin
              else A' $ B'
            end
        | filter_out_typ (origin as (Abs (N,T,X))) =
            let val X' = filter_out_typ X
             in if pointer_eq (X, X')
              then origin
              else Abs (N,T,X')
            end
        | filter_out_typ X = X
   in case Config.get ctxt typ_parsing_mode
   of "" => terms
    | "no_typ" => map filter_out_typ terms
    | "flexible" =>
        let val ctxt't = Config.put typ_parsing_mode "" ctxt
         in if can (Syntax.check_terms ctxt't) terms
           then terms
           else map filter_out_typ terms
        end
    | wrong => error ("Minilang.mini_typ_mode must be either [\"\", \"no_typ\", \"flexible\"] but " ^
                      wrong ^ " is given.")
  end

(*...*)

fun NEED_STANDARD (ctxt, HHF (st, _) :: _) = Phi_Sledgehammer_Solver.need_standard_tac ctxt st
  | NEED_STANDARD _ = false

fun TRY_STANDARD SK =
  if NEED_STANDARD SK
  then apply' (K ()) (CONTEXT_TACTIC (Classical.standard_tac (#1 SK) [])) NONE SK
  else SK

val INTRO = OPR oo INTRO'
val INTRO_CMD = OPT_VARS >> (OPR o INTRO' SINGLE_GOAL)
val INTRO_ALL_CMD = OPT_VARS >> (OPR o INTRO' ALL_SUBGOALS)

local
(*
fun read_trrules thy raw_rules =
  let
    val ctxt = Proof_Context.init_global thy;
    val read_root =
      #1 o dest_Type o Proof_Context.read_type_name {proper = true, strict = false} ctxt;
  in
    raw_rules
    |> map (Syntax.map_trrule (fn (r, s) => Syntax_Phases.parse_ast_pattern ctxt (read_root r, s)))
  end;

val trrules = read_trrules \<^theory> [
      Syntax.Parse_Rule (("logic", "(a \<le> b) \<le> c"), ("logic", "a \<le> b \<and> b \<le> c")),
      Syntax.Parse_Rule (("logic", "(a < b) < c"), ("logic", "a < b \<and> b < c")),
      Syntax.Parse_Rule (("logic", "a = b = c"), ("logic", "a = b \<and> b = c")),
      Syntax.Parse_Rule (("logic", "a \<longleftrightarrow> b \<longleftrightarrow> c"), ("logic", "a \<longleftrightarrow> b \<and> b \<longleftrightarrow> c"))
  ]
*)

val term_qchk = exists_subterm (
      fn Const(\<^const_name>\<open>less\<close>, _) $ (Const(\<^const_name>\<open>less\<close>, _) $ _ $ _) $ _ => true
       | Const(\<^const_name>\<open>less_eq\<close>, _) $ (Const(\<^const_name>\<open>less_eq\<close>, _) $ _ $ _) $ _ => true
       | Const("HOL.eq", _) $ (Const("HOL.eq", _) $ _ $ _) $ _ => true
       | Const("HOL.iff", _) $ _ $ (Const("HOL.iff", _) $ _ $ _) => true
       | _ => false )


fun term_check tm =
  if term_qchk tm
  then let
      fun maptm (Const(\<^const_name>\<open>less\<close>, _) $ (Const(\<^const_name>\<open>less\<close>, T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const(\<^const_name>\<open>less\<close>, T1) $ A $ B)
                          $ (Const(\<^const_name>\<open>less\<close>, T1) $ B $ C)
        | maptm (Const(\<^const_name>\<open>less_eq\<close>, _) $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ A $ B)
                          $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ B $ C)
        | maptm (Const("HOL.eq", _) $ (Const("HOL.eq", T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const("HOL.eq", T1) $ A $ B)
                          $ (Const("HOL.eq", T1) $ B $ C)
        | maptm (Const("HOL.iff", _) $ (Const("HOL.iff", T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const("HOL.iff", T1) $ A $ B)
                          $ (Const("HOL.iff", T1) $ B $ C)
        | maptm (origin as (A $ B)) =
            let val A' = maptm A
                val B' = maptm B
             in if pointer_eq (A', A) andalso pointer_eq (B', B)
                then origin
                else A' $ B'
            end
        | maptm (origin as Abs (N,T,X)) =
            let val X' = maptm X
             in if pointer_eq (X', X)
                then origin
                else Abs (N, T, X')
            end
        | maptm X = X
   in maptm tm
  end
  else tm

in

fun INIT_SYNTAX ctxt = ctxt
  |> Proof_Context.notation false Syntax.mode_default [
      (Const (\<^const_name>\<open>less_eq\<close>, dummyT), Mixfix (Input.string "(_/ \<le> _)", [51, 51], 50, Position.no_range)),
      (Const (\<^const_name>\<open>less\<close>,    dummyT), Mixfix (Input.string "(_/ < _)",     [51, 51], 50, Position.no_range))
    ]
  |> Proof_Context.notation true Syntax.mode_default [
      (Const (\<^const_name>\<open>less_eq\<close>, dummyT), Mixfix (Input.string "(_/ \<le> _)", [50, 51], 50, Position.no_range)),
      (Const (\<^const_name>\<open>less\<close>,    dummyT), Mixfix (Input.string "(_/ < _)",     [50, 51], 50, Position.no_range))
    ]
  |> Context.proof_map (
        Syntax_Phases.term_check ~200  "a < b < c" (K (map term_check)))

end


(* INIT *)

fun init_ctxt c st = c
  |> IPS_Data.put (
        (0, 0, Hasher.term (Thm.prop_of st))
      )
  |> Context.proof_map (
        Syntax_Phases.term_check ~10000 "minlang-flexible-typ" typ_parsing
    )

val install_relaxed_typ_parsing = Syntax_Phases.term_check ~10000 "minlang-flexible-typ" typ_parsing

fun INIT c st =
  let val facts = Proof_Context.facts_of c
      val facts' = if can Local_Theory.assert c
                   then Proof_Context.facts_of (Local_Theory.target_of c)
                   else Global_Theory.facts_of (Proof_Context.theory_of c)
      val local_facts =
        Facts.dest_static false [facts'] facts
          |> map (apsnd (map Thm.prop_of))

      val (vars, _) = Variable.constraints_of c
      val vars' = Vartab.fold (fn ((N,~1),T) => (fn L => (N,T) :: L)
                                | _ => I) vars []
      val st' = init_goal c st
   in ((init_ctxt c st, [HHF (st', (vars',local_facts)), ENDBLK T_END]), Symtab.empty, 0)
  end

fun INIT'  st = INIT (Proof.context_of st) (#goal (Proof.simple_goal st))

(** Crush **)

val crush_timeout = Attrib.setup_config_int \<^binding>\<open>crush_timeout\<close> (K 3) (*in seconds*)

fun SIMP' _ _ (ctxt, []) = (ctxt, [])
  | SIMP' prep_with raw_with_lems SK0 =
    TRY_STANDARD SK0 |> (fn (s as (ctxt, _)) =>
  let val with_lems = prep_with ctxt raw_with_lems
      val ctxt = apply_WITH with_lems ctxt
      val time = Config.get ctxt crush_timeout
              |> Time.fromSeconds
   in
   (( raw_apply (K ()) (CONTEXT_TACTIC (Clasimp.auto_tac ctxt)) (SOME time) s
      handle Timeout.TIMEOUT _ => 
      raw_apply (K ()) (CONTEXT_TACTIC (Clasimp.clarsimp_tac ctxt 1)) (SOME time) s)
      handle OPR_FAIL E =>
                (case s of (_, HHF (st, _) :: _) =>
                                if need_intro st orelse NEED_STANDARD SK0
                                then s
                                else raise OPR_FAIL E
                         | _ => raise OPR_FAIL E )
           | Timeout.TIMEOUT _ =>
                raise OPR_FAIL (PROOF_FAIL, "Timeout"))
  end)

fun CRUSH' prep_with (vars, raw_with_lems) SK0 =
     SIMP' prep_with raw_with_lems SK0
  |> SKIP_SUCCESS (INTRO' ALL_SUBGOALS vars)
  |> report_goal


val SIMP   = OPR o (report_goal oo SIMP'  (K I))
val SIMP'' = OPR o (report_goal oo SIMP'  read_with)
val CRUSH  = OPR o (CRUSH' (K I))

val SIMP_CMD  = with_parser >> SIMP''
val CRUSH_CMD = ( OPT_VARS -- with_parser )
             >> (OPR o CRUSH' read_with)

(** INDUCT & CASE **)

fun powerful_MP ctxt rule thA0 =
  let
    fun protect_prop ctxt ctm = let open Conv
       in case Thm.term_of ctm
           of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
                (arg_conv (abs_conv (protect_prop o snd) ctxt)) ctm
            | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
                (combination_conv (arg_conv (rewr_conv Thms.prop_def'sym))
                                  (protect_prop ctxt) ctm)
            | _ => Conv.all_conv ctm
      end
    val thA = Conv.fconv_rule (protect_prop ctxt) thA0
  in rule
  |> Conv.fconv_rule (Conv.arg1_conv (protect_prop ctxt))
  |> (Thm.biresolution (SOME ctxt) true [(false, thA)]
        THEN_ALL_NEW Thm.assumption (SOME ctxt)) 1
  |> Seq.pull
  |> (fn SOME (ret, _) => ret
       | NONE => error "BUG: CASES' MP")
 end

fun make_case term =
  let val (vars, prems, concl) = strip_meta_hhf term
      val vars' = Name.variant_list [] (map fst vars) ~~ map snd vars
      val fixes = map (apfst Binding.name) vars
      val assms = map_index (fn (i, tm) =>
                    ("prem" ^ string_of_int i, [fold_rev Term.abs vars' tm])) prems
      val binds = [((Rule_Cases.case_conclN, 0),
                   SOME (fold_rev Term.abs vars' (HOLogic.dest_Trueprop concl)))]
   in Rule_Cases.Case {
        fixes=fixes, assumes=assms, binds=binds, cases=[]
    }
  end


fun CASES' diff ADDITIONAL_NOTES tac first_vars (SK as (ctxt0, HHF (st00, items00) :: _)) =
  apply' (get_reporter()) tac NONE SK
    |> (fn (ctxt, SK as HHF (rule, items0) :: REMAIN_SK) =>
   let val cases0 = Proof_Context.dest_cases (SOME ctxt0) ctxt
                |> filter (fn (_, Rule_Cases.Case {binds,...}) =>
                      forall (fn ((name,_), SOME term) =>
                                    name <> Rule_Cases.case_conclN orelse
                                    (case term of Const(\<^const_name>\<open>HOL.induct_true\<close>, _) => false
                                                | Const(\<^const_name>\<open>HOL.True\<close>, _) => false
                                                | _ => true)
                               | _ => true) binds)
       val diffxxx = (num_goals_of' rule - num_goals_of' st00 + 1 + diff) - length cases0
       val cases =
               if diffxxx = 0
               then cases0
               else if diffxxx > 0
               then let
                    val additional = drop (length cases0) (goals_of' rule)
                                  |> map_index (fn (i,x) =>
                                        ("Prem" ^ string_of_int i, make_case x))
                 in cases0 @ additional
                end
               else error "BUG REWLK"
       val used_qualifiers = quanlifiers_of (print_stack SK)
       val cases = Name.variant_list used_qualifiers (map #1 cases)
                ~~ map #2 cases

       fun is_case x t =
            x = Rule_Cases.case_conclN andalso not (Term.exists_subterm Term.is_Var t)
       fun goal_term_of ctxt binds =
            if exists (fn ((x, _), SOME t) => is_case x t | _ => false) binds
            then Vartab.lookup (Variable.binds_of ctxt) (Rule_Cases.case_conclN, 0)
                  |> (fn SOME (\<^Type>\<open>bool\<close>, goal) => HOLogic.mk_Trueprop goal
                       | _ => error "BUG 0ejOD0qNRfaTJCrbK7lH3w")
            else fst (Logic.dest_implies (Thm.prop_of st00))

       val siblings = map (fn (_, kase as Rule_Cases.Case {fixes, binds, ...}) =>
              let val (asms, ctxt) = Proof_Context.apply_case kase ctxt
               in PROP ((map (apfst Binding.name_of) fixes, asms), goal_term_of ctxt binds)
              end
            ) cases

       fun CB initial rule cases siblings
              ctxt' (lem, _, SK, param) =
        let val rule' =
                if initial then rule
                else let val thA = lem
                                |> is_protected (Thm.prop_of lem) ? Goal.conclude
                                |> singleton (Proof_Context.export ctxt' ctxt)
                  in thA
                  |> not initial ? ( powerful_MP ctxt rule
                                  #> not (null cases) ? conclude_goal )
                 end
         in case cases
         of [] =>
            (ctxt, HHF (rule', items0) :: SK)
          | ((name, kase) :: remaining_cases) =>
        let val opt_case_name = case param of CASE_NAME param => param
                                            | NO_PARAM => NONE
                                            | _ => raise BROKEN_INVARIANT
            (* val name = if Char.isAlpha (String.sub (name, 0)) then name
                       else "case_" ^ name *)
            val kase = case kase
                  of Rule_Cases.Case {fixes, assumes, binds, cases} =>
                     Rule_Cases.Case {
                       fixes = (
                         case opt_case_name
                           of SOME fixes'0 =>
                              let val fixes' = if member (op =) ["COMPLETE_NEXT", "RELAXED"]
                                                                 (Config.get ctxt working_mode)
                                               then take (length fixes) fixes'0
                                               else fixes'0
                               in map2_opt (fn NONE => I
                                             | SOME name => fn (_, T) => (Binding.name name, T)
                                           ) fixes' fixes
                                  handle ListPair.UnequalLengths =>
                                      raise OPR_FAIL (INVALID_OPR, "Incorrect number of VARS")
                              end
                            | _ => fold_map (fn (B,T) => fn names =>
                              let val name = Binding.name_of B
                                  val name = if Name.is_internal name then Name.dest_internal name
                                                                      else name
                                  (*val (name, names) = if name = ""
                                                      then Name.variant "case" names
                                                      else (name, names)*)
                                  (*val (name, names) = Name.variant name names*)
                               in ((Binding.name name,T), names)
                              end ) fixes (Variable.names_of ctxt)
                              |> #1 ),
                       assumes = map_index (fn (i,(N,tms)) =>
                                    if N = "" then ("prem" ^ string_of_int i, tms)
                                              else (N, tms) ) assumes,
                       binds=binds,
                       cases=cases
                     }

            val Rule_Cases.Case {fixes, cases, binds, ...} = kase
            val _ = if null cases then () else error "XQY: Unsupported! #1"

            
            val (asms, ctxt) = Proof_Context.apply_case kase ctxt

            val goalx =
               (if exists (fn ((x, _), SOME t) => is_case x t | _ => false) binds
                then Vartab.lookup (Variable.binds_of ctxt) (Rule_Cases.case_conclN, 0)
                  |> (fn SOME (\<^Type>\<open>bool\<close>, goal) => HOLogic.mk_Trueprop goal
                       | _ => error "BUG 0ejOD0qNRfaTJCrbK7lH3w")
                  |> Thm.cterm_of ctxt
                else Thm.cprop_of st00
                  |> Thm.dest_arg1)
                  |> Goal.init

            val binding = Binding.name (variant_factname ctxt name)
            val bindings = map (rpair [] o Binding.qualify_name true binding o fst) asms

            fun export is_G asms =
                let val (A,B) = Assumption.assume_export is_G asms
                 in (A #> Thm.permute_prems 0 (length asms) ,B)
                end
         in ctxt
         |> fold_burrow ( Assumption.add_assms export
                        o map (Thm.cterm_of ctxt) ) (map #2 asms)
         |-> (fn thms => fn ctxt =>
           let val tagged = maps (filter (is_tagged_Trueprop o Thm.prop_of)) thms
               val thms  = map ( filter_out (is_tagged_Trueprop o Thm.prop_of)
                              #> map (unwrap_tags ctxt) ) thms
               val pairs = bindings ~~ thms
               val notes = pairs
                        |> filter_out (null o snd)
                        |> map (apsnd (map (fn th => ([remove_TAG_premises ctxt th], []))))
            in ctxt
            |> not (null pairs) ?
               ( Proof_Context.note_thms "" ((binding,[]), [(maps snd pairs,[])]) #> snd)
            |> Proof_Context.note_thmss "" (ADDITIONAL_NOTES ctxt tagged @ notes)
           end )
         |-> (fn thms0 =>
        let val thms = map (apfst simp_name) thms0
            val items' = ( map (apfst Binding.name_of) fixes,
                           map (apfst simp_name o apsnd (map Thm.prop_of)) thms )
            val report = get_reporter ()
            fun PRT _ T = case siblings
                            of [_] => cat_tree T (print_stack [HHF (st00, items00)])
                             | _ => cat_tree (BUNDL (empty_items, T :: tl siblings))
                                             (print_stack [HHF (st00, items00)])
         in report (New_Items items')
          ; report (Consider_Case (Binding.name_of binding))
          ; if null remaining_cases
         then rpair ( HHF (goalx, items')
                 :: MAGIC (CB false rule' remaining_cases (tl siblings), PRT, NO_PARAM)
                 :: SK)
         else rpair ( HHF (goalx, items')
                 :: ENDBLK T_NXT
                 :: MAGIC (CB false rule' remaining_cases (tl siblings), PRT, NO_PARAM)
                 :: SK)
        end )
        end
        end
    in CB true rule cases siblings
          ctxt (Drule.dummy_thm, ([],[]), REMAIN_SK, CASE_NAME first_vars)
   end
     | _ => raise BROKEN_INVARIANT)
  | CASES' _ _ _ _ _ = raise BROKEN_INVARIANT

(* Syntax *)



exception IH_MAP of (string * string list) list

val induct_auto_use_facts = Attrib.setup_config_bool \<^binding>\<open>induct_auto_use_facts\<close> (K false)

fun INDUCT' (no_simp, (insts, ((arbitrary, taking), opt_rule))) first_vars using (ctxt, SK) =
  let val (tamper_facts, tamper_fact') =
        if Config.get ctxt induct_auto_use_facts
        then let
            val (_, facts, _) = collect_context (print_stack SK)
            val facts = map (fn (name, _) => (name, Proof_Context.get_thms ctxt name)) facts
            
            val dirty_frees = fold (fold (fn NONE => I
                                           | SOME (_, (X, _)) => Term.add_frees X)) insts []
                           |> fold (curry (merge (op =))) arbitrary
            val dirty = member (op =) dirty_frees
      
            val tamper_facts = map (apsnd (map (` ( Term.exists_subterm (fn Free f => dirty f
                                                                          | _ => false)
                                                  o Thm.prop_of)))) facts
                            |> filter (exists fst o snd)
         in (tamper_facts,
             maps (map_filter (fn (true, x) => SOME x | _ => NONE) o snd) tamper_facts)
        end
        else ([], [])

      val IH_map = Unsynchronized.ref []
      val diff = case opt_rule of NONE => 0
                    | SOME rules => length rules - 1
      fun tac (ctxt, st) =
        let val st' = pop_n_goals (diff + 1) st
         in induction_tac IH_map (not no_simp) insts arbitrary taking opt_rule
              (if null using
               then if null tamper_fact' then [] else [wraps ctxt tamper_fact']
               else using) 1 (ctxt, st')
        end

      fun update_tampered ctxt th =
        let val ths = unwrap_conjs ctxt th
                   |> map (unwrap_tags ctxt)
            fun burrow' [] _ = []
              | burrow' ((true , _ ) :: L) (th::ths) = th :: burrow' L ths
              | burrow' ((false, th) :: L) (    ths) = th :: burrow' L ths
              | burrow' _ _ = error "BUG"
            fun burrow'2 [] ths = ths
              | burrow'2 ((true , _) :: L) (_ ::ths) = burrow'2 L ths
              | burrow'2 ((false, _) :: L) (    ths) = burrow'2 L ths
              | burrow'2 _ _ = error "BUG"
            fun burrow [] [] = []
              | burrow ((N, L) :: L') ths = (N, burrow' L ths) :: burrow L' (burrow'2 L ths)
              | burrow _ _ = error "BUG"
            val tamper_facts'' = burrow tamper_facts ths
         in map (fn (B,ths) => ((mk_binding B, []), [(ths,[])]) ) tamper_facts''
        end
      val ret = CASES' diff (maps o update_tampered) tac first_vars (ctxt, SK)
   in get_reporter () (Internal (IH_MAP (!IH_map)))
    ; ret
  end

fun CASE_SPLIT' (no_simp, (insts, opt_rule)) vars facts =
  let (* val facts' = if (* not (null (flat insts)) orelse *) is_some opt_rule then [] else facts *)
      val facts' = facts
      val tac = Induct.cases_context_tactic (not no_simp) insts opt_rule facts' 1
   in CASES' 0 (K (K [])) tac vars
  end

val INDUCT = OPR ooo INDUCT'
fun INDUCT'' (args, vars, raw_using) s =
  let val ctxt = context_of s
      val toks = if \<^try>\<open>Token.is_eof (List.last args) catch _ => false\<close>
                 then args
                 else args @ [Token.eof]
      val (args', _) = ind_synt (Context.Proof ctxt) toks
      val using = Attrib.eval_thms ctxt raw_using
   in OPR (INDUCT' args' vars using) s
  end
val INDUCT_CMD = CONTEXTUAL_CMD (fn ctxt =>
         ind_synt (Context.Proof ctxt) -- OPT_VARS -- Scan.optional WITH_CLAUSE []
      >> (fn (((no_simp, (insts, ((arbitrary, taking), opt_rule))), vars), raw_using) =>
        let val using = Attrib.eval_thms ctxt raw_using
         in INDUCT (no_simp, (insts, ((arbitrary, taking), opt_rule))) vars using
        end ))

val CASE_SPLIT = OPR ooo CASE_SPLIT'
val CASE_SPLIT_CMD = CONTEXTUAL_CMD (fn ctxt =>
         case_synt (Context.Proof ctxt) -- OPT_VARS -- Scan.optional WITH_CLAUSE []
      >> (fn (((no_simp, (insts, opt_rule)), vars), raw_facts) =>
        let val facts = Attrib.eval_thms ctxt raw_facts
         in CASE_SPLIT (no_simp, (insts, opt_rule)) vars facts
        end ) )
fun CASE_SPLIT'' (args, vars, raw_facts) s =
  let val ctxt = context_of s
      val toks = if \<^try>\<open>Token.is_eof (List.last args) catch _ => false\<close>
                 then args
                 else args @ [Token.eof]
      val (args', _) = case_synt (Context.Proof ctxt) toks
      val facts = Attrib.eval_thms ctxt raw_facts
   in OPR (CASE_SPLIT' args' vars facts) s
  end


(** RULE **)

fun RULE' [] raw_facts (SK as (ctxt, _)) =
    let val facts = Attrib.eval_thms ctxt raw_facts
     in apply' (get_reporter())
               (CONTEXT_TACTIC (Classical.standard_tac (#1 SK) facts)) NONE SK
    end
 (* if NEED_STANDARD SK
    then TRY_STANDARD SK
    else let val facts = Attrib.eval_thms ctxt raw_facts
     in RULE'_i [] facts SK
    end *)
  | RULE' raw_rules raw_facts (ctxt, HHF (st, items) :: SK) =
    let val facts = Attrib.eval_thms ctxt raw_facts

        fun transpose [] [] = []
          | transpose nxt [] = transpose [] (rev nxt)
          | transpose nxt ([] :: L) = transpose nxt L
          | transpose nxt ((x :: L) :: L') = x :: transpose (L :: nxt) L'
        val rules = maps (fn raw_rule =>
              let val name = name_of_ref (fst raw_rule)
               in map (fn rule0 =>
                    let open Phi_Sledgehammer_Solver
                        val rule = rule0 OF facts
                        fun try_drule rule =
                         (case try Tactic.make_elim rule
                            of SOME rule' => [(true, rule')]
                             | NONE => [])
                     in case infer_type_of_rule name rule
                     of T_ELIM => [(true, rule)]
                      | T_DEST => (case try Tactic.make_elim rule
                                     of SOME rule => [(true, rule)]
                                      | NONE      => [(false, rule)])
                      | T_UNKNOWN =>
                            if Thm.nprems_of rule = 1
                            then [(false, rule)] @ try_drule rule
                            else [(false, rule)]
                      | _      => [(false, rule)]
                    end
                    handle THM _ => []
                  ) (Attrib.eval_thms ctxt [raw_rule])
              end ) raw_rules
          |> transpose []
     in st
     |> Thm.biresolution NONE false rules 1
     |> Seq.map Thm.solve_constraints
     |> Seq.pull
     |> (fn SOME (st', _) =>
              let val new_goals = Thm.prems_of st'
               in get_reporter () (Goals (SOME new_goals))
                ; (ctxt, HHF (protect_goals st', items) :: SK)
              end 
          | NONE => raise OPR_FAIL (PROOF_FAIL, "Fail to apply the rules" ))
     |> maintain
    end
  | RULE' _ _ _ = raise BROKEN_INVARIANT

val RULE = OPR oo RULE'
val RULE_CMD = let open Parse
      in Scan.optional thms1 []
      -- Scan.optional (($$$ "with" || $$$ "WITH") |-- thms1) [] >> uncurry RULE
     end


(** HAVE **)

(*
fun HAVE'' _ _ _ (ctxt, []) = (ctxt, [])
  | HAVE'' AP raw_name expr (ctxt, HHF (G,items) :: S) =
      let val SOME (_, jj, _) = IPS_Data.get ctxt
          val name = Option.map (fn (name, raw_attrs) =>
                        (Binding.name name,
                         raw_attrs |> map ( Attrib.check_src ctxt
                                         #> Attrib.attribute ctxt ) ) ) raw_name
                  |> (fn SOME some => some
                       | NONE => let val b = Binding.name ("fact" ^ string_of_int (!jj))
                                     val _ = (jj := !jj + 1)
                                  in (b, [])
                                 end)
          val goal_term = Syntax.read_prop ctxt expr
          val goal = Goal.init (Thm.cterm_of ctxt goal_term)
          fun CB ctxt' (st',(*items'*) _,S, _) =
            let val lem = Goal.conclude st'
                       |> singleton (Proof_Context.export ctxt' ctxt)
             in AP (ctxt,name,items,G,S,lem)
            end
          fun PRT _ t = BUNDL (items, [t, print_stack [HHF (G,([],[]))]])
       in (ctxt, HHF (goal, ([],[])) :: ENDBLK T_END :: MAGIC (CB, PRT, NO_PARAM) :: S)
      end
  | HAVE'' _ _ _ _ = raise BROKEN_INVARIANT

val HAVE' = HAVE'' (fn (ctxt,name,items,st,S,lem) =>
  let val lems = elim_conjs ctxt lem
      val ((name,lems), ctxt'') = Proof_Context.note_thms "" (name, [(lems,[])]) ctxt
   in (ctxt'', HHF (st, cat_items ([], [(name, map Thm.prop_of lems)]) items) :: S)
  end)

val HAVE = OPR oo HAVE'

val HAVE_CMD =
        Scan.option (Parse.name -- Parse.opt_attribs --| \<^keyword>\<open>:\<close>) --
        Parse.term
     >> (fn (name, expr) => HAVE name expr)
*)

fun gen_HAVE' mkG shows (ctxt0, HHF (st,items) :: S) =
      let val s01 = mkG ctxt0
          val ctxt01 = Proof.context_of s01
          val goal = #goal (Proof.goal s01)
                  |> init_goal ctxt01                  

          val binds = map (apsnd (map (Attrib.attribute_cmd ctxt0)) o fst) shows
          fun CB ctxt' (st',(*items'*) _,S, _) =
            let val lems = Goal.conclude st'
                        |> finalize_goal ctxt'
                        |> Conjunction.elim_conjunctions
                        |> Proof_Context.export ctxt' ctxt0
                        |> unflat (map snd shows)
                val (lems, ctxt02) = Proof_Context.note_thmss "" (binds ~~ map (fn x => [(x, [])]) lems) ctxt0
                val ctxt03 = Proof_Context.auto_bind_facts (maps (map Thm.prop_of o snd) lems) ctxt02
                val items' = ([], map (apsnd (map Thm.prop_of)) lems)
             in get_reporter () (New_Items items')
              ; (ctxt03, HHF (st, cat_items items' items) :: S)
            end

          val thy01 = Proof_Context.theory_of ctxt01
          val preruns = concl_of (Thm.prop_of goal)
                  |> Logic.dest_conjunctions
                  |> filter_out (fn Const(\<^const_name>\<open>Pure.term\<close>, _) $ _ => false
                                  | _ => true)
                  |> map (Skip_Proof.make_thm thy01)
                  |> unflat (map snd shows)
          val (fakes, _) = Proof_Context.note_thmss "" (binds ~~ map (fn x => [(x, [])]) preruns) ctxt0
          val items' = ([], map (apsnd (map Thm.prop_of)) fakes)

          fun PRT _ t = BUNDL (items, [BLOCK t, print_stack [HHF (st, items')]])
       in (ctxt01, HHF (goal, ([],[])) :: ENDBLK T_END :: MAGIC (CB, PRT, NO_PARAM) :: S)
      end
  | gen_HAVE' _ _ _ = raise BROKEN_INVARIANT

fun gen_HAVE mkspec fixes assumes shows =
  OPR (fn (ctxt, SK) =>
    let val delta = fold (fn ((B,_),_) => fn N =>
                            if Binding.is_empty B then (N+1) else N
                         ) shows 0
        val (i', ctxt') = incr_fact_counter delta ctxt
        val i = Unsynchronized.ref i'
        fun mkB () = let val j = !i
                      in i := j + 1
                       ; Binding.name ("fact" ^ string_of_int j)
                     end
        val shows' = map (fn origin as ((B,atts),props) =>
                            if Binding.is_empty B then ((mkB(),atts),props) else origin ) shows
     in gen_HAVE' (mkspec false "" NONE (K I) Binding.empty_atts []
                  [Element.Fixes fixes, Element.Assumes assumes] (Element.Shows shows) false)
                  shows' (ctxt', SK)
    end )

val HAVE   = gen_HAVE Specification.schematic_theorem_cmd
val HAVE'' = gen_HAVE Specification.schematic_theorem

val HAVE_CMD =
        Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
     >> (fn ((shows, assumes), fixes) =>
          tolerate_typ (HAVE fixes assumes shows)
                       (fn s => HAVE fixes (remove_typ_ass assumes) (remove_typ_ass shows) s) )

(** CONSIDER **)

fun atomize_term ctxt =
      Object_Logic.atomize_term ctxt
  #> (fn X => if Term.fastype_of X = \<^Type>\<open>bool\<close>
              then X
              else raise OPR_FAIL (INVALID_OPR, "Fail to atomize the proposition into HOL"))

(*can be cached*)
fun mk_consider_rule ctxt DNF_SPEC =
  let fun var TS name =
        let val EN = length TS
         in Var((name,0), (map #2 TS) ---> \<^Type>\<open>bool\<close>)
         |> fold (fn (i,_) => fn X => X $ Bound (EN - 1 - i)) TS
        end
      fun mk_conj_clause (ii, (EN,CN)) =
        let val TS = List.tabulate (EN, fn i =>
                      (i, TVar (("'x" ^ string_of_int ii ^ "'" ^ string_of_int i, 0), \<^sort>\<open>type\<close>)))
            val PS = List.tabulate (CN, fn i =>
                      var TS ("P"  ^ string_of_int ii ^ "'" ^ string_of_int i))
         in foldr1 (fn (A,B) => \<^Const>\<open>conj\<close> $ A $ B) PS
         |> fold_rev (fn (i,T) => fn X =>
                      \<^Const>\<open>Ex T\<close> $ Abs ("x" ^ string_of_int ii ^ "'" ^ string_of_int i, T, X)) TS
        end
      fun import_vars ctxt th =
        let val ((_, [th']), ctxt') = ctxt |> Variable.set_body false |> Variable.import true [th];
         in (ctxt', th')
        end
      val C = HOLogic.mk_Trueprop (var [] "C")
   in map_index mk_conj_clause DNF_SPEC
   |> foldr1 (fn (A,B) => \<^Const>\<open>disj\<close> $ A $ B)
   |> (fn X => Logic.mk_implies (HOLogic.mk_Trueprop X, C))
   |> Thm.cterm_of ctxt
   |> Thm.trivial
   |> import_vars ctxt
   |-> (fn ctxt' => fn th => th
   |> Seq.REPEAT (REPEAT_DETERM_SOME (Thm.biresolution NONE true
              [(true, Thms.exE), (true, Thms.conjE), (true, Thms.disjE)]))
   |> Seq.hd
   |> Thm.permute_prems 0 ~1
   |> singleton (Variable.export ctxt' ctxt))
  end

fun CONSIDER' raw_dnf (ctxt0, HHF (st0, items0) :: S) =
  let fun parse (raw_decls, (raw_fixes, raw_prems, raw_statements)) ctxt =
        let val raw_props = map snd raw_statements
      
            val binders = map fst raw_statements
                       |> map (apsnd (map ( Attrib.check_src ctxt
                                         #> Attrib.attribute ctxt )))

            val (ii,jj,ID) = IPS_Data.get ctxt
            val (binders, nn) =
                  fold_map (fn (B,AT) => fn N =>
                      if Binding.is_empty B
                      then ((Binding.name ("fact" ^ string_of_int N), AT), N+1)
                      else ((B,AT),N)) binders jj
            val ctxt = IPS_Data.put (ii,nn,ID) ctxt
      
            val ({vars, propss, binds, result_binds, ...}, params_ctxt) =
                    Proof_Context.read_stmt (raw_decls @ raw_fixes) (raw_prems @ raw_props) ctxt
            val (decls, fixes) = chop (length raw_decls) vars ||> map #2;
            val (premss, conclss) = chop (length raw_prems) propss;
            val propss' = (map o map) (Logic.close_prop fixes (flat premss)) conclss
                       |> flat
                       |> map (atomize_term ctxt)
            val AS = map (Thm.cterm_of ctxt o HOLogic.mk_Trueprop) propss'
      
            val goal = propss'
                    |> foldr1 (fn (A, B) => \<^Const>\<open>conj\<close> $ A $ B)
                    |> fold_rev (fn (_, t) => fn T =>
                          \<^Const>\<open>Ex \<open>Term.type_of (snd t)\<close>\<close> $ Term.lambda_name t T
                        ) decls
      
            val cparams = map (Thm.cterm_of params_ctxt o #2 o #2) decls
         in ((cparams,
             (length decls, length propss'),
             (decls,
              fixes,
              AS,
              raw_props,
              binds,
              binders),
             (goal,
              result_binds)),
             params_ctxt)
        end

      val (conj_clauses, params_ctxt) = fold_map parse raw_dnf ctxt0
      val rule0 = mk_consider_rule ctxt0 (map #2 conj_clauses)

      val goal0= map (#1 o #4) conj_clauses
              |> foldr1 (fn (A,B) => \<^Const>\<open>disj\<close> $ A $ B)
              |> (fn X => HOLogic.Trueprop $ X) 
      val _ = get_reporter () (Goals (SOME [goal0]))
      val goal = goal0
              |> Thm.cterm_of params_ctxt
              |> Goal.init
              |> singleton (Variable.export params_ctxt ctxt0)
      val goal_binds = map (#2 o #4) conj_clauses
              |> foldl1 (AList.merge (op =) (op aconv))
      val ctxt_rule = params_ctxt
                   |> fold Variable.bind_term goal_binds

      val subgoals = map (fn (_, _, (decls, fixes, AS, raw_props, _, binders), _) =>
              print_stack [HHF (st0, (  map (apsnd Term.fastype_of o snd) decls
                                      @ map (apsnd Term.fastype_of) fixes,
                                     map (Binding.name_of o fst) binders ~~
                                        (unflat raw_props (map Thm.term_of AS)) ))] ) conj_clauses
      fun PRT0 sgs _ t = BUNDL (items0, (case conj_clauses of [_] => BLOCK t | _ => t) :: sgs)
      fun CB _ _ [] _  _ = raise BROKEN_INVARIANT
        | CB initial sgs
             ((cparams, _, (decls, fixes, AS, raw_props, binds, binders), _) :: remain_clauses)
             ctxt' (lem, _, S, _) =
            let val rule' = lem
                         |> Goal.conclude
                         |> singleton (Proof_Context.export ctxt' ctxt0)
                         |> initial ? MP ctxt0 rule0
                fun export a b =
                    let val (A,B) = Obtain.obtain_export ctxt0 rule' cparams a b 
                        fun export_thm thm =
                          let val protected = is_protected (Thm.prop_of thm)
                           in thm
                           |> protected? Goal.conclude
                           |> A
                           |> protected? Goal.protect 0
                          end
                     in (export_thm,B)
                    end
                val (lems', ctxt'') = Proof_Context.add_fixes (map #1 decls) ctxt0
                                   |> snd
                                   |> fold (Variable.bind_term o apsnd (Logic.close_term fixes)) binds
                                   |> Assumption.add_assms export AS
                val lems'' = binders ~~ map (map (fn X => ([X],[]))) (unflat raw_props lems')
                val (new_facts, ctxt'3) = Proof_Context.note_thmss "" lems'' ctxt''
                val items_delt = (map (apsnd Term.fastype_of o snd) decls,
                                  map (apsnd (map Thm.prop_of)) new_facts)
                val items'3 = items_delt
                           |> null remain_clauses ? (fn X => cat_items X items0)
             in get_reporter () (New_Items items_delt)
              ; (ctxt'3, HHF (st0, items'3)
                          :: (case remain_clauses
                                of [] => S
                                 |  _ =>    ENDBLK T_NXT
                                         :: MAGIC (CB false (tl sgs) remain_clauses,
                                                   PRT0 (tl sgs),
                                                   NO_PARAM)
                                         :: S))
            end

   in (ctxt_rule,
          HHF (goal,([],[]))
       :: ENDBLK (case conj_clauses of [_] => T_END | _ => T_NXT)
       :: MAGIC (CB true subgoals conj_clauses, PRT0 subgoals, NO_PARAM) :: S)
  end
  | CONSIDER' _ _ = raise BROKEN_INVARIANT

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));

val CONSIDER = OPR o CONSIDER'
fun CONSIDER_CMD toks = (
     Parse.enum1 "|"
        (Scan.optional (Parse.vars --| Parse.where_) []
          -- structured_statement)
     >> (fn x =>
          tolerate_typ (CONSIDER x)
                       (fn s => CONSIDER (map (apsnd (fn (a,b,c) =>
                                  (a,remove_typ_ss b,remove_typ_ass c) )) x) s)
        )) toks

(** STEP, the alternative calculation mechanism **)

fun STEP' prep_term opt_rule raw_term (ctxt, HHF (st, items) :: SK) =
  let val term0 = prep_term ctxt raw_term
      val (opr, term) = case Term.fastype_of term0
                          of \<^Type>\<open>bool\<close> => (case term0 of opr $ _ $ RHS => (SOME opr, RHS)
                                               | _ => (NONE, term0))
                           | _ => (NONE, term0)
      val term = Thm.cterm_of ctxt term
      fun err () = raise OPR_FAIL (INVALID_OPR, "The goal is not about a known transitive operator")
      fun parse_opr (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = parse_opr X
        | parse_opr (C $ _ $ _) = C
        | parse_opr _ = err ()
      
     
      val i = Unsynchronized.ref (Thm.maxidx_of st)
      fun mk_i () = (i := !i + 1; !i)
      fun mkV () = TVar (("'a", mk_i()), [])
      val Y' = ("Y", mk_i())
      val (X,Y,Z) = ( Var(("X", mk_i()), mkV ())
                    , Var(Y', mkV ())
                    , Var(("Z", mk_i()), mkV ()) )
      fun erase (Free (N,_)) = Free (N, mkV ())
        | erase (Var  (N,_)) = Var  (N, mkV ())
        | erase (Const(N,_)) = Const(N, mkV ())
        | erase (X $ Y) = erase X $ erase Y
        | erase (Abs (N,_,X)) = Abs (N,  mkV (), erase X)
        | erase X = X
      val const = parse_opr (Thm.major_prem_of st)
               |> erase
      val opr' = case opr of SOME opr => erase opr | _ => const
      val pat = \<^Const>\<open>Pure.imp\<close> $ HOLogic.mk_Trueprop (opr' $ X $ Y)
                                $ (
                \<^Const>\<open>Pure.imp\<close> $ HOLogic.mk_Trueprop (const $ Y $ Z)
                                $ HOLogic.mk_Trueprop (const $ X $ Z) )
      val thy = Proof_Context.theory_of ctxt
      fun can_match tm = can (Pattern.match thy (pat, tm)) (Vartab.empty, Vartab.empty)

      val rules =
          case opt_rule
            of [] =>
             let 
              in Find_Theorems.find_theorems ctxt NONE NONE true [(true, Find_Theorems.Pattern pat)]
              |> snd
              |> filter (can_match o Thm.prop_of o snd)
              |> map_filter (fn (_, th) =>
                    let fun parse (Const(\<^const_name>\<open>Pure.imp\<close>, _)
                              $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (_ $ Var (X, _) $ _))
                              $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ _))
                                  = X
                          | parse (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = parse X
                          | parse (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = parse X
                          | parse _ = raise Fail ""
                     in try (Drule.infer_instantiate ctxt [(parse (Thm.prop_of th), term)]) th
                    end handle Fail _ => NONE )
             end
             | rule' =>
                Attrib.eval_thms ctxt rule'

      val st's = rules
             |> map_filter (fn th =>
                  Thm.biresolution (SOME ctxt) true [(false, th)] 1 st
                    |> Seq.pull
                    |> Option.map fst)
             |> distinct (Thm.equiv_thm thy)
      val st' = case st's
                  of st' :: _ => protect_goals st'
                   | [] => err ()
   in (Proof_Context.auto_bind_facts [term0] ctxt,
       HHF (st', items) :: SK)
  end
  | STEP' _ _ _ _ = raise BROKEN_INVARIANT

val STEP   = OPR oo STEP' (K I)
val STEP'' = OPR oo STEP' Syntax.read_term
val STEP_CMD = Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.thms1 --| \<^keyword>\<open>)\<close>) []
            -- Parse.term >> uncurry STEP''


(** HAMMER **)

fun conclude_SK (ctxt, HHF (st, itms) :: S) = (ctxt, HHF (conclude_goal st, itms) :: S)
  | conclude_SK _ = raise BROKEN_INVARIANT

exception SH_PRF of string
exception REPLACE_CMD of string * string

val enable_cache_by_step = Config.declare_bool ("enable_cache_by_step", \<^here>) (K true)

fun HAMMER_i override step_id (ctxt, HHF (s,facts) :: S) =
  let val (_, _, ID_BASE) = IPS_Data.get ctxt
      val ID = ID_BASE ^ "/" ^ step_id
      val ID' = if Config.get ctxt enable_cache_by_step
                then SOME ID
                else NONE
      val (prf, s') = Phi_Sledgehammer_Solver.auto true override ID' ctxt s
                      handle ERROR E => raise OPR_FAIL (PROOF_FAIL, E)
   in get_reporter () (Internal (SH_PRF prf))
    ; (ctxt, HHF (s', facts) :: S)
   |> maintain
  end
  | HAMMER_i _ _ _ = raise BROKEN_INVARIANT

(*
fun HAMMER_all override step_id =
  let val ID_BASE = step_id ^ "/"
      fun loop j (stack as (_, HHF (s,_) :: _)) =
        if no_goal' s then stack
        else HAMMER_i override (ID_BASE ^ string_of_int j) stack
          |> loop (j+1)
        | loop _ _ = raise BROKEN_INVARIANT
   in loop 0
  end
*)

fun HAMMER override = OPR_ID (HAMMER_i override o string_of_int)
val HAMMER_CMD = orverride_parser >> HAMMER

(** END **)

fun END' param SH_override jj ID (stack as (_, HHF _ :: _)) =
  let val ID_BASE = if jj = 0 then string_of_int ID 
                    else string_of_int ID ^ "+" ^ string_of_int jj
      val (ctxt, SK'1) = HAMMER_i SH_override ID_BASE stack
                      |> conclude_SK
      val st' = case SK'1 of HHF (st', _) :: _ => st'
                           | _ => raise BROKEN_INVARIANT
   in if no_goal' st'
    then case SK'1
      of HHF s :: ENDBLK T' :: SK' =>
        ( get_reporter () (Internal (REPLACE_CMD ("END", "END")))
        ; if T' = T_END then maintain (ctxt, HHF s :: SK')
          else if member (op =) ["COMPLETE_NEXT", "RELAXED"]
                                (Config.get ctxt working_mode)
          then maintain (ctxt, HHF s :: SK')
            |> END' param SH_override (jj+1) ID
          else raise OPR_FAIL (INVALID_OPR, 
                  "This block should be closed by the " ^
                  (case T' of T_END => "END" | T_NXT => "NEXT") ^
                  " command.") )
       | _ => raise BROKEN_INVARIANT
    else if member (op =) ["COMPLETE_NEXT", "RELAXED"]
                          (Config.get ctxt working_mode)
    then ( get_reporter () (Internal (REPLACE_CMD ("NEXT", "NEXT")))
         ; END' param SH_override (jj+1) ID (ctxt, SK'1) )
    else raise OPR_FAIL (INVALID_OPR, "This block should be closed by the NEXT command.")
  end
  | END' _ _ _ _ _ = raise BROKEN_INVARIANT

fun NXT' param SH_override ID (origin as stack as (_, HHF (st, _) :: _)) =
  let val ID_BASE = string_of_int ID
      val (ctxt, SK'1) = HAMMER_i SH_override ID_BASE stack
                      |> conclude_SK
      val st' = case SK'1 of HHF (st', _) :: _ => st'
                           | _ => raise BROKEN_INVARIANT
   in if no_goal' st'
    then case SK'1
      of HHF s :: ENDBLK T' :: SK' =>
        ( get_reporter () (Internal (REPLACE_CMD ("END", "END")))
        ; if T' = T_NXT
          then (case SK'
            of MAGIC (CB, PRT, _) :: SK'' =>
                    maintain (ctxt, HHF s :: MAGIC (CB, PRT, param) :: SK'')
                 |> report_goal
             | _ => maintain (ctxt, HHF s :: SK')
                 |> report_goal )
          else (case Config.get ctxt working_mode
            of "RELAXED" => origin
             | _ => raise OPR_FAIL(INVALID_OPR,  "This block should be closed by the END command."
          )))
       | _ => raise BROKEN_INVARIANT
    else report_goal (ctxt, SK'1)
  end
  | NXT' _ _ _ _ = raise BROKEN_INVARIANT

fun END SH_override = OPR_ID (END' NO_PARAM SH_override 0)
fun NXT param SH_override = OPR_ID (NXT' (CASE_NAME param) SH_override)
val END_CMD  = orverride_parser >> END
val NXT_CMD  = (fn toks => (OPT_VARS -- orverride_parser >> uncurry NXT ) toks)

fun type_of_end' [] = NONE
  | type_of_end' (ENDBLK typ :: _) = SOME typ
  | type_of_end' (HHF _ :: L) = type_of_end' L
  | type_of_end' (MAGIC _ :: L) = type_of_end' L

val type_of_end = type_of_end' o #2 o #1

(** LET **)

local

fun gen_bind prep_terms raw_binds ctxt =
    let
      fun prep_bind (raw_pats, t) ctxt1 =
        let
          val T = Term.fastype_of t;
          val ctxt2 = Variable.declare_term t ctxt1;
          val pats = prep_terms (Proof_Context.set_mode Proof_Context.mode_pattern ctxt2) T raw_pats;
          val binds = Proof_Context.simult_matches ctxt2 (t, pats);
        in (binds, ctxt2) end;

      val ts = prep_terms ctxt dummyT (map snd raw_binds);
      val (binds, ctxt') = apfst flat (fold_map prep_bind (map fst raw_binds ~~ ts) ctxt);
      val binds' = map #1 binds ~~ Variable.exportT_terms ctxt' ctxt (map #2 binds);

      val ctxt'' =
        ctxt
        |> fold Variable.declare_term (map #2 binds')
        |> fold Proof_Context.bind_term binds';
      val _ = Variable.warn_extra_tfrees ctxt ctxt'';
    in ctxt'' end

fun read_terms ctxt T =
  map (Syntax.parse_term ctxt #> Type.constraint T) #> Syntax.check_terms ctxt;

in

fun LET' prep_terms raw_binds (ctxt, S) =
      (gen_bind prep_terms raw_binds ctxt, S)

val LET = OPR o LET' (fn ctxt => fn _ => map (Proof_Context.cert_term ctxt))
val LET'' = OPR o LET' read_terms
val LET_CMD =
  (Parse.and_list1 (Parse.and_list1 Parse.term -- (\<^keyword>\<open>=\<close> |-- Parse.term))
    >> (OPR o LET' read_terms))


end

(** CHOOSE -- Instantiate Existential Quantification **)

fun CHOOSE' prep_terms raw_terms (ctxt, HHF (st, items) :: SK) =
  let val terms = prep_terms ctxt raw_terms

      fun rule_of st =
          case Thm.major_prem_of st
            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ex\<close>, _) $ _) => Thms.exI
             | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ex1\<close>, _) $ _) => Thms.ex1I
             | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Set.Bex\<close>, _) $ _) =>
                Proof_Context.get_thm ctxt "Set.bexI"
             | _ => raise OPR_FAIL (INVALID_OPR, "The leading goal is not about existential quantification")

      val st' = fold (fn term => fn st =>
            let val rule = rule_of st
                        |> Drule.infer_instantiate ctxt [(("x",0), Thm.cterm_of ctxt term)]
             in rule RS st
            end ) terms st
   in report_goal (ctxt, HHF (st', items) :: SK)
  end
  | CHOOSE' _ _ _ = raise BROKEN_INVARIANT

fun read_term ctxt (raw_term, vs) =
  let val (_, ctxt') = Proof_Context.add_fixes_cmd vs ctxt
      val term = Syntax.read_term ctxt' raw_term
   in singleton (Variable.export_terms ctxt' ctxt) term
  end

val CHOOSE = OPR o CHOOSE' (K I)
val CHOOSE'' = OPR o CHOOSE' (map o read_term)
val CHOOSE_CMD = Parse.and_list (Scan.repeat1 (Parse.term -- Scan.optional (VARS_KWD |-- Parse.vars) [])) >> (CHOOSE'' o flat)

(** PRINT **)
fun fixes_is_outdated ctxt var_name =
  Name.is_skolem var_name andalso Variable.revert_fixed ctxt var_name = var_name

fun contains_outdated_fixes ctxt term =
  let val vars = Term.add_free_names term []
   in exists (fixes_is_outdated ctxt) vars
  end

(*
fun ap2_3 f (a,b,c) = (a, f b, c)

fun pretty_top_state ctxt tree =
  let open Pretty
      val atom_goals = Config.get ctxt atomize_goals
      val prt_typ = Syntax.pretty_typ ctxt
      val prt_term= Syntax.pretty_term ctxt o (atom_goals ? Object_Logic.atomize_term ctxt)
      fun prt_bundle (vars, facts, term) =
        let val prems = Logic.strip_imp_prems term
            val name = str o simp_name
            val tails =
                 (if null vars   then [] else [keyword1 "fixed variables"])
                @ map (fn (N,T) => item [str N, brk 1, str "::", brk 1, prt_typ  T]) vars
                @ (if null facts then [] else [keyword1 "contextual facts"])
                @ map (fn (N,[])  => item [name N, brk 1, str ":", brk 1, str "<empty>"]
                        | (N,[T]) => item [name N, brk 1, str ":", brk 1, prt_term T]
                        | (N,TS)  => item [name N, brk 1, str ":", brk 1, chunks (map prt_term TS)]
                      ) facts
         in case prems
         of [] => str "All goals are proven!"
          | [goal] => chunks ( block [keyword1 "goal: ", prt_term goal] :: tails)
          | _  => chunks (
              keyword1 "goals: " ::
              map (fn X => item [prt_term X]) prems
              @ tails)
        end
   in collect_context tree
   |> ap2_3 (map (apsnd (filter_out (contains_outdated_fixes ctxt)))
          #> filter_out (null o snd))
   |> prt_bundle
  end
*)

fun pretty_tree0 _ (BUNDL (_,[])) =
      Pretty.keyword1 "All goals are solved!"
  | pretty_tree0 ctxt tree =
  let open Pretty
      val prt_typ = Syntax.pretty_typ ctxt
      val prt_term= Syntax.pretty_term ctxt

      val name = str o simp_name
      fun pretty_items (vars0, facts0) =
        let val facts = filter_out (exists (contains_outdated_fixes ctxt) o snd) facts0
            val vars  = filter_out (fixes_is_outdated ctxt o fst) vars0
         in (if null vars  then [] else [keyword1 "variables"])
          @ map (fn (N,T)   => item [str N, brk 1, str "::", brk 1, prt_typ  T]) vars
          @ (if null facts then [] else [keyword1 "facts"])
          @ map (fn (N,[])  => item [name N, brk 1, str ":", brk 1, str "<empty>"]
                  | (N,[T]) => item [name N, brk 1, str ":", brk 1, prt_term T]
                  | (N,TS)  => item [name N, brk 1, str ":", brk 1, chunks (map prt_term TS)]
                ) facts
        end
      fun pretty prefix (PROP (items, term)) =
            if items = empty_items andalso null prefix
            then prt_term term
            else chunks ( keyword1 (String.concat prefix ^ "goal")
                       :: item [prt_term term]
                       :: pretty_items items )
        | pretty prefix (BUNDL (items, children)) =
              chunks ( keyword1 (String.concat prefix ^ 
                                (case children
                                   of [_] => "goal"
                                    | [ ] => raise BROKEN_INVARIANT
                                    | _ => string_of_int (length children) ^ " subgoals"))
                    :: map (item o single o pretty []) children
                     @ pretty_items items )
        | pretty prefix (BLOCK tree) = pretty ("block of " :: prefix) tree
   in pretty [] (BLOCK tree)
  end

fun pretty_tree ctxt tree = tree
      |> Config.get ctxt atomize_goals ? atomize_tree ctxt
      |> pretty_tree0 ctxt

(* fun pretty_tree (POPL ) *)

fun PRINT (state as ((ctxt,SK), _, ID)) =
  let open Pretty
   in Pretty.writeln (chunks [
        block [keyword1 "proof state after step ", str (string_of_int ID)],
        pretty_tree ctxt (print_stack SK)
      ])
    ; state
  end
val PRINT_CMD = Scan.succeed PRINT

(** NOTATION **)

local

fun read_arg (c, mx) ctxt =
  (case Proof_Context.read_const {proper = false, strict = false} ctxt c of
    Free (x, _) =>
      let
        val ctxt' =
          ctxt |> is_none (Variable.default_type ctxt x) ?
            Variable.declare_constraints (Free (x, Mixfix.default_constraint mx));
        val t = Free (#1 (Proof_Context.inferred_param x ctxt'));
      in ((t, mx), ctxt') end
  | t => ((t, mx), ctxt));

in

fun WRITE' prep_arg mode args (ctxt, SK) =
  (Proof_Context.notation true mode (fst (fold_map prep_arg args ctxt)) ctxt, SK)

val NOTATION   = OPR oo WRITE' pair
val NOTATION'' = OPR oo WRITE' read_arg
val NOTATION_CMD = Parse.syntax_mode -- Parse.and_list1 (Parse.const -- Parse.mixfix)
             >> (fn (mode, args) => OPR (WRITE' read_arg mode args))

end

(** OPEN_MODULE **)

local

fun abs_def_rule eqns ctxt =
  (map (Local_Defs.abs_def_rule ctxt) (maps snd eqns), ctxt);

fun note_eqns_register note add_registration
    deps eqnss witss def_eqns thms export export' ctxt =
  let
    val factss = thms
      |> unflat ((map o map) #1 eqnss)
      |> map2 (map2 (fn b => fn eq =>
          (b, [([Morphism.thm export (Thm.transfer' ctxt eq)], [])]))) ((map o map) #1 eqnss);
    val (eqnss', ctxt') =
      fold_map (fn facts => note Thm.theoremK facts #-> abs_def_rule) factss ctxt;
    val defs = (Binding.empty_atts, [(map (Morphism.thm (export' $> export)) def_eqns, [])]);
    val (eqns', ctxt'') = ctxt' |> note Thm.theoremK [defs] |-> abs_def_rule;
    val transform_witness = Element.transform_witness (Morphism.set_trim_context' ctxt' export');
    val deps' =
      (deps ~~ witss) |> map (fn ((dep, morph), wits) =>
        (dep, morph $> Element.satisfy_morphism (map transform_witness wits)));
    fun register (dep, eqns) ctxt =
      ctxt |> add_registration
        {inst = dep,
          mixin = Option.map (rpair true) (Element.eq_morphism ctxt (eqns @ eqns')),
          export = export};
  in ctxt'' |> fold register (deps' ~~ eqnss') end;

in

fun generic_interpretation prep_interpretation setup_proof note add_registration
    expression raw_defs initial_ctxt =
  let
    val (((propss, eq_propss, deps, eqnss, export, export'), def_eqns), goal_ctxt) =
      prep_interpretation expression raw_defs initial_ctxt;
    fun after_qed witss eqns =
      note_eqns_register note add_registration deps eqnss witss def_eqns eqns export export';
  in setup_proof after_qed propss (flat eq_propss) goal_ctxt end;

end

local

fun augment_with_def prep_term ((name, atts), ((b, mx), raw_rhs)) lthy =
  let
    val rhs = prep_term lthy raw_rhs;
    val lthy' = Variable.declare_term rhs lthy;
    val ((_, (_, def)), lthy'') =
      Local_Theory.define ((b, mx), ((Thm.def_binding_optional b name, atts), rhs)) lthy';
  in (Thm.symmetric def, lthy'') end;

fun augment_with_defs _ [] _ = pair []
      (*quasi-inhomogeneous type: definitions demand local theory rather than bare proof context*)
  | augment_with_defs prep_term raw_defs deps =
      Local_Theory.begin_nested
      #> snd
      #> fold Locale.activate_declarations deps
      #> fold_map (augment_with_def prep_term) raw_defs
      #> Local_Theory.end_nested_result Morphism.fact;

fun prep_interpretation prep_expr prep_term
  expression raw_defs initial_ctxt =
  let
    val ((propss, eq_propss, deps, eqnss, export), expr_ctxt) = prep_expr expression initial_ctxt;
    val (def_eqns, def_ctxt) =
      augment_with_defs prep_term raw_defs deps expr_ctxt;
    val export' = Proof_Context.export_morphism def_ctxt expr_ctxt;
  in (((propss, eq_propss, deps, eqnss, export, export'), def_eqns), def_ctxt) end;

in

fun cert_interpretation expression =
  prep_interpretation Expression.cert_goal_expression Syntax.check_term expression;

fun read_interpretation expression =
  prep_interpretation Expression.read_goal_expression Syntax.read_term expression;

end;

val add_registration = Context.proof_map o Locale.add_registration

fun notes_kind kind facts ctxt =
  let val facts' = map ( apfst (apsnd (map (Attrib.attribute ctxt)))
                      #> apsnd (map (apsnd (map (Attrib.attribute ctxt)))) ) facts
   in Proof_Context.note_thmss kind facts' ctxt
  end

fun interpretation expression =
  generic_interpretation cert_interpretation Element.witness_proof_eqs
    notes_kind add_registration expression []

fun interpretation_cmd expression =
  generic_interpretation read_interpretation Element.witness_proof_eqs
    notes_kind add_registration expression [];


fun OPEN_MODULE' interp expr (lthy, HHF (st, items) :: SK) =
  let val _ = Local_Theory.assert lthy
      val ps = interp expr lthy
      val ctxtp = Proof.context_of ps
      
      fun PRT _ t = BUNDL (items, [t, print_stack [HHF (st, empty_items)]])
      fun CB ctxt' (raw_st', _, SK', _) =
        let val st' = singleton (Proof_Context.export ctxt' ctxtp) raw_st'
            val ctxt'' = Proof.refine_primitive (K (K st')) ps
                      |> Proof.global_done_proof

            val facts = Proof_Context.facts_of ctxt'';
            val local_facts =
              Facts.dest_static false [Proof_Context.facts_of lthy] facts
                |> map (apsnd (map Thm.prop_of))
            val local_facts = if length local_facts > 16 then [] else local_facts
                  (*Trim off facts if too many*)
            val items' = ([],local_facts)
         in get_reporter () (New_Items items')
          ; (ctxt'',
             HHF (st, cat_items items' items) :: SK')
        end

   in (ctxtp,
       HHF (#goal (Proof.raw_goal ps), empty_items)
       :: ENDBLK T_END
       :: MAGIC (CB, PRT, NO_PARAM)
       :: SK)
   |> report_goal
  end
  | OPEN_MODULE' _ _ _ = raise BROKEN_INVARIANT

val OPEN_MODULE   = OPR o OPEN_MODULE' interpretation
val OPEN_MODULE'' = OPR o OPEN_MODULE' interpretation_cmd
val OPEN_MODULE_CMD = Parse.!!! Parse_Spec.locale_expression
                  >> (OPR o OPEN_MODULE' interpretation_cmd)

(** LOCAL DEFINITION **)

(*TODO: items*)
fun DEFINE' define (ctxt, SK) =
  (Proof.init ctxt
    |> define
    |> Proof.context_of,
   SK)

fun DEFINE   names exprs fixes = OPR (DEFINE' (Proof.define names fixes exprs))
fun DEFINE'' names exprs fixes = OPR (DEFINE' (Proof.define_cmd names fixes exprs))
val DEFINE_CMD = (Parse.vars --| Parse.where_) -- Parse_Spec.statement -- Parse.for_fixes
              >> (fn ((a,b),c) => OPR (DEFINE' (Proof.define_cmd a c b)))


(** CONFIG **)

(*TODO: items*)

datatype config = CFG_NOTE   of Thm.binding * (thm list * attribute list) list
                | CFG_BUNDLE of Bundle.name

fun CONFIG' prep_attr_thms raw_thms (ctxt, SK) =
  let val cfgs = prep_attr_thms ctxt raw_thms
   in (fold (fn CFG_BUNDLE name => Bundle.includes [name]
              | CFG_NOTE   note => snd o Proof_Context.note_thms "" note) cfgs ctxt, SK)
  end

val CONFIG   = OPR o CONFIG' (K I)
val CONFIG_FACTS'' = OPR o CONFIG' (fn ctxt =>
    let fun parse_fact ((b,attrs), facts) =
              ((b, map (Attrib.attribute_cmd ctxt) attrs),
               map (apfst (Proof_Context.get_fact ctxt)
                 #> apsnd (map (Attrib.attribute_cmd ctxt))) facts)
     in map (CFG_NOTE o parse_fact)
    end )
val CONFIG_BUNDL'' = OPR o CONFIG' (fn ctxt =>
    let fun parse name = CFG_BUNDLE (Bundle.check ctxt (name, Position.none))
     in map parse
    end )

val CONFIG_CMD = Parse_Spec.name_facts >> (
      OPR o CONFIG' (fn ctxt => fn facts =>
    let fun parse_fact ((b,attrs), facts) =
              ((b, map (Attrib.attribute_cmd ctxt) attrs),
               map (apfst (Proof_Context.get_fact ctxt)
                 #> apsnd (map (Attrib.attribute_cmd ctxt))) facts)
        fun parse (origin as ((b,[]), [(Facts.Named (name,_), [])])) =
              if Binding.is_empty b
              then CFG_BUNDLE (Bundle.check ctxt name)
              else CFG_NOTE (parse_fact origin)
          | parse fact = CFG_NOTE (parse_fact fact)
     in map parse facts
    end ))

(*** Toplevel ***)

(* Interfaces *)

val CMDS = Symtab.make [
      ("end",     END_CMD),
      ("next",    NXT_CMD),
      ("consider",CONSIDER_CMD),
      ("have",    HAVE_CMD),
      ("END",     END_CMD),
      ("NEXT",    NXT_CMD),
      ("CONSIDER",CONSIDER_CMD),
      ("HAVE",    HAVE_CMD),
      ("CASE_SPLIT", CASE_SPLIT_CMD),
      ("INDUCT",  INDUCT_CMD),
      ("SIMP" ,   SIMP_CMD),
      ("CRUSH",   CRUSH_CMD),
      ("INTRO",   INTRO_CMD),
      ("ALL_INTRO",INTRO_ALL_CMD),
      ("HAMMER",  HAMMER_CMD),
      ("PRINT",   PRINT_CMD),
      ("RULE",    RULE_CMD),
      ("LET",     LET_CMD),
      ("let",     LET_CMD),
      ("APPLY",   APPLY_CMD),
      ("apply",   APPLY_CMD),
      ("UNFOLD",  UNFOLD_CMD),
      ("CHOOSE",  CHOOSE_CMD),
      ("NOTATION",NOTATION_CMD),
      ("OPEN_MODULE", OPEN_MODULE_CMD),
      ("DEFINE",  DEFINE_CMD),
      ("CONFIG",  CONFIG_CMD),
      ("STEP"  ,  STEP_CMD)
    ]

val keywords = let open Keyword
      in empty_keywords
      |> add_keywords
         [ (("where", \<^here>), quasi_command_spec),
           (("::",    \<^here>), quasi_command_spec),
           ((":",     \<^here>), quasi_command_spec),
           ((",",     \<^here>), quasi_command_spec),
           (("and",   \<^here>), quasi_command_spec),
           (("in",   \<^here>), quasi_command_spec),
           (("when",  \<^here>), quasi_command_spec),
           (("if",    \<^here>), quasi_command_spec),
           (("obtains",\<^here>),quasi_command_spec),
           (("shows", \<^here>), quasi_command_spec),
           (("fixes", \<^here>), quasi_command_spec),
           (("defines",\<^here>),quasi_command_spec),
           (("shows", \<^here>), quasi_command_spec),
           (("constrains",\<^here>),quasi_command_spec),
           (("assumes",\<^here>),quasi_command_spec),
           (("notes", \<^here>), quasi_command_spec),
           (("includes",\<^here>),quasi_command_spec),
           (("|",     \<^here>), quasi_command_spec),
           (("(",     \<^here>), quasi_command_spec),
           ((")",     \<^here>), quasi_command_spec),
           (("[",     \<^here>), quasi_command_spec),
           (("]",     \<^here>), quasi_command_spec),
           (("?",     \<^here>), quasi_command_spec),
           (("=",     \<^here>), quasi_command_spec),
           (("for",   \<^here>), quasi_command_spec),
           (("WITH",  \<^here>), quasi_command_spec),
           (("WITHOUT",\<^here>),quasi_command_spec),
           (("IN",    \<^here>), quasi_command_spec),
           (("VARS",  \<^here>), quasi_command_spec),
           (("infix",  \<^here>), quasi_command_spec),
           (("infixr", \<^here>), quasi_command_spec),
           (("infixl", \<^here>), quasi_command_spec),

           (("END",   \<^here>), command_spec (thy_end, [])),
           (("end",   \<^here>), command_spec (thy_end, [])),
           (("NEXT",  \<^here>), command_spec (thy_end, [])),
           (("CONSIDER",\<^here>),command_spec (prf_asm_goal, [])),
           (("HAVE",  \<^here>), command_spec (prf_goal, [])),
           (("CASE_SPLIT",  \<^here>), command_spec (prf_goal, [])),
           (("INDUCT",\<^here>), command_spec (prf_goal, [])),
           (("CRUSH", \<^here>), command_spec (prf_goal, [])),
           (("SIMP" , \<^here>), command_spec (prf_goal, [])),
           (("INTRO", \<^here>), command_spec (prf_goal, [])),
           (("ALL_INTRO", \<^here>), command_spec (prf_goal, [])),
           (("HAMMER",\<^here>), command_spec (prf_goal, [])),
           (("PRINT", \<^here>), command_spec (diag,     [])),
           (("RULE",  \<^here>), command_spec (prf_decl, [])),
           (("LET",   \<^here>), command_spec (prf_decl, [])),
           (("APPLY", \<^here>), command_spec (prf_decl, [])),
           (("UNFOLD",\<^here>), command_spec (prf_goal, [])),
           (("CHOOSE",\<^here>), command_spec (prf_decl, [])),
           (("NOTATION",\<^here>), command_spec (prf_decl, [])),
           (("OPEN_MODULE",\<^here>), command_spec (prf_goal, [])),
           (("DEFINE",\<^here>), command_spec (prf_decl, [])),
           (("CONFIG",\<^here>), command_spec (prf_decl, [])),
           (("STEP",  \<^here>), command_spec (prf_decl, []))
         ]
     end

fun lex_cmds source =
  let val pos = Position.make {
                  line=1, offset=1, end_offset=1,
                  props={label="", file="#MINSHELL SCRIPT", id="no_id"} }
      val src = Symbol_Pos.explode (source, pos)
      val toks = Token.tokenize keywords {strict = false} src

      fun split ret []  [] = ret
        | split ret buf [] = rev (Token.eof :: buf) :: ret
        | split ret buf (x::L) =
            if Token.is_command x
            then split (case buf of [] => ret
                           | _ => rev (Token.eof :: buf) :: ret) [x] L
            else if Token.is_ignored x
            then split ret buf L
            else split ret (x::buf) L

   in split [] [] toks
   |> rev
  end

fun parse_cmds toks =
  let val cmds = toks
              |> map (fn (h::toks) =>
                    case Symtab.lookup CMDS (Token.content_of h)
                      of SOME parser => fst (parser toks)
                       | NONE => error ("Bad Command " ^ Token.content_of h) )
   in fold I cmds
  end

fun stack_is_finished (_, [HHF (st', _)]) = no_goal' st'
  | stack_is_finished _ = false
fun is_finished (SK,_,_) = stack_is_finished SK

fun conclude initial_ctxt ((ctxt', S  as [HHF (st',_)]),_,_) =
      let val st'' = singleton (Proof_Context.export ctxt' initial_ctxt) st'
                  |> finalize_goal ctxt'
       in Pretty.writeln (pretty_tree ctxt' (print_stack S));
          st''
      end
  | conclude _ ((ctxt', S), _, _) =
     (Pretty.writeln (pretty_tree ctxt' (print_stack S));
      error "incomplete MINSHELL script")

fun PROVE tr ctxt st =
      INIT ctxt st
   |> OPR_NO_INCR (apfst INIT_SYNTAX)
   |> tr
   |> conclude ctxt

fun METHOD_i tr : Method.method = CONTEXT_METHOD (fn _ => fn (ctxt,st) =>
  if Thm.no_prems st
  then Seq.single (Seq.Result (ctxt, st))
  else Seq.make (fn () =>
        SOME (Seq.Result (ctxt, PROVE tr ctxt st), Seq.empty)))

val METHOD = METHOD_i o parse_cmds o lex_cmds

val _ = Theory.setup (
  Method.setup \<^binding>\<open>min_script\<close> (
    Scan.peek (fn _ => Parse.embedded >> (fn src => fn _ =>
        METHOD src)))
  ""
)

end
