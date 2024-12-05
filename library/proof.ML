signature IPS_PROOF = sig

type stack
type state
type operation = state -> state
type command = Proof.context -> operation parser

exception OPR_FAIL of string

(* Operations *)

val init : Proof.context -> stack

val INTROS : stack -> stack

val apply : context_tactic -> Time.time option -> stack -> stack
val apply_method : Method.method -> Time.time option -> stack -> stack

val crush_timeout : int Config.T
val CRUSH : operation
val CRUSH_CMD : command

val INDUCT : bool * ((binding option * (term * bool)) option list list *
              (((string * typ) list list * term option list) * thm list option))
          -> state -> state
val INDUCT_CMD : command

val CASE : bool * (term option list list * thm option) -> operation
val CASE_CMD : command

val record_history : string -> operation
val restore_history : string -> operation

val HAVE : (bstring * Token.src list) option -> string -> operation
val HAVE_CMD : command

end

structure IPS_Proof : IPS_PROOF = struct


(*only for printing*)
type local_facts = (string * term) list
datatype tree = PROP  of (string * typ) list (*variables*) * local_facts * term (*goal*)
              | BUNDL of (string * typ) list (*variables*) * local_facts * tree list


type intro_subgaols = bool (*whether to intro the variables & assumpstions for all its subgoals*)
datatype frame = HHF   of thm (*a local_facts bundle node, represented as a Hereditary Harrop Formula*)
                        * local_facts
                        * intro_subgaols
               | MAGIC of (Proof.context -> thm * local_facts * intro_subgaols -> Proof.context * frame)
                        * (tree -> tree)

type stack = Proof.context * (frame list)
  (*invariant: the head must be an HHF*)

type state = stack              (*current stack*)
           * stack Symtab.table (*history*)

type operation = state -> state
type command = Proof.context -> operation parser

exception BROKEN_INVARIANT

exception OPR_FAIL of string



(** Basic Operations **)

fun init c = (c,[])

(*Modus Ponens*)
fun MP thAB thA =
  let val LHS = Thm.cprop_of thAB
             |> Thm.dest_arg1
      val inst = Thm.match (LHS, Thm.cprop_of thA)
      val thAB' = Thm.instantiate inst thAB
   in Thm.implies_elim thAB' thA
  end

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

(* fun join_lstR pr = AList.join (op =) (fn _ => fn (_,x) => x) pr *)
fun join_lstL pr = AList.join (op =) (fn _ => fn (x,_) => x) pr

fun augment_print (vs',hs') (PROP (vs, hs, goal))
      = (PROP  (join_lstL (vs, vs'), hs' @ hs, goal))
  | augment_print (vs',hs') (BUNDL (vs, hs, goal))
      = (BUNDL (join_lstL (vs, vs'), hs' @ hs, goal))

(*fix local variables & facts*)
fun INTROS (ctxt, HHF (st, facts, IA) :: L) =
     (case Thm.nprems_of st
        of 0 => raise BROKEN_INVARIANT
         | _ => if need_intro st
                then let val (foc, st') = Subgoal.focus_prems ctxt 1 NONE st
                         fun CB ctxt' (st',_,IA) =
                            (ctxt', HHF (
                                Subgoal.retrofit ctxt' ctxt (#params foc) (#asms foc) 1 st' st
                                  |> Seq.hd,
                                [],
                                IA))
                         val PRT = augment_print (map (apsnd Thm.typ_of_cterm) (#params foc),
                                                  map (pair "" o Thm.prop_of) (#prems foc))
                      in (#context foc, HHF (st', facts, IA) :: MAGIC (CB,PRT) :: L)
                     end
                else (ctxt, HHF (st, facts, IA) :: L)
      )
  | INTROS _ = raise BROKEN_INVARIANT

fun maintain (c,[]) = (c,[])
  | maintain (origin as (ctxt, HHF (st, facts, IA) :: L)) =
    ( case Thm.nprems_of st
        of 0 => (case L
            of [] => (ctxt,[])
             | (HHF (st1, facts', IA') :: L') =>
                  maintain (ctxt, HHF (MP st1 st, facts' @ facts, IA') :: L')
             | (MAGIC (cb,_) :: L') =>
                  (case cb ctxt (st, facts, IA) of (ctxt', fr) => maintain (ctxt', fr:: L') ))
         | 1 => origin
         | _ => let val goal = Thm.cprop_of st
                            |> Thm.dest_arg1
                            |> Goal.init
                    val st' = Conv.gconv_rule (Conv.rewr_conv @{thm prop_def[symmetric]}) 1 st
                 in (ctxt, (HHF (goal,[],false))::(HHF (st',facts,IA))::L)
                 |> IA ? INTROS
                end )
  | maintain (_, MAGIC _ :: _) = raise BROKEN_INVARIANT

fun INTROS_ALL_SUBGOALS (ctxt, HHF (st, facts, _) :: L) =
      maintain (ctxt, HHF (st, facts, Thm.nprems_of st >= 1) :: L)
  | INTROS_ALL_SUBGOALS _ = raise BROKEN_INVARIANT

fun raw_apply tac timeout (ctxt, HHF (st, facts, IA) :: L) =
    ( case (case timeout
              of SOME time => Timeout.apply time Seq.pull (tac (ctxt, st))
               | NONE      => Seq.pull (tac (ctxt, st)) )
        of NONE => raise OPR_FAIL "Fail to apply the tactic"
         | SOME (Seq.Result (ctxt', st'), _) => (ctxt', HHF (st', facts, IA) :: L)
         | SOME (Seq.Error E, _) => raise OPR_FAIL (E ()) )
  | raw_apply _ _ _ = raise BROKEN_INVARIANT

fun apply' tac timeout s = maintain (raw_apply tac timeout s)

fun apply tac time s = apply' tac time s
      handle Timeout.TIMEOUT _ => raise OPR_FAIL "Timeout"

fun apply_method meth timeout s = apply (meth []) timeout s


fun record_history name (s,his) = (s, Symtab.update (name,s) his)
fun restore_history name (_,his) =
    case Symtab.lookup his name
      of NONE => raise OPR_FAIL ("history " ^ name ^ " not found")
       | SOME s => (s, his)

val OPR = apfst : (stack -> stack) -> (state -> state)

fun strip_meta_hhf term =
  let fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,("",H)::P) B
        | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
        | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ X) =
            strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | strip (V,P) X = (rev V, rev P, X)
   in strip ([],[]) term end

val SOLVED_GOAL = \<^prop>\<open>True\<close>

fun print_stack [] = PROP ([], [], SOLVED_GOAL)
  | print_stack (S::L) =
      let fun prt t [] = t
            | prt t (HHF (st, facts, IA) :: L) =
                let val goals = case Thm.prems_of st
                                  of [] => raise BROKEN_INVARIANT
                                   | (_::prems) => prems
    
                    val nodes = map (fn goal =>
                          if IA
                          then let val (vs,hs,concl) = strip_meta_hhf goal
                                in PROP (vs, hs, concl)
                               end
                          else PROP ([], [], goal)) goals
                 in prt (BUNDL ([], facts, t::nodes)) L
                end
            | prt t (MAGIC (_, PRT) :: L) = prt (PRT t) L
          fun prt0 (HHF (st, facts, _)) = PROP ([], facts, Thm.prop_of st)
            | prt0 _ = raise BROKEN_INVARIANT
       in prt (prt0 S) L
      end


(** Interfaces **)


(*fun INTROS_ALL (ctxt, HHF (st, facts) :: L) = *)
  

(* Crush *)

val crush_timeout = Attrib.setup_config_int \<^binding>\<open>crush_timeout\<close> (K 10) (*in seconds*)

fun CRUSH' (ctxt, []) = (ctxt, [])
  | CRUSH' (s as (ctxt, _)) =
  let val time = Config.get ctxt crush_timeout
              |> Time.fromSeconds
   in
   (( raw_apply (CONTEXT_TACTIC (Clasimp.auto_tac ctxt)) (SOME time) s
      handle Timeout.TIMEOUT _ => 
      raw_apply (CONTEXT_TACTIC (Clasimp.clarsimp_tac ctxt 1)) (SOME time) s)
      handle OPR_FAIL E =>
                (case s of (_, HHF (st, _, _) :: _) =>
                                if need_intro st then s else raise OPR_FAIL E
                         | _ => raise OPR_FAIL E )
           | Timeout.TIMEOUT _ =>
                raise OPR_FAIL "Timeout")
   |> INTROS_ALL_SUBGOALS
  end

val CRUSH = OPR CRUSH'

val CRUSH_CMD = K (Args.$$$ "CRUSH" >> K CRUSH)

(* INDUCT & CASE *)

local (*copied from $ISABELLE_HOME/src/Tools/induct.ML*)

val arbitraryN = "arbitrary";
val takingN = "taking";
val ruleN = "rule";

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ arbitraryN || Args.$$$ takingN || Args.$$$ Induct.typeN ||
    Args.$$$ Induct.predN || Args.$$$ Induct.setN || Args.$$$ ruleN) -- Args.colon)) scan;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val inst' = Scan.lift (Args.$$$ "_") >> K NONE ||
  Args.term >> (SOME o rpair false) ||
  Scan.lift (Args.$$$ "(") |-- (Args.term >> (SOME o rpair true)) --|
    Scan.lift (Args.$$$ ")");

val def_inst =
  ((Scan.lift (Args.binding --| (Args.$$$ "\<equiv>" || Args.$$$ "==")) >> SOME)
      -- (Args.term >> rpair false)) >> SOME ||
    inst' >> Option.map (pair NONE);

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));

val arbitrary = Scan.optional (Scan.lift (Args.$$$ arbitraryN -- Args.colon) |--
  Parse.and_list1' (Scan.repeat (unless_more_args free))) [];

val taking = Scan.optional (Scan.lift (Args.$$$ takingN -- Args.colon) |--
  Scan.repeat1 (unless_more_args inst)) [];

fun single_rule [rule] = rule
  | single_rule _ = error "Single rule expected";

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- Scan.repeat arg :|--
    (fn names => Scan.peek (fn context => Scan.succeed (names |> map (fn name =>
      (case get (Context.proof_of context) name of SOME x => x
      | NONE => error ("No rule for " ^ k ^ " " ^ quote name))))));

fun rule get_type get_pred =
  named_rule Induct.typeN (Args.type_name {proper = false, strict = false}) get_type ||
  named_rule Induct.predN (Args.const {proper = false, strict = false}) get_pred ||
  named_rule Induct.setN (Args.const {proper = false, strict = false}) get_pred ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.thms;

val induct_rule = rule Induct.lookup_inductT Induct.lookup_inductP;
val cases_rule = rule Induct.lookup_casesT Induct.lookup_casesP >> single_rule;


val ind_synt' =
      (Scan.lift (Args.mode Induct.no_simpN) --
      (Parse.and_list' (Scan.repeat (unless_more_args def_inst)) --
        (arbitrary -- taking -- Scan.option induct_rule)))

fun ind_synt ctxt toks = case ind_synt' (ctxt, toks) of (x, (_, toks)) => (x,toks)

val case_synt' =
      (Scan.lift (Args.mode Induct.no_simpN) --
        (Parse.and_list' (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule))

fun case_synt ctxt toks = case case_synt' (ctxt, toks) of (x, (_, toks)) => (x,toks)

in

fun INDUCT' (no_simp, (insts, ((arbitrary, taking), opt_rule))) s =
  let val tac = Induct.induct_context_tactic no_simp insts arbitrary taking opt_rule [] 1
   in apply' tac NONE s
  end

val INDUCT = OPR o INDUCT'
fun INDUCT_CMD ctxt =
      ind_synt (Context.Proof ctxt) >> (fn (no_simp, (insts, ((arbitrary, taking), opt_rule))) =>
          INDUCT (no_simp, (insts, ((arbitrary, taking), opt_rule))) )

fun CASE' (no_simp, (insts, opt_rule)) s =
  let val tac = Induct.cases_context_tactic no_simp insts opt_rule [] 1
   in apply' tac NONE s
  end

val CASE = OPR o CASE'
fun CASE_CMD ctxt =
      case_synt (Context.Proof ctxt) >> (fn (no_simp, (insts, opt_rule)) =>
          CASE (no_simp, (insts, opt_rule)))

end

(* HAVE *)

fun HAVE' _ _ (ctxt, []) = (ctxt, [])
  | HAVE' raw_name expr (ctxt, HHF (G,facts,IA) :: S) =
      let val name = Option.map (fn (name, raw_attrs) =>
                        (Binding.name name,
                         raw_attrs |> map ( Attrib.check_src ctxt
                                         #> Attrib.attribute ctxt ) ) ) raw_name
                  |> the_default (Binding.empty, [])
          val goal = Goal.init (Thm.cterm_of ctxt (Syntax.read_prop ctxt expr))
          fun CB ctxt' (st',facts',_) =
            let val ((name,[thm]), ctxt'') =
                        Proof_Context.note_thms "" (name, [([st'],[])]) ctxt'
             in (ctxt'', HHF (G, (name, Thm.prop_of thm) :: facts' @ facts, IA))
            end
          fun PRT t = BUNDL ([], [], [t, print_stack [HHF (G,facts,IA)]])
       in (ctxt, HHF (goal, [], false) :: MAGIC (CB, PRT) :: S)
      end
  | HAVE' _ _ (_, _) = raise BROKEN_INVARIANT

val HAVE = OPR oo HAVE'

val HAVE_CMD = K (Args.$$$ "HAVE" |--
        Scan.option (Parse.name -- Parse.opt_attribs --| \<^keyword>\<open>:\<close>) --
        Parse.term
     >> (fn (name, expr) => HAVE name expr))

(* OBTAIN *)

end