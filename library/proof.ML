signature IPS_PROOF = sig

type stack
type state
type operation = state -> state
type parse_ctxt = Context.generic
type command = parse_ctxt -> operation parser

exception OPR_FAIL of string

(* options *)

val atomize_goals : bool Config.T

(* Operations *)

val INIT : Proof.context -> thm -> state
val INIT': Proof.state -> state

val INTROS : operation
val INTROS_CMD : command

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

val OBTAIN : (binding * string option * mixfix) list
          -> ((binding * Token.src list) * (string * string list) list) list
          -> operation
val OBTAIN_CMD : command

val HAMMER : operation
val HAMMER_CMD : command

val END : operation
val END_CMD : command

val PRINT : operation
val PRINT_CMD : command

(* Toplevel *)

val parse_cmds : parse_ctxt -> string -> state -> state
val METHOD : parse_ctxt -> string -> Method.method

end

structure IPS_Proof : IPS_PROOF = struct

val assm_N = "assm"
fun assm_name i = assm_N ^ string_of_int i

(* options *)

val atomize_goals = Attrib.setup_config_bool \<^binding>\<open>min_shell_atomize_goals\<close> (K true)

(*only for printing*)
type local_facts = (string * term list) list
datatype tree = PROP  of (string * typ) list (*variables*) * local_facts * term (*goal*)
              | BUNDL of (string * typ) list (*variables*) * local_facts * tree list


datatype frame = HHF   of thm (*a local_facts bundle node, represented as a Hereditary Harrop Formula*)
                        * local_facts
               | MAGIC of (Proof.context -> thm * local_facts * frame list -> Proof.context * frame list)
                        * (tree -> tree)
               | ENDBLK 

type stack = Proof.context * (frame list)
  (*invariant: the head must be an HHF*)

type state = stack              (*current stack*)
           * stack Symtab.table (*history*)
           * int                (*cache id*)

type operation = state -> state
type parse_ctxt = Context.generic
type command = parse_ctxt -> operation parser

exception BROKEN_INVARIANT

exception OPR_FAIL of string



(** Basic Operations **)

structure IPS_Data = Proof_Data (
  type T = ( int Unsynchronized.ref (*counter for fixed premise*)
           * int Unsynchronized.ref (*facts counter*)
           * string                 (*hash used for caching proof*) ) option
  val init = K NONE
)

fun init_ctxt c st = IPS_Data.put (
        SOME (Unsynchronized.ref 0,
              Unsynchronized.ref 0,
              Hasher.term (Thm.prop_of st))
        ) c
fun INIT c st = ((init_ctxt c st, [HHF (st, []), ENDBLK]), Symtab.empty, 0)
fun INIT'  st = INIT (Proof.context_of st) (#goal (Proof.simple_goal st))

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

fun maintain (c,[]) = (c,[])
  | maintain (origin as (ctxt, HHF (st, facts) :: L)) =
    ( case Thm.nprems_of st
        of 0 => (case L
            of [] => origin
             | (HHF (st1, facts') :: L') =>
                  maintain (ctxt, HHF (MP st1 st, facts' @ facts) :: L')
             | (MAGIC (cb,_) :: L') =>
                  (case cb ctxt (st, facts, L') of (ctxt', S) => maintain (ctxt', S) )
             | ENDBLK :: _ => origin )
         | _ => origin)
  | maintain (_, MAGIC _ :: _) = raise BROKEN_INVARIANT
  | maintain (_, ENDBLK :: _) = raise BROKEN_INVARIANT

(*fix local variables & facts*)
fun INTROS'' all_subgoals F (ctxt, HHF (st, facts) :: L) =
     (case Thm.nprems_of st
        of 0 => raise BROKEN_INVARIANT
         | _ => if Thm.nprems_of st > 1 orelse need_intro st
                then let val (foc, st') = Subgoal.focus_prems ctxt 1 NONE st
                         val PRT = augment_print (map (apsnd Thm.typ_of_cterm) (#params foc), [])
                         fun CB ctxt' (st',_,S) =
                            (ctxt', HHF (
                                Subgoal.retrofit ctxt' ctxt (#params foc) (#asms foc) 1 st' st
                                  |> Seq.hd,
                                []) :: S)
                            |> all_subgoals ? INTROS'' all_subgoals F
                         val (facts', ctxt') = F foc
                      in (ctxt', HHF (st', facts' @ facts) :: MAGIC (CB,PRT) :: L)
                     end
                else (ctxt, HHF (st, facts) :: L)
      )
  | INTROS'' _ _ _ = raise BROKEN_INVARIANT

fun INTROS' all_subgoals = INTROS'' all_subgoals (fn foc =>
  let val ctxt = #context foc
      val SOME (ii,_,_) = IPS_Data.get ctxt
      val i = !ii
      val _ = ii := i + 1
   in ctxt
   |> Proof_Context.note_thms "" ((Binding.name (assm_name i), []),
                                  map (fn th => ([th], [])) (#prems foc))
   |> apfst (apsnd (map Thm.prop_of) #> single)
  end )

fun raw_apply tac timeout (ctxt, HHF (st, facts) :: L) =
    ( case (case timeout
              of SOME time => Timeout.apply time Seq.pull (tac (ctxt, st))
               | NONE      => Seq.pull (tac (ctxt, st)) )
        of NONE => raise OPR_FAIL "Fail to apply the tactic"
         | SOME (Seq.Result (ctxt', st'), _) => (ctxt', HHF (st', facts) :: L)
         | SOME (Seq.Error E, _) => raise OPR_FAIL (E ()) )
  | raw_apply _ _ _ = raise BROKEN_INVARIANT

fun apply' tac timeout s = maintain (raw_apply tac timeout s)

fun apply tac time s = apply' tac time s
      handle Timeout.TIMEOUT _ => raise OPR_FAIL "Timeout"

fun apply_method meth timeout s = apply (meth []) timeout s


fun record_history name (s,his,ID) = (s, Symtab.update (name,s) his,ID)
fun restore_history name (_,his,ID) =
    case Symtab.lookup his name
      of NONE => raise OPR_FAIL ("history " ^ name ^ " not found")
       | SOME s => (s, his,ID)

fun OPR (f : stack -> stack) ((S,TAB,ID) : state) : state
  = (f S, TAB, ID+1)
fun OPR_ID (f : int -> stack -> stack) ((S,TAB,ID) : state) : state
  = (f ID S, TAB, ID+1)

val INTROS = OPR (INTROS' false)
val INTROS_CMD = K (Scan.succeed INTROS)
val INTROS_ALL = OPR (INTROS' true)
val INTROS_ALL_CMD = K (Scan.succeed INTROS_ALL)

(*
fun strip_meta_hhf N term =
  let fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,(N,[H])::P) B
        | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
        | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ X) =
            strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | strip (V,P) X = (rev V, rev P, X)
   in strip ([],[]) term end
*)

val SOLVED_GOAL = \<^prop>\<open>True\<close>

fun print_stack [] = PROP ([], [], SOLVED_GOAL)
  | print_stack (S::L) =
      let fun prt t [] = t
            | prt t (HHF (st, facts) :: L) =
                let val goals = case Thm.prems_of st
                                  of [] => raise BROKEN_INVARIANT
                                   | (_::prems) => prems
    
                    val nodes = map (fn goal => PROP ([], [], goal)) goals
                 in prt (BUNDL ([], facts, t::nodes)) L
                end
            | prt t (MAGIC (_, PRT) :: L) = prt (PRT t) L
            | prt t (ENDBLK :: L) = prt t L
          fun prt0 (HHF (st, facts)) = PROP ([], facts, Thm.prop_of st)
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
                (case s of (_, HHF (st, _) :: _) =>
                                if need_intro st then s else raise OPR_FAIL E
                         | _ => raise OPR_FAIL E )
           | Timeout.TIMEOUT _ =>
                raise OPR_FAIL "Timeout")
   |> INTROS' true
  end

val CRUSH = OPR CRUSH'

val CRUSH_CMD = K (Scan.succeed CRUSH)

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
         ind_synt ctxt
      >> (fn (no_simp, (insts, ((arbitrary, taking), opt_rule))) =>
          INDUCT (no_simp, (insts, ((arbitrary, taking), opt_rule))) )

fun CASE' (no_simp, (insts, opt_rule)) s =
  let val tac = Induct.cases_context_tactic no_simp insts opt_rule [] 1
   in apply' tac NONE s
  end

val CASE = OPR o CASE'
fun CASE_CMD ctxt =
         case_synt ctxt
      >> (fn (no_simp, (insts, opt_rule)) =>
          CASE (no_simp, (insts, opt_rule)))

end

(* HAVE *)

fun HAVE' _ _ (ctxt, []) = (ctxt, [])
  | HAVE' raw_name expr (ctxt, HHF (G,facts) :: S) =
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
          fun CB ctxt' (st',facts',S) =
            let val ((name,[thm]), ctxt'') =
                        Proof_Context.note_thms "" (name, [([Goal.conclude st'],[])]) ctxt'
             in (ctxt'', HHF (G, (name, [Thm.prop_of thm]) :: facts' @ facts) :: S)
            end
          fun PRT t = BUNDL ([], facts, [t, print_stack [HHF (G,[])]])
       in (ctxt, HHF (goal, []) :: ENDBLK :: MAGIC (CB, PRT) :: S)
      end
  | HAVE' _ _ _ = raise BROKEN_INVARIANT

val HAVE = OPR oo HAVE'

val HAVE_CMD = K (
        Scan.option (Parse.name -- Parse.opt_attribs --| \<^keyword>\<open>:\<close>) --
        Parse.term
     >> (fn (name, expr) => HAVE name expr))

(* OBTAIN *)

fun atomize_term ctxt =
      Object_Logic.atomize_term ctxt
  #> (fn X => if Term.fastype_of X = \<^Type>\<open>bool\<close>
              then X
              else raise OPR_FAIL "Fail to atomize the proposition into HOL")

val elim_Ex = @{lemma \<open>Ex (\<lambda>x. P x) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q\<close>
                   by (unfold Ex_def, blast)}
val conjD1 = @{lemma \<open>conj A B \<Longrightarrow> A\<close> by (unfold conj_def, blast)}
val conjD2 = @{lemma \<open>conj A B \<Longrightarrow> B\<close> by (unfold conj_def, blast)}

fun OBTAIN' raw_fixes raw_statements (ctxt, HHF (st,facts) :: S) =
  let val raw_props = map snd raw_statements

      val binders = map fst raw_statements
                 |> map (apsnd (map ( Attrib.check_src ctxt
                                   #> Attrib.attribute ctxt )))

      val SOME (_, jj, _) = IPS_Data.get ctxt
      val nn = fold (fn (B,_) => fn N => if Binding.is_empty B then N+1 else N) binders 0
      val (binders, nn) =
            fold_map (fn (B,AT) => fn N =>
                if Binding.is_empty B
                then ((Binding.name ("fact" ^ string_of_int N), AT), N+1)
                else ((B,AT),N)) binders (!jj)
      val _ = jj := nn

      val (stmt, _) = Proof_Context.read_stmt raw_fixes raw_props ctxt
      val prop = #propss stmt
              |> flat
              |> map (atomize_term ctxt)
              |> foldr1 (fn (A, B) => \<^Const>\<open>conj\<close> $ A $ B)
              |> fold_rev (fn (_, t) => fn T =>
                    \<^Const>\<open>Ex \<open>Term.type_of (snd t)\<close>\<close> $ Term.lambda_name t T
                  ) (#vars stmt)
              |> (fn X => HOLogic.Trueprop $ X)
      val goal = Goal.init (Thm.cterm_of ctxt prop)
              |> Local_Defs.unfold_tac ctxt @{thms Ex_def conj_def}
              |> Seq.hd

      fun CB ctxt' (lem, facts', S) =
        let val lem = Goal.conclude lem
            val st' = Method.insert_tac ctxt' [lem] 1 st
                   |> Seq.hd
                   |> REPEAT_DETERM (eresolve_tac ctxt' [elim_Ex] 1)
                   |> Seq.hd
         in (ctxt', HHF (st', facts' @ facts) :: S)
         |> INTROS'' false (fn foc =>
            let val lem = case #prems foc
                            of [lem] => lem
                             | _ => error "5ViUXLLqRB+AA9ffsaEPDQ"
                fun split th =
                  case Thm.prop_of th
                    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _) =>
                        MP conjD1 th :: split (MP conjD2 th)
                     | _ => [th]
                val facts = binders ~~ map (map (fn X => ([X],[]))) (unflat raw_props (split lem))
             in #context foc
             |> Proof_Context.note_thmss "" facts
             |> apfst (map (apsnd (map Thm.prop_of)))
            end)
        end
      fun PRT t = BUNDL ([], [], [t, print_stack [HHF (st,facts)]])
               |> augment_print (map (apsnd Term.fastype_of o snd) (#vars stmt),
                                 [])
   in (ctxt, HHF (goal, []) :: ENDBLK :: MAGIC (CB, PRT) :: S)
  end
  | OBTAIN' _ _ _ = raise BROKEN_INVARIANT

val OBTAIN = OPR oo OBTAIN'
val OBTAIN_CMD =
        K (Parse.vars --| Parse.where_ -- Parse_Spec.statement
     >> (fn (vs,ss) => OBTAIN vs ss))

(* CONSIDER *)

val elim_disj = @{lemma \<open>disj P Q \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> (Q \<Longrightarrow> C) \<Longrightarrow> C\<close>
                     by (unfold disj_def, blast)}

(*
fun CONSIDER' raw_terms (ctxt, HHF (st,facts,IA) :: SK) =
  let val terms = Syntax.read_props ctxt raw_terms
               |> map (atomize_term ctxt)
      val goal  = foldr1 (fn (A, B) => \<^Const>\<open>HOL.disj\<close> $ A $ B ) terms
               |> HOLogic.mk_Trueprop
               |> Thm.cterm_of ctxt
               |> Goal.init

      val SOME (ii, _, _) = IPS_Data.get ctxt
      val binder = Binding.name (assm_name (!ii))
      val _ = ii := (!ii) + 1

      fun CB ctxt' (lem, facts', _, S) =
        let val lem = Goal.conclude lem
            val st' = Method.insert_tac ctxt' [lem] 1 st
                   |> Seq.hd
                   |> REPEAT_DETERM (eresolve_tac ctxt' [elim_Ex] 1)
                   |> Seq.hd
         in (ctxt', HHF (st', facts' @ facts, IA) :: S)
         |> INTROS'' (fn foc =>
            let val lem = case #prems foc
                            of [lem] => lem
                             | _ => error "5ViUXLLqRB+AA9ffsaEPDQ"
                fun split th =
                  case Thm.prop_of th
                    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>conj\<close>, _) $ _ $ _) =>
                        MP conjD1 th :: split (MP conjD2 th)
                     | _ => [th]
                val facts = binders ~~ map (map (fn X => ([X],[]))) (unflat raw_props (split lem))
             in #context foc
             |> Proof_Context.note_thmss "" facts
             |> apfst (map (apsnd (map Thm.prop_of)))
            end)
        end
      fun PRT t = BUNDL ([], [], [t, print_stack [HHF (st,facts,IA)]])
               |> augment_print (map (apsnd Term.fastype_of o snd) (#vars stmt),
                                 [])
   in (ctxt, HHF (goal, [], false) :: ENDBLK :: MAGIC (CB, PRT) :: SK)
  end
*)

(* HAMMER *)

fun HAMMER_i step_id (ctxt, HHF (s,facts) :: S) =
  let val SOME (_, _, ID_BASE) = IPS_Data.get ctxt
      val ID = ID_BASE ^ "/" ^ step_id
      val s' = Phi_Sledgehammer_Solver.auto (SOME ID) ctxt s
   in maintain (ctxt, HHF (s', facts) :: S)
  end

fun HAMMER_all step_id =
  let val ID_BASE = string_of_int step_id ^ "/"
      fun loop j (stack as (_, HHF (s,_) :: _)) =
        if Thm.no_prems s then stack
        else HAMMER_i (ID_BASE ^ string_of_int j) stack
          |> HAMMER_all (j+1)
        | loop _ _ = raise BROKEN_INVARIANT
   in loop 0
  end

val HAMMER = OPR_ID (HAMMER_i o string_of_int)
val HAMMER_CMD = K (Scan.succeed HAMMER)

(* END *)

fun END' ID (stack as (_, HHF _ :: _)) =
  let val (ctxt, SK'1) = HAMMER_all ID stack
   in case SK'1
   of HHF s :: ENDBLK :: SK' => maintain (ctxt, HHF s :: SK')
    | _ => raise BROKEN_INVARIANT
  end
  | END' _ S = raise BROKEN_INVARIANT

val END = OPR_ID END'
val END_CMD = K (Scan.succeed END)

(* PRINT *)


fun fixes_is_outdated ctxt var_name =
  Name.is_skolem var_name andalso Variable.revert_fixed ctxt var_name = var_name

fun contains_outdated_fixes ctxt term =
  let val vars = Term.add_free_names term []
   in exists (fixes_is_outdated ctxt) vars
  end

fun ap2_3 f (a,b,c) = (a, f b, c)

fun pretty_state ctxt tree =
  let open Pretty
      val atom_goals = Config.get ctxt atomize_goals
      val prt_typ = Syntax.pretty_typ ctxt
      val prt_term= Syntax.pretty_term ctxt o (atom_goals ? Object_Logic.atomize_term ctxt)
      fun prt_bundle (vars, facts, term) =
        let val prems = Logic.strip_imp_prems term
            val tails =
                 (if null vars   then [] else [keyword1 "fixed variables"])
                @ map (fn (N,T) => item [str N, brk 1, str "::", brk 1, prt_typ  T]) vars
                @ (if null facts then [] else [keyword1 "contextual facts"])
                @ map (fn (N,[])  => item [str N, brk 1, str ":", brk 1, str "<empty>"]
                        | (N,[T]) => item [str N, brk 1, str ":", brk 1, prt_term T]
                        | (N,TS)  => item [str N, brk 1, str ":", brk 1, chunks (map prt_term TS)]
                      ) facts
         in case prems
         of [] => str "All goals are proven!"
          | [goal] => chunks ( block [keyword1 "goal: ", prt_term goal] :: tails)
          | _  => chunks (
              keyword1 "goals: " ::
              map (fn X => item [prt_term X]) prems
              @ tails)
        end
      fun collect V F (PROP  (V',F',term)) = (V' @ V, F' @ F, term)
        | collect V F (BUNDL (V',F',chil)) = collect (V' @ V) (F' @ F) (hd chil)
   in collect [] [] tree
   |> ap2_3 (map (apsnd (filter_out (contains_outdated_fixes ctxt)))
          #> filter_out (null o snd))
   |> prt_bundle
  end

fun PRINT (state as ((ctxt,SK), _, ID)) =
  let open Pretty
   in Pretty.writeln (chunks [
        block [keyword1 "proof state after step ", str (string_of_int ID)],
        pretty_state ctxt (print_stack SK)
      ])
    ; state
  end
val PRINT_CMD = K  (Scan.succeed PRINT)

(** Toplevel **)

(* Interfaces *)

val CMDS = Symtab.make [
      ("end",     END_CMD),
      ("obtain",  OBTAIN_CMD),
      ("have",    HAVE_CMD),
      ("END",     END_CMD),
      ("OBTAIN",  OBTAIN_CMD),
      ("HAVE",    HAVE_CMD),
      ("CASE_SPLIT",    CASE_CMD),
      ("INDUCT",  INDUCT_CMD),
      ("CRUSH",   CRUSH_CMD),
      ("INTROS",  INTROS_CMD),
      ("HAMMER",  HAMMER_CMD),
      ("PRINT",   PRINT_CMD)
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
           (("for",   \<^here>), quasi_command_spec),

           (("end",   \<^here>), command_spec (thy_end, [])),
           (("obtain",\<^here>), command_spec (prf_asm_goal, [])),
           (("have",  \<^here>), command_spec (prf_goal, [])),
           (("END",   \<^here>), command_spec (thy_end, [])),
           (("OBTAIN",\<^here>), command_spec (prf_asm_goal, [])),
           (("HAVE",  \<^here>), command_spec (prf_goal, [])),
           (("CASE_SPLIT",  \<^here>), command_spec (prf_goal, [])),
           (("INDUCT",\<^here>), command_spec (prf_goal, [])),
           (("CRUSH", \<^here>), command_spec (prf_goal, [])),
           (("INTROS",\<^here>), command_spec (prf_goal, [])),
           (("HAMMER",\<^here>), command_spec (prf_goal, [])),
           (("PRINT", \<^here>), command_spec (prf_goal, []))
         ]
     end

fun parse_cmds ctxt source =
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

      val cmds = split [] [] toks
              |> map (fn (h::toks) =>
                    case Symtab.lookup CMDS (Token.content_of h)
                      of SOME parser => fst (parser ctxt toks)
                       | NONE => error ("Bad Command " ^ Token.content_of h) )
   in fold_rev I cmds
  end

fun METHOD_i tr : Method.method = CONTEXT_METHOD (fn _ => fn (ctxt,st) =>
  if Thm.no_prems st
  then Seq.single (Seq.Result (ctxt, st))
  else Seq.make (fn () =>
        INIT ctxt st
     |> tr
     |> (fn ((ctxt', S  as [HHF (st',_)]),_,_) =>
             (Pretty.writeln (pretty_state ctxt' (print_stack S));
              SOME (Seq.Result (ctxt',st'), Seq.empty))
          | ((ctxt', S), _, _) =>
             (Pretty.writeln (pretty_state ctxt' (print_stack S));
              error "incomplete MINSHELL script") ) ))

val METHOD = METHOD_i oo parse_cmds

val _ = Theory.setup (
  Method.setup \<^binding>\<open>min_script\<close> (
    Scan.peek (fn ctxt => Parse.embedded >> (fn src => fn _ =>
        METHOD ctxt src)))
  ""
)

end