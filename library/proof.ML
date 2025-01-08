signature IPS_PROOF = sig

type stack
type state
type operation = state -> state
type parse_ctxt = Context.generic
type command = parse_ctxt -> operation parser

exception OPR_FAIL of string

(* options *)

val atomize_goals : bool Config.T
val END_completes_all_NEXT : bool Config.T

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

val CONSIDER : (
               (binding * string option * mixfix) list
             * (binding * string option * mixfix) list
             * (string * string list) list list
             * ((binding * Token.src list) * (string * string list) list) list
             ) list
          -> operation
val CONSIDER_CMD : command

val HAMMER : operation
val HAMMER_CMD : command

val END : operation
val END_CMD : command

val NXT : operation
val NXT_CMD : command

val PRINT : operation
val PRINT_CMD : command

val RULE : (Facts.ref * Token.src list) list -> (Facts.ref * Token.src list) list -> operation
val RULE_CMD : command

(* Toplevel *)

val parse_cmds : parse_ctxt -> string -> operation
val PROVE : operation -> Proof.context -> thm -> thm

val METHOD : parse_ctxt -> string -> Method.method

end

structure IPS_Proof : IPS_PROOF = struct

val assm_N = "assm"
fun assm_name i = assm_N ^ string_of_int i

(* options *)

val atomize_goals = Attrib.setup_config_bool \<^binding>\<open>min_shell_atomize_goals\<close> (K true)
val END_completes_all_NEXT = Attrib.setup_config_bool \<^binding>\<open>END_completes_all_NEXT\<close> (K true)

(*only for printing*)
type variables = (string * typ) list
type local_facts = (string * term list) list
type pctxt = variables * local_facts
datatype tree = PROP  of pctxt * term (*goal*)
              | BUNDL of pctxt * tree list

datatype endblk_type = T_END | T_NXT
datatype frame = HHF   of thm (*a local_facts bundle node, represented as a Hereditary Harrop Formula*)
                        * pctxt
               | MAGIC of (Proof.context -> thm * pctxt * frame list -> Proof.context * frame list)
                        * (tree -> tree)
               | ENDBLK of endblk_type

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
fun INIT c st = ((init_ctxt c st, [HHF (st, ([],[])), ENDBLK T_END]), Symtab.empty, 0)
fun INIT'  st = INIT (Proof.context_of st) (#goal (Proof.simple_goal st))

fun beta_eta_contract th =
  if Term.could_beta_eta_contract (Thm.prop_of th)
  then Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th
  else th

(*Modus Ponens*)
fun MP thAB thA =
  let val LHS = Thm.cprop_of thAB
             |> Thm.dest_arg1
      val inst = Thm.match (LHS, Thm.cprop_of thA)
      val thAB' = Thm.instantiate inst thAB
   in Thm.implies_elim (beta_eta_contract thAB') (beta_eta_contract thA)
  end

(* fun join_lstR pr = AList.join (op =) (fn _ => fn (_,x) => x) pr *)
fun join_lstL pr = AList.join (op =) (fn _ => fn (x,_) => x) pr

fun cat_pctxt (vs',hs') (vs,hs)
      = (join_lstL (vs, vs'), hs' @ hs)
fun augment_print pctxt' (PROP (pctxt, goal))
      = (PROP  (cat_pctxt pctxt' pctxt, goal))
  | augment_print pctxt' (BUNDL (pctxt, goal))
      = (BUNDL (cat_pctxt pctxt' pctxt, goal))

fun maintain (c,[]) = (c,[])
  | maintain (origin as (ctxt, HHF (st, pctxt) :: L)) =
    ( case Thm.nprems_of st
        of 0 => (case L
            of [] => origin
             | (HHF (st1, pctxt') :: L') =>
                  maintain (ctxt, HHF (MP st1 st, cat_pctxt pctxt' pctxt) :: L')
             | (MAGIC (cb,_) :: L') =>
                  (case cb ctxt (st, pctxt, L') of (ctxt', S) => maintain (ctxt', S) )
             | ENDBLK _ :: _ => origin )
         | _ => origin)
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

(*fix local variables & facts*)
fun INTROS'' F all_subgoals (origin as (ctxt, HHF (st, pctxt) :: L)) =
     (case Thm.nprems_of st
        of 0 => origin
         | _ => if Thm.nprems_of st > 1 orelse need_intro st
                then let val (foc, st') = Subgoal.focus_prems ctxt 1 NONE st
                         val PRT = augment_print (map (apsnd Thm.typ_of_cterm) (#params foc), [])
                         val (st'', (pctxt', ctxt')) = F (st', foc)
                         fun CB ctxt'' (st'',_,S) =
                          let val st'3 = singleton (Proof_Context.export ctxt'' ctxt') st''
                           in (ctxt, HHF (
                                     Subgoal.retrofit ctxt'' ctxt (#params foc) (#asms foc) 1 st'3 st
                                  |> Seq.hd,
                                ([],[])) :: S)
                           |> all_subgoals ? INTROS'' F all_subgoals
                          end
                      in (ctxt', HHF (st'', cat_pctxt pctxt' pctxt) :: MAGIC (CB,PRT) :: L)
                     end
                else (ctxt, HHF (st, pctxt) :: L)
      )
  | INTROS'' _ _ _ = raise BROKEN_INVARIANT

val INTROS' = INTROS'' (fn (st, foc) =>
  let val ctxt = #context foc
      val SOME (ii,_,_) = IPS_Data.get ctxt
      val i = !ii
      val _ = ii := i + 1
   in ctxt
   |> Proof_Context.note_thms "" ((Binding.name (assm_name i), []),
                                  map (fn th => ([th], [])) (#prems foc))
   |> apfst (apsnd (map Thm.prop_of) #> single #> pair [])
   |> pair st
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

fun SKIP_SUCCESS F (SK as (_, HHF (st,_) :: _)) =
        if Thm.no_prems st then SK else F SK
  | SKIP_SUCCESS F SK = F SK
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

fun print_stack [] = PROP (([], []), SOLVED_GOAL)
  | print_stack (S::L) =
      let fun prt t [] = t
            | prt t (HHF (st, pctxt) :: L) =
                let val goals = case Thm.prems_of st
                                  of [] => raise BROKEN_INVARIANT
                                   | (_::prems) => prems
    
                    val nodes = map (fn goal => PROP (([],[]), goal)) goals
                 in prt (BUNDL (pctxt, t::nodes)) L
                end
            | prt t (MAGIC (_, PRT) :: L) = prt (PRT t) L
            | prt t (ENDBLK _ :: L) = prt t L
          fun prt0 (HHF (st, pctxt)) = PROP (pctxt, Thm.prop_of st)
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
   |> SKIP_SUCCESS (INTROS' true)
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

(* RULE *)

fun RULE'_i rules facts =
  apply' (fn s => CONTEXT_TACTIC (HEADGOAL (Classical.rule_tac (#1 s) rules facts)) s) NONE

fun RULE' raw_rules raw_facts (SK as (ctxt, _)) =
  let val rules = Attrib.eval_thms ctxt raw_rules
      val facts = Attrib.eval_thms ctxt raw_facts
   in RULE'_i rules facts SK
  end

val RULE = OPR oo RULE'
val RULE_CMD = let open Parse
      in K ( Scan.optional thms1 []
          -- Scan.optional (($$$ "with" || $$$ "WITH") |-- thms1) [] >> uncurry RULE) end


(* HAVE *)

fun HAVE' _ _ (ctxt, []) = (ctxt, [])
  | HAVE' raw_name expr (ctxt, HHF (G,pctxt) :: S) =
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
          fun CB ctxt' (st',(*pctxt'*) _,S) =
            let val ((name,[thm]), ctxt'') =
                        Proof_Context.note_thms "" (name, [([Goal.conclude st'],[])]) ctxt'
             in (ctxt'', HHF (G, cat_pctxt ([], [(name, [Thm.prop_of thm])]) pctxt) :: S)
            end
          fun PRT t = BUNDL (pctxt, [t, print_stack [HHF (G,([],[]))]])
       in (ctxt, HHF (goal, ([],[])) :: ENDBLK T_END :: MAGIC (CB, PRT) :: S)
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


(* can be cached *)
(*
fun mk_obtain_rule ctxt CN EN =
  let val TS = List.tabulate (EN, fn i =>
                  (i, TVar (("'x" ^ string_of_int i, 0), \<^sort>\<open>type\<close>)))
      fun var TS name = Var((name,0), (map #2 TS) ---> \<^Type>\<open>bool\<close>)
                     |> fold (fn (i,_) => fn X => X $ Bound (EN - 1 - i)) TS
      val C = HOLogic.mk_Trueprop (var [] "C")
      val PS = List.tabulate (CN, fn i => var TS ("P" ^ string_of_int i))
      fun import_vars ctxt th =
        let val ((_, [th']), ctxt') = ctxt |> Variable.set_body false |> Variable.import true [th];
         in (ctxt', th') end;

   in foldr1 (fn (A,B) => \<^Const>\<open>conj\<close> $ A $ B) PS
   |> fold_rev (fn (i,T) => fn X => \<^Const>\<open>Ex T\<close> $ Abs ("x" ^ string_of_int i, T, X)) TS
   |> (fn X => Logic.mk_implies (HOLogic.mk_Trueprop X, C))
   |> Thm.cterm_of ctxt
   |> Thm.trivial
   |> import_vars ctxt
   |-> (fn ctxt' => fn th => th
   |> Seq.REPEAT (Thm.biresolution NONE true [(true, @{thm exE}), (true, @{thm conjE})] 1)
   |> Seq.hd
   |> Thm.permute_prems 0 1
   |> singleton (Variable.export ctxt' ctxt))
  end
*)

(* can be cached *)
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
              [(true, @{thm exE}), (true, @{thm conjE}), (true, @{thm disjE})]))
   |> Seq.hd
   |> Thm.permute_prems 0 ~1
   |> singleton (Variable.export ctxt' ctxt))
  end

(*
val elim_Ex = @{lemma \<open>Ex (\<lambda>x. P x) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q\<close>
                   by (unfold Ex_def, blast)}
val conjD1 = @{lemma \<open>conj A B \<Longrightarrow> A\<close> by (unfold conj_def, blast)}
val conjD2 = @{lemma \<open>conj A B \<Longrightarrow> B\<close> by (unfold conj_def, blast)}
*)

(*
local val prop_def = @{thm prop_def}
   in val protect_goal   = Conv.gconv_rule (Conv.rewr_conv (Thm.symmetric prop_def))
      val unprotect_goal = Conv.gconv_rule (Conv.rewr_conv prop_def)
end
*)

(* raw_decls raw_fixes raw_prems raw_statements *)

fun CONSIDER' raw_dnf (ctxt0, HHF (st0, pctxt0) :: S) =
  let val SOME (_, jj, _) = IPS_Data.get ctxt0
      fun parse (raw_decls, raw_fixes, raw_prems, raw_statements) ctxt =
        let val raw_props = map snd raw_statements
      
            val binders = map fst raw_statements
                       |> map (apsnd (map ( Attrib.check_src ctxt
                                         #> Attrib.attribute ctxt )))
      
            val (binders, nn) =
                  fold_map (fn (B,AT) => fn N =>
                      if Binding.is_empty B
                      then ((Binding.name ("fact" ^ string_of_int N), AT), N+1)
                      else ((B,AT),N)) binders (!jj)
            val _ = jj := nn
      
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

      val goal = map (#1 o #4) conj_clauses
              |> foldr1 (fn (A,B) => \<^Const>\<open>disj\<close> $ A $ B)
              |> (fn X => HOLogic.Trueprop $ X)
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
      fun PRT0 sgs t = BUNDL (pctxt0, t :: sgs)
      fun CB _ _ [] _  _ = raise BROKEN_INVARIANT
        | CB initial sgs
             ((cparams, _, (decls, fixes, AS, raw_props, binds, binders), _) :: remain_clauses)
             ctxt' (lem, _, S) =
            let val rule' = lem
                         |> Goal.conclude
                         |> singleton (Proof_Context.export ctxt' ctxt0)
                         |> initial ? MP rule0
                fun export a b =
                    let val (A,B) = Obtain.obtain_export ctxt0 rule' cparams a b 
                        fun export_thm thm =
                          let val protected = (case Thm.prop_of thm
                                                 of \<^Const>\<open>Pure.prop\<close> $ _ => true
                                                  | _ => false)
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
                val pctxt'3 = (map (apsnd Term.fastype_of o snd) decls,
                               map (apsnd (map Thm.prop_of)) new_facts)
                           |> null remain_clauses ? (fn X => cat_pctxt X pctxt0)
             in (ctxt'3, HHF (st0, pctxt'3)
                          :: (case remain_clauses
                                of [] => S
                                 |  _ =>    ENDBLK T_NXT
                                         :: MAGIC (CB false (tl sgs) remain_clauses, PRT0 sgs)
                                         :: S))
            end

   in (ctxt_rule,
          HHF (goal,([],[]))
       :: ENDBLK (case conj_clauses of [_] => T_END | _ => T_NXT)
       :: MAGIC (CB true subgoals conj_clauses, PRT0 subgoals) :: S)
  end
  | CONSIDER' _ _ = raise BROKEN_INVARIANT

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));

val CONSIDER = OPR o CONSIDER'
val CONSIDER_CMD = K (fn toks => (
     Parse.enum1 "|"
        (Scan.optional (Parse.vars --| Parse.where_) []
          -- structured_statement
        >> (fn (vs,(a,b,c)) => (vs,a,b,c)))
     >> CONSIDER) toks)

(* CONSIDER *)

(*
val elim_disj = @{lemma \<open>disj P Q \<Longrightarrow> (P \<Longrightarrow> C) \<Longrightarrow> (Q \<Longrightarrow> C) \<Longrightarrow> C\<close>
                     by (unfold disj_def, blast)}


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
  | HAMMER_i _ _ = raise BROKEN_INVARIANT

fun HAMMER_all step_id =
  let val ID_BASE = step_id ^ "/"
      fun loop j (stack as (_, HHF (s,_) :: _)) =
        if Thm.no_prems s then stack
        else HAMMER_i (ID_BASE ^ string_of_int j) stack
          |> loop (j+1)
        | loop _ _ = raise BROKEN_INVARIANT
   in loop 0
  end

val HAMMER = OPR_ID (HAMMER_i o string_of_int)
val HAMMER_CMD = K (Scan.succeed HAMMER)

(* END *)

fun END' T jj ID (stack as (_, HHF _ :: _)) =
  let val ID_BASE = if jj = 0 then string_of_int ID 
                    else string_of_int ID ^ "+" ^ string_of_int jj
      val (ctxt, SK'1) = HAMMER_all ID_BASE stack
   in case SK'1
   of HHF s :: ENDBLK T' :: SK' =>
           if T = T' then maintain (ctxt, HHF s :: SK')
           else if T = T_END andalso T' = T_NXT andalso Config.get ctxt END_completes_all_NEXT
           then maintain (ctxt, HHF s :: SK')
             |> END' T_END (jj+1) ID
           else raise OPR_FAIL (
                  "This block should be closed by the " ^
                  (case T' of T_END => "END" | T_NXT => "NEXT") ^
                  " command.")
    | _ => raise BROKEN_INVARIANT
  end
  | END' _ _ _ _ = raise BROKEN_INVARIANT

val END = OPR_ID (END' T_END 0)
val NXT = OPR_ID (END' T_NXT 0)
val END_CMD = K (Scan.succeed END)
val NXT_CMD = K (Scan.succeed NXT)

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
      fun collect V F (PROP  ((V',F'),term)) = (V' @ V, F' @ F, term)
        | collect V F (BUNDL ((V',F'),chil)) = collect (V' @ V) (F' @ F) (hd chil)
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
      ("next",    NXT_CMD),
      ("consider",CONSIDER_CMD),
      ("have",    HAVE_CMD),
      ("END",     END_CMD),
      ("NEXT",    NXT_CMD),
      ("CONSIDER",CONSIDER_CMD),
      ("HAVE",    HAVE_CMD),
      ("CASE_SPLIT",    CASE_CMD),
      ("INDUCT",  INDUCT_CMD),
      ("CRUSH",   CRUSH_CMD),
      ("INTROS",  INTROS_CMD),
      ("HAMMER",  HAMMER_CMD),
      ("PRINT",   PRINT_CMD),
      ("RULE",    RULE_CMD)
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
           (("with",  \<^here>), quasi_command_spec),
           (("WITH",  \<^here>), quasi_command_spec),

           (("end",   \<^here>), command_spec (thy_end, [])),
           (("next",  \<^here>), command_spec (thy_end, [])),
           (("consider",\<^here>),command_spec (prf_asm_goal, [])),
           (("have",  \<^here>), command_spec (prf_goal, [])),
           (("END",   \<^here>), command_spec (thy_end, [])),
           (("NEXT",  \<^here>), command_spec (thy_end, [])),
           (("CONSIDER",\<^here>),command_spec (prf_asm_goal, [])),
           (("HAVE",  \<^here>), command_spec (prf_goal, [])),
           (("CASE_SPLIT",  \<^here>), command_spec (prf_goal, [])),
           (("INDUCT",\<^here>), command_spec (prf_goal, [])),
           (("CRUSH", \<^here>), command_spec (prf_goal, [])),
           (("INTROS",\<^here>), command_spec (prf_goal, [])),
           (("HAMMER",\<^here>), command_spec (prf_goal, [])),
           (("PRINT", \<^here>), command_spec (prf_goal, [])),
           (("RULE",  \<^here>), command_spec (prf_goal, []))
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

fun PROVE tr ctxt st =
      INIT ctxt st
   |> tr
   |> (fn ((ctxt', S  as [HHF (st',_)]),_,_) =>
          let val st'' = singleton (Proof_Context.export ctxt' ctxt) st'
           in Pretty.writeln (pretty_state ctxt' (print_stack S));
              st''
          end
        | ((ctxt', S), _, _) =>
           (Pretty.writeln (pretty_state ctxt' (print_stack S));
            error "incomplete MINSHELL script") )

fun METHOD_i tr : Method.method = CONTEXT_METHOD (fn _ => fn (ctxt,st) =>
  if Thm.no_prems st
  then Seq.single (Seq.Result (ctxt, st))
  else Seq.make (fn () =>
        SOME (Seq.Result (ctxt, PROVE tr ctxt st), Seq.empty)))

val METHOD = METHOD_i oo parse_cmds

val _ = Theory.setup (
  Method.setup \<^binding>\<open>min_script\<close> (
    Scan.peek (fn ctxt => Parse.embedded >> (fn src => fn _ =>
        METHOD ctxt src)))
  ""
)

end