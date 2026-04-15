signature MINILANG_AUX = sig
include MINILANG_AUX

val variant_name : string -> Name.context -> string * Name.context
val variant_name_list : string list -> string list -> string list
val variant_factname : Proof.context -> string -> string

val induction_tac:
    (string * string list) list Unsynchronized.ref ->
    bool ->
    (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> context_tactic

val xOF : bool -> Proof.context -> thm list -> thm -> thm
val xof : Proof.context -> string option list * string option list ->
    (binding * string option * mixfix) list -> thm -> thm

val xwhere : Proof.context ->
      ((indexname * Position.T) * (string * string)) list ->
        (binding * string option * mixfix) list ->
          thm -> thm

val inst_hol_alls : Proof.context -> (string * cterm) list -> thm -> thm
val inst_universal_quantifiers : Proof.context -> (indexname * term) list -> thm -> thm
val inst_universal_quantifiers' : Proof.context -> (indexname * string) list -> thm -> thm

val print_toks : Token.src -> string list
val trim_markup : string -> string
val method_sorry : Method.text

val ind_synt' :
      (bool * ((binding option * (term * bool)) option list list *
        (((string * typ) list list * term option list) *
         thm list option))) context_parser
val ind_synt : Context.generic ->
        (bool * ((binding option * (term * bool)) option list list
          * (((string * typ) list list * term option list) *
            thm list option))) parser
val rule_of_ind : Context.generic -> Token.T list -> thm list option
val case_synt' : (bool * (term option list list * thm option)) context_parser
val case_synt : Context.generic -> (bool * (term option list list * thm option)) parser

val simp_fact_name' : string -> string
val simp_fact_name : Proof.context -> string -> string

val flatten_facts : (string * term list) list -> (string * term) list
val base_name : string -> string
val filter_redundant_facts : (string * term) list -> (string * term) list

val implode_with' : 'a -> 'a list list -> 'a list -> 'a list
val implode_with : 'a -> 'a list list -> 'a list

end

structure Minilang_Aux : MINILANG_AUX = struct
open Minilang_Aux

fun trim_markup msg =
  let fun auto _ [] = []
        | auto acc (#"\127" :: L) = auto acc L
        | auto acc (#"\005" :: L) = auto (not acc) L
        | auto true (x :: L) = x :: auto true L
        | auto false (_ :: L) = auto false L
      val s = String.size msg
      val ex = Unsynchronized.ref false
      val i  = Unsynchronized.ref 0
      val _ = while !i < s
                 do if String.sub (msg, !i) = #"\005" orelse
                       String.sub (msg, !i) = #"\127"
                    then (ex := true ;
                           i := s)
                    else ( i := !i + 1)
   in if !ex
    then String.implode (auto true (String.explode msg))
    else msg
  end


(** Aux Isar Commands **)

local
  (* Split name into base and numeric suffix *)
  fun split_numeric_suffix name =
    let
      val len = String.size name

      (* Find the start position of trailing digits by scanning backwards *)
      val i = Unsynchronized.ref (len - 1)
      val () = while !i >= 0 andalso Char.isDigit (String.sub (name, !i)) do
        i := !i - 1
      val digit_start = !i + 1
    in
      if digit_start = len  (* no trailing digits *)
      then (name, NONE)
      else
        let
          val base = String.substring (name, 0, digit_start)
          val num_str = String.substring (name, digit_start, len - digit_start)
        in
          case Int.fromString num_str of
            SOME num => (base, SOME num)
          | NONE => (name, NONE)  (* shouldn't happen *)
        end
    end

  (* Core scaffold: accepts a predicate to check if a name is used *)
  fun variant_with_predicate is_used name =
    if name = "" then ""
    else
      let
        fun bump x =
          if is_used x
          then
            let
              val (base, num_opt) = split_numeric_suffix x
              val next_num = case num_opt of NONE => 1 | SOME n => n + 1
              val next_name = base ^ Int.toString next_num
            in
              bump next_name
            end
          else x
      in
        bump name
      end
in
  (* Public interface 1: variant using Name.context *)
  fun variant_name name name_ctxt =
    let
      val result = variant_with_predicate (Name.is_declared name_ctxt) name
      val name_ctxt' = if result = "" then name_ctxt
                       else Name.declare result name_ctxt
    in
      (result, name_ctxt')
    end

  (* Public interface 2: batch variant using Name.context *)
  fun variant_name_list used names =
    #1 (Name.make_context used |> fold_map variant_name names)

  (* Public interface 3: variant for fact names using Proof.context *)
  fun variant_factname ctxt name =
    variant_with_predicate (Facts.defined (Proof_Context.facts_of ctxt)) name
end


val ind_hypsN = "IH";

fun preds_of t =
  (case strip_comb t of
    (p as Var _, _) => [p]
  | (p as Free _, _) => [p]
  | (_, ts) => maps preds_of ts);

fun induction_tac IH_map =
  Induct.gen_induct_context_tactic (fn arg as ((cases, consumes), th) =>
    if not (forall (null o #2 o #1) cases) then arg
    else
      let
        val (prems, concl) = Logic.strip_horn (Thm.prop_of th);
        val prems' = drop consumes prems;
        val ps = preds_of concl;
  
        fun hname_of t =
          if exists_subterm (member (op aconv) ps) t
          then ind_hypsN else Rule_Cases.case_hypsN;
  
        val hnamess = map (map hname_of o Logic.strip_assums_hyp) prems';
        val n = Int.min (length hnamess, length cases);
        val cases' =
          map (fn (((cn, _), concls), hns) => ((cn, hns), concls))
            (take n cases ~~ take n hnamess);
      in IH_map := map (#1 o #1) (take n cases) ~~ take n hnamess
       ; ((cases', consumes), th)
     end);

(** Aux Attributes **)

fun beta_eta_contract_cterm x =
  if Term.could_beta_eta_contract (Thm.term_of x)
  then Thm.dest_arg (Thm.cprop_of (Drule.beta_eta_conversion x))
  else x

local

(* Discharge a single premise of [rule] using [fact].
   Fast path: ordinary OF unification.
   Fallback (when prove_discharge): construct a goal from the premise,
   insert the fact as an assumption via insert_tac, and prove with fast_mepo_tac. *)
fun discharge_one _ rule fact =
      rule OF [fact]

fun discharge_one_prove ctxt rule fact =
      (rule OF [fact])
      handle THM _ =>
        let val premise = hd (Thm.prems_of rule)
            val goal = Goal.init (Thm.cterm_of ctxt premise)
            val tac = Method.insert_tac ctxt [fact] 1
                      THEN Phi_Sledgehammer_Solver.fast_mepo_tac
                             (Time.fromSeconds 3) ctxt 1
        in case Seq.pull (tac goal)
             of SOME (st', _) =>
                  let val proved = Goal.finish ctxt st'
                  in rule OF [proved] end
              | NONE => raise THM ("the given fact mismatches the target premise",
                                   1, [fact, rule])
        end

fun discharge_all _ _ rule [] = rule
  | discharge_all discharge1 ctxt rule (fact :: rest) =
      discharge_all discharge1 ctxt (discharge1 ctxt rule fact) rest

in

fun xOF prove_discharge ctxt thms st =
  let open Conv
      val LEN = length thms
      fun rulify N ctxt ctm =
        if N <= Logic.count_prems (Thm.term_of ctm)
        then all_conv ctm
        else case Thm.term_of ctm
          of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
              (arg_conv (abs_conv (rulify N o snd) ctxt)) ctm
           | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
              (arg_conv (rulify (N-1) ctxt)) ctm
           | Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs _) =>
              (rewr_conv Thms.atomize_all'sym then_conv rulify N ctxt) ctm
           | Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) =>
              (rewr_conv Thms.atomize_imp'sym then_conv rulify N ctxt) ctm
           | _ => raise THM ("more facts are given than the number of premises of the rule",
                              LEN + 1, st :: thms)
      val discharge1 = if prove_discharge then discharge_one_prove else discharge_one
   in if LEN <= Thm.nprems_of st
    then (st OF thms
          handle THM _ =>
            if not prove_discharge then st OF thms  (* re-raise *)
            else discharge_all discharge1 ctxt st thms)
    else let
         val i = Thm.maxidx_of st + 1
         val st' = fconv_rule (rulify LEN ctxt) st
                |> Thm.forall_elim_vars i
      in (st' OF thms
          handle THM _ =>
            if not prove_discharge then st' OF thms  (* re-raise *)
            else discharge_all discharge1 ctxt st' thms)
      |> fconv_rule (Object_Logic.atomize ctxt)
     end
  end

end

fun xof ctxt (args, concl_args) fixes thm =
  let val num_var = length args - length (Term.add_vars (Thm.prop_of thm) [])
      fun spec_rule thm =
        case Thm.concl_of thm
          of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) =>
              thm RS Thms.spec
           | _ => error "More instantiations than variables in theorem"
   in thm
   |> num_var > 0 ? funpow num_var spec_rule
   |> Rule_Insts.of_rule ctxt (args, concl_args) fixes
  end

(* Instantiate HOL.All (∀) bound variables in the conclusion of a theorem.
   Takes a list of (name, cterm) pairs. For each HOL.All-bound variable matching
   a name, reorders quantifiers as needed and applies spec to instantiate it.
   Non-targeted ∀-variables are left unchanged. *)
fun inst_hol_alls ctxt insts thm =
  if null insts then thm
  else let
    fun concl_conv C ctxt ctm =
      case Thm.term_of ctm
        of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
            Conv.arg_conv (Conv.abs_conv (concl_conv C o snd) ctxt) ctm
         | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
            Conv.arg_conv (concl_conv C ctxt) ctm
         | _ => C ctxt ctm

    (* Pull a ∀ from inside ⟶ consequent(s) to the top:
       (P ⟶ ∀x. Q x) = (∀x. P ⟶ Q x)  via all_simps(6)[symmetric] *)
    fun pull_forall ctxt ctm =
      case Thm.term_of ctm of
        Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs _ => Conv.all_conv ctm
      | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
          (Conv.arg_conv (pull_forall ctxt)
           then_conv Conv.rewr_conv @{lemma "(P \<longrightarrow> (\<forall>x. Q x)) \<equiv> (\<forall>x. P \<longrightarrow> Q x)" for P Q by auto}) ctm
      | _ => Conv.all_conv ctm

    fun swap_all [] _ ctm = Conv.all_conv ctm
      | swap_all (NONE :: L) ctxt ctm =
          let fun swap [] ctm = Conv.all_conv ctm
                | swap (NONE :: L) ctm = swap L ctm
                | swap (SOME _ :: L) ctm =
                   (Conv.rewr_conv @{thm HOL.all_comm[folded atomize_eq]} then_conv
                    Conv.arg_conv (swap L)) ctm
           in (pull_forall ctxt
               then_conv Conv.arg_conv (Conv.abs_conv (swap_all L o snd) ctxt)
               then_conv swap L) ctm end
      | swap_all (SOME _ :: L) ctxt ctm =
          (pull_forall ctxt
           then_conv Conv.arg_conv (Conv.abs_conv (swap_all L o snd) ctxt)) ctm

    fun foralls (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = foralls X
      | foralls (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = foralls X
      | foralls (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, _, X)) = name :: foralls X
      | foralls (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = foralls X
      | foralls (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = foralls X
      | foralls _ = []

    val alls = foralls (Thm.concl_of thm)
            |> map (fn name =>
                case AList.lookup (op =) insts name of
                  SOME ct => SOME ct
                | NONE => NONE)

  in Conv.fconv_rule (concl_conv (fn ctxt =>
          HOLogic.Trueprop_conv (swap_all alls ctxt)) ctxt) thm
     |> fold (fn SOME ct => (fn th =>
          th RS Drule.infer_instantiate ctxt [(("x", 0), Thm.incr_indexes_cterm 1 ct)] @{thm spec})
               | NONE => I) alls
     |> Drule.zero_var_indexes
  end

fun xwhere ctxt inst0 fixes thm =
  let val vs = Term.add_var_names (Thm.prop_of thm) []
      val inst = map_filter (fn (((name,0),pos), (name',src)) =>
                                  if name = name'
                                  then NONE
                                  else SOME (((name,0),pos), src)
                              | (x, (_, src)) => SOME (x, src) ) inst0
   in if forall (fn ((name, _), _) => exists (fn name' => name' = name) vs) inst
    then Rule_Insts.where_rule ctxt inst fixes thm
    else let
      fun foralls (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = foralls X
        | foralls (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = foralls X
        | foralls (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, T, X)) = (name, T) :: foralls X
        | foralls (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = foralls X
        | foralls (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = foralls X
        | foralls _ = []
      val hol_insts = foralls (Thm.concl_of thm)
              |> map_filter (fn (name, T) =>
                  if exists (fn (((name', 0), _), _) => name' = name
                              | _ => false ) inst andalso
                     not (exists (fn (name', _) => name' = name) vs)
                  then SOME (name, Thm.var ((name, 0), Thm.ctyp_of ctxt T))
                  else NONE)
      val thm' = inst_hol_alls ctxt hol_insts thm
   in Rule_Insts.where_rule ctxt inst fixes thm'
  end
  end

(* Instantiate universal quantifiers and schematic variables in a theorem by name.
   Handles three kinds of variables:
   - Pure.all (⋀x. ...) — outermost meta-level quantifiers
   - HOL.All (∀x. ...) — object-level quantifiers in the conclusion
   - Schematic variables (?x) — anywhere in the theorem
   Each instantiation is classified automatically based on where the variable name
   appears in the theorem. *)
fun inst_universal_quantifiers ctxt insts thm =
  let
    val prop = Thm.prop_of thm

    (* === Classification === *)

    val schematic_vars = Term.add_vars prop []

    fun strip_pure_alls (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs(name, T, body)) =
          (name, T) :: strip_pure_alls body
      | strip_pure_alls (Const(\<^const_name>\<open>Pure.all\<close>, Type(_, [T, _])) $ _) =
          ("_", T) :: []  (* eta-contracted *)
      | strip_pure_alls _ = []
    val pure_all_vars = strip_pure_alls prop

    fun get_body (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs(_, _, body)) = get_body body
      | get_body (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ body) = get_body body
      | get_body t = t
    fun strip_hol_alls (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = strip_hol_alls X
      | strip_hol_alls (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = strip_hol_alls X
      | strip_hol_alls (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs(name, T, X)) =
          (name, T) :: strip_hol_alls X
      | strip_hol_alls _ = []
    val hol_all_vars = strip_hol_alls (get_body prop)

    fun classify ((idx as (name, _)), t) =
      if exists (fn (idx', _) => idx = idx') schematic_vars
      then (1, idx, t)
      else if exists (fn (n, _) => n = name) pure_all_vars
      then (2, idx, t)
      else if exists (fn (n, _) => n = name) hol_all_vars
      then (3, idx, t)
      else error ("Variable " ^ Term.string_of_vname idx ^ " is not found in the rule")

    val classified = map classify insts
    val schematic_insts = map_filter (fn (1, idx, t) => SOME (idx, t) | _ => NONE) classified
    val pure_insts = map_filter (fn (2, (name,_), t) => SOME (name, t) | _ => NONE) classified
    val hol_insts = map_filter (fn (3, (name,_), t) => SOME (name, t) | _ => NONE) classified

    (* === Phase 1: Instantiate outermost Pure.all variables === *)
    fun inst_pure insts thm =
      if null insts then thm
      else let
        fun process thm =
          case Thm.prop_of thm of
            Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs(name, T, _) =>
              (case AList.lookup (op =) insts name of
                SOME t =>
                  process (Thm.forall_elim (Thm.cterm_of ctxt t) thm)
              | NONE =>
                  let val frees = Term.add_free_names (Thm.prop_of thm) []
                      val name' = singleton (Name.variant_list frees) name
                      val free_ct = Thm.cterm_of ctxt (Free(name', T))
                      val thm' = process (Thm.forall_elim free_ct thm)
                   in Thm.forall_intr free_ct thm' end)
          | _ => thm
      in process thm end

    val thm1 = inst_pure pure_insts thm
               handle THM (msg, _, _) =>
                 error ("type mismatch in instantiation of meta-universal (\<And>) \
                        \variable:\n  " ^
                        String.translate (fn #"\n" => "\n  " | c => str c) msg)

    (* === Phase 2: Instantiate schematic variables ===
       Must happen before HOL.All phase, because inst_hol_alls uses RS which
       bumps schematic variable indices. *)
    fun inst_schematic insts thm =
      if null insts then thm
      else let
        val var_names = Term.add_var_names (Thm.prop_of thm) []
        val _ = map (fn (idx, _) =>
          if member (op =) var_names idx then ()
          else error ("Variable " ^ Term.string_of_vname idx ^ " is not found in the rule"))
          insts
        val ct_insts = map (fn (idx, t) => (idx, Thm.cterm_of ctxt t)) insts
      in Drule.infer_instantiate ctxt ct_insts thm
         handle THM (msg, _, _) =>
           let val cleaned =
                 perhaps (try (unprefix "infer_instantiate_types: ")) msg
               val indented =
                 String.translate (fn #"\n" => "\n  " | c => str c) cleaned
           in error ("type mismatch in instantiation:\n  " ^ indented) end
      end

    val thm2 = inst_schematic schematic_insts thm1

    (* === Phase 3: Instantiate HOL.All variables in conclusion === *)
    val hol_cterm_insts = map (fn (name, t) => (name, Thm.cterm_of ctxt t)) hol_insts
    val thm3 = inst_hol_alls ctxt hol_cterm_insts thm2
               handle THM (msg, _, _) =>
                 error ("type mismatch in instantiation of HOL-universal (\<forall>) \
                        \variable:\n  " ^
                        String.translate (fn #"\n" => "\n  " | c => str c) msg)

  in thm3 end

fun inst_universal_quantifiers' ctxt insts thm =
  let val (idxs, raws) = ListPair.unzip insts
      val terms = Syntax.read_terms (Proof_Context.set_mode Proof_Context.mode_pattern ctxt) raws
   in inst_universal_quantifiers ctxt (idxs ~~ terms) thm
  end



fun print_toks [] = []
  | print_toks toks =
  let open Token Position
      fun assmble _ [] = []
        | assmble NONE (tok :: toks) =
            let val pos  = pos_of tok
             in case (line_of pos, end_offset_of pos)
             of (SOME line, SOME ofst') =>
                     " " :: unparse tok :: assmble (SOME (line, ofst')) toks
              | _ => " " :: unparse tok :: assmble NONE toks
            end
        | assmble (SOME (line0, ofst0)) (tok :: toks) =
            let val pos  = pos_of tok
             in case (line_of pos, offset_of pos, end_offset_of pos)
             of (SOME line, SOME ofst, SOME ofst') =>
                  if line = line0 andalso ofst0 = ofst
                  then unparse tok :: assmble (SOME (line, ofst')) toks
                  else " " :: unparse tok :: assmble (SOME (line, ofst')) toks
              | _ => " " :: unparse tok :: assmble NONE toks
            end
   in tl (assmble NONE toks)
  end


val method_sorry = Method.Basic (fn _ =>
      CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      TACTIC_CONTEXT ctxt (ALLGOALS (Skip_Proof.cheat_tac ctxt) st)))


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



in

val ind_synt' =
      (Scan.lift (Args.mode Induct.no_simpN) --
      (Parse.and_list' (Scan.repeat (unless_more_args def_inst)) --
        (arbitrary -- taking -- Scan.option induct_rule)))

fun ind_synt ctxt toks = case ind_synt' (ctxt, toks) of (x, (_, toks)) => (x,toks)
fun rule_of_ind ctxt toks =
  case ind_synt ctxt toks
    of ((_, (_, ((_, _), opt_rule))), _) => opt_rule

val case_synt' =
      (Scan.lift (Args.mode Induct.no_simpN) --
        (Parse.and_list' (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule))

fun case_synt ctxt toks = case case_synt' (ctxt, toks) of (x, (_, toks)) => (x,toks)

fun simp_fact_name' name =
  if String.isPrefix "local." name
  then String.substring (name, 6, size name - 6)
  else name

fun simp_fact_name ctxt name =
  if String.isPrefix "local." name
  then let
      val name' = String.substring (name, 6, size name - 6)
      val ths  = Proof_Context.get_thms ctxt name
      val ths' = Proof_Context.get_thms ctxt name'
   in if eq_list (Thm.equiv_thm (Proof_Context.theory_of ctxt)) (ths, ths')
     then name'
     else name
  end
  else name

(* Flatten facts: convert (string * term list) list to (string * term) list with indexing *)
(* Also applies simp_fact_name' to strip "local." prefix from all names *)
fun flatten_facts (facts: (string * term list) list) : (string * term) list =
  maps (fn (name, terms) =>
    let val simp_name = simp_fact_name' name
    in case terms of
      [single_term] => [(simp_name, single_term)]
    | _ => map_index (fn (i, term) =>
            (String.concat [simp_name, "(", string_of_int (i + 1), ")"], term)) terms
    end
  ) facts

(* Extract base name from indexed name like "that(1)" -> "that" *)
fun base_name name =
  case String.tokens (fn c => c = #"(") name of
    [base, _] => base
  | _ => name

(* Filter out redundant "that" and "assms" entries that just alias other facts *)
(* Works on flattened (string * term) list with indexed names *)
fun filter_redundant_facts (local_facts: (string * term) list) : (string * term) list =
  let
    (* Collect all terms NOT from "that" *)
    val other_than_that =
      local_facts
        |> filter (fn (name, _) => base_name name <> "that")
        |> map #2
        |> distinct (op aconv)

    (* Collect all terms NOT from "that" or "assms" *)
    val other_than_that_assms =
      local_facts
        |> filter (fn (name, _) =>
            let val base = base_name name
            in base <> "that" andalso base <> "assms" end)
        |> map #2
        |> distinct (op aconv)
  in
    local_facts
      |> filter (fn (name, term) =>
          let val base = base_name name
          in
            if base = "that"
            then not (member (op aconv) other_than_that term)
            else if base = "assms"
            then not (member (op aconv) other_than_that_assms term)
            else true
          end)
  end

end




fun implode_with' _ []  R = R
  | implode_with' _ [x] R = x @ R
  | implode_with' s (h::L) R = h @ s :: implode_with' s L R

fun implode_with _ [] = []
  | implode_with _ [x] = x
  | implode_with s (h::L) = h @ s :: implode_with s L




end