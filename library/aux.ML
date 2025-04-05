signature MINILANG_AUX = sig
include MINILANG_AUX

val variant_factname : Proof.context -> string -> string

val induction_tac:
    (string * string list) list Unsynchronized.ref ->
    bool ->
    (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> context_tactic

val xOF : Proof.context -> thm list -> thm -> thm
val xof : Proof.context -> string option list * string option list ->
    (binding * string option * mixfix) list -> thm -> thm

val xwhere : Proof.context ->
      ((indexname * Position.T) * string) list ->
        (binding * string option * mixfix) list ->
          thm -> thm

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

val simp_fact_name : Proof.context -> string -> string

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

fun variant_factname ctxt =
  let val facts = Proof_Context.facts_of ctxt
      fun bump name =
        if Facts.defined facts name
        then bump (Symbol.bump_string name)
        else name
   in bump
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

fun xOF ctxt thms st =
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
           | _ => raise THM ("OF : more facts are given than the number of premises of the rule",
                              LEN + 1, st :: thms)
   in if LEN <= Thm.nprems_of st
    then st OF thms
    else let
         val i = Thm.maxidx_of st + 1
         val st' = fconv_rule (rulify LEN ctxt) st
                |> Thm.forall_elim_vars i
      in (st' OF thms)
      |> fconv_rule (Object_Logic.atomize ctxt)
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

fun xwhere ctxt inst fixes thm =
  let val vs = Term.add_var_names (Thm.prop_of thm) []
   in if forall (fn ((name, _), _) => exists (fn name' => name' = name) vs) inst
    then Rule_Insts.where_rule ctxt inst fixes thm
    else let
      fun concl_conv C ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
              Conv.arg_conv (Conv.abs_conv (concl_conv C o snd) ctxt) ctm
           | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
              Conv.arg_conv (concl_conv C ctxt) ctm
           | _ => C ctxt ctm
      fun swap_all [] _ ctm = Conv.all_conv ctm
        | swap_all (NONE :: L) ctxt ctm =
            let fun swap [] ctm = Conv.all_conv ctm
                  | swap (NONE :: L) ctm = swap L ctm
                  | swap (SOME _ :: L) ctm =
                     (Conv.rewr_conv @{thm HOL.all_comm[folded atomize_eq]} then_conv
                      Conv.arg_conv (swap L)
                     ) ctm
             in (Conv.arg_conv (Conv.abs_conv (swap_all L o snd) ctxt) then_conv swap L) ctm
            end
        | swap_all (SOME _ :: L) ctxt ctm =
            Conv.arg_conv (Conv.abs_conv (swap_all L o snd) ctxt) ctm
      fun foralls (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = foralls X
        | foralls (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = foralls X
        | foralls (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, T, X)) = (name, T) :: foralls X
        | foralls (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = foralls X
        | foralls (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = foralls X
        | foralls _ = []
      val alls = foralls (Thm.concl_of thm)
              |> map (fn (name, T) =>
                  if exists (fn (((name', 0), _), _) => name' = name
                              | _ => false ) inst andalso
                     not (exists (fn (name', _) => name' = name) vs)
                  then SOME (Thm.var ((name, 0), Thm.ctyp_of ctxt T))
                  else NONE )
      val thm'= Conv.fconv_rule (concl_conv (fn ctxt =>
                  HOLogic.Trueprop_conv (swap_all alls ctxt)) ctxt) thm
             |> fold (fn SOME ctm => (fn thm =>
                  thm RS Drule.infer_instantiate ctxt [(("x", 0), ctm)] @{thm spec})
                       | NONE => I ) alls
   in Rule_Insts.where_rule ctxt inst fixes thm'
  end
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


end

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




fun implode_with' _ []  R = R
  | implode_with' _ [x] R = x @ R
  | implode_with' s (h::L) R = h @ s :: implode_with' s L R

fun implode_with _ [] = []
  | implode_with _ [x] = x
  | implode_with s (h::L) = h @ s :: implode_with s L



end