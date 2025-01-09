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

val print_toks : Token.src -> string list
val trim_markup : string -> string
val method_sorry : Method.text

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

end