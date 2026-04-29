theory Test_SafeNames_Probe
  imports Minilang.Minilang
begin

ML \<open>
(* Simulate the insts structure for "induction n :: nat" inside a Have,
   and check what induct_safe_names extracts. *)
local
  val T = @{typ nat}
in
val _ =
  let
    val ctxt0 = @{context} |> Variable.set_body true
    val ([n_int], ctxt1) =
      Proof_Context.add_fixes [(Binding.name "n", SOME T, NoSyn)] ctxt0
    val ctxt1 = Variable.restore_body @{context} ctxt1

    (* The insts structure for "induction n": the target term Free *)
    val target_term = Free (n_int, T)
    val insts = [[SOME (NONE : Binding.binding option, (target_term, false))]]
      : (Binding.binding option * (term * bool)) option list list

    val safe_names =
      fold (fold (fn NONE => I
                   | SOME (_, (X, _)) =>
                       fold (insert (op =) o Name.clean o fst) (Term.add_frees X [])))
           insts []

    val _ = warning ("n_int = " ^ n_int)
    val _ = warning ("target_term = " ^ Syntax.string_of_term ctxt1 target_term)
    val _ = warning ("add_frees = " ^
                     String.concatWith ", " (map (fn (n,_) => n) (Term.add_frees target_term [])))
    val _ = warning ("safe_names = " ^ String.concatWith ", " safe_names)
  in () end
end
\<close>

end
