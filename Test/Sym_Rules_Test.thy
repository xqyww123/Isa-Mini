theory Sym_Rules_Test
  imports Complex_Main
begin

ML \<open>
let
  val ctxt = \<^context>
  val sym_rules = [@{thm sym}, @{thm not_sym}, @{thm converseI}, @{thm converseD},
                   @{thm equivclp_sym}, @{thm rtranclp_symclp_sym}, Drule.symmetric_thm]

  val _ = writeln "=== All sym rules ==="
  val _ = sym_rules |> List.app (fn th =>
    let val nprems = Thm.nprems_of th
        val tag = if nprems = 1 then "" else " *** NOT 1 PREM ***"
    in writeln (Thm.get_name_hint th ^ " [" ^ string_of_int nprems ^ " prems]" ^ tag) end)

  (* Build the template:  (?A ==> ?B) ==> (?B ==> ?A) ==> (?A == ?B)
     using kernel primitives *)
  val (cA, cB) =
    let val ([cA, cB], _) = Variable.import_terms true
            [Free ("A", propT), Free ("B", propT)] ctxt
    in (Thm.cterm_of ctxt cA, Thm.cterm_of ctxt cB) end
  val AB = Thm.assume (Drule.mk_implies (cA, cB))   (* A ==> B *)
  val BA = Thm.assume (Drule.mk_implies (cB, cA))   (* B ==> A *)
  val eq = Thm.equal_intr AB BA                    (* A == B *)
  val template = eq
    |> Thm.implies_intr (Drule.mk_implies (cB, cA))   (* (B==>A) ==> A==B *)
    |> Thm.implies_intr (Drule.mk_implies (cA, cB))   (* (A==>B) ==> (B==>A) ==> A==B *)
  val _ = writeln ("\ntemplate: " ^ Syntax.string_of_term ctxt (Thm.prop_of template))

  (* Step 1: For each r1, bicompose with template's first premise *)
  val _ = writeln "\n=== Pairing sym rules ==="
  val _ = sym_rules |> List.app (fn r1 =>
    let
      val name1 = Thm.get_name_hint r1
      val nprems1 = Thm.nprems_of r1
    in
      if nprems1 <> 1 then writeln (name1 ^ ": skip (" ^ string_of_int nprems1 ^ " prems)")
      else
      let
        (* bicompose r1 (which is A==>B, 1 prem) with template's first premise *)
        val step1_results = Seq.list_of (
          Thm.bicompose (SOME ctxt)
            {flatten = false, match = false, incremented = false}
            (false, r1, 1) 1 template)
        val _ = if null step1_results then writeln (name1 ^ ": bicompose step1 FAILED") else ()
      in
        step1_results |> List.app (fn after_r1 =>
          (* after_r1 should be:  ?prem_of_r1 ==> (?B ==> ?A) ==> ?A == ?B
             with ?A, ?B partially instantiated *)
          let
            val _ = writeln ("\n" ^ name1 ^ " step1: " ^
              Syntax.string_of_term ctxt (Thm.prop_of after_r1) ^
              " [" ^ string_of_int (Thm.nprems_of after_r1) ^ " prems]")
          in
            (* Step 2: try each r2 against the remaining (B ==> A) premise *)
            (* The (B ==> A) premise is at position 1 now (after the r1's own prem) *)
            sym_rules |> List.app (fn r2 =>
              let
                val name2 = Thm.get_name_hint r2
                val nprems2 = Thm.nprems_of r2
              in
                if nprems2 <> 1 then () else
                let
                  val step2_results = Seq.list_of (Seq.take 2 (
                    Thm.bicompose (SOME ctxt)
                      {flatten = false, match = false, incremented = false}
                      (false, r2, 1) 1 after_r1))
                in
                  case step2_results of
                    [] => ()
                  | [result] =>
                      let val result_str = Syntax.string_of_term ctxt (Thm.prop_of result)
                      in writeln ("  + " ^ name2 ^ " => " ^ result_str ^
                           " [" ^ string_of_int (Thm.nprems_of result) ^ " prems]")
                      end
                  | results =>
                      writeln ("  ? " ^ name2 ^ " => " ^
                        string_of_int (length results) ^ " results (ambiguous)")
                end
              end)
          end)
      end
    end)
in () end
\<close>

end
