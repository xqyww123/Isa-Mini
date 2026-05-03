theory Test_LTE_InfraFilter
  imports
    "Lifting_the_Exponent.LTE"
    "Performant_Isabelle_ML.Performant_Isabelle_ML"
    (* Number theory / algebra *)
    "HOL-Number_Theory.Number_Theory"
    "HOL-Algebra.Ring"
    "HOL-Algebra.Group"
    "HOL-Algebra.IntRing"
    "HOL-Computational_Algebra.Factorial_Ring"
    (* Analysis *)
    "HOL-Analysis.Derivative"
    "HOL-Analysis.Measure_Space"
    "HOL-Analysis.Brouwer_Fixpoint"
    (* Core HOL *)
    "HOL.List"
    "HOL.Map"
    "HOL.Finite_Set"
    "HOL.Complete_Lattices"
    "HOL.Wellfounded"
    "HOL.Equiv_Relations"
    "HOL.Zorn"
    "HOL.Binomial"
    "HOL.GCD"
    "HOL.Topological_Spaces"
    "HOL.Real_Vector_Spaces"
    (* HOL-Library *)
    "HOL-Library.Multiset"
    "HOL-Library.FSet"
    "HOL-Library.Finite_Map"
    (* IMP language semantics *)
    "HOL-IMP.Small_Step"
    "HOL-IMP.Compiler"
    (* Data structures *)
    "HOL-Data_Structures.AVL_Set"
    "HOL-Data_Structures.RBT_Set"
    "HOL-Data_Structures.Tree_Map"
    (* AFP *)
    "Catalan_Numbers.Catalan_Numbers"
    "Bernoulli.Bernoulli"
    "Bell_Numbers_Spivey.Bell_Numbers"
    "Polynomial_Factorization.Gauss_Lemma"
    "Gauss_Jordan.Rank"
begin

ML_file \<open>../../Semantic_Embedding/Tools/infra_filter.ML\<close>

ML \<open>
let
  val out_path = Path.explode "~/.isabelle/Isabelle2024/log/infra_filter_pos_test.log"
  val lines : string list Synchronized.var = Synchronized.var "log_lines" []
  fun log s = Synchronized.change lines (fn ls => ls @ [s])
  fun flush () =
    File.write out_path (String.concatWith "\n" (Synchronized.value lines) ^ "\n")

  val context = Context.Proof \<^context>
  val {is_infra_const, ...} = Infra_Filter.gen_infra_filters context

  val test_consts = [
    (* Should NOT be filtered (lift_definition / user constants) *)
    ("Multiset.multiset.count", false),
    ("Finite_Map.fmap.fmlookup", false),
    ("Product_Type.prod.swap", false),
    (* Should be filtered (BNF infrastructure, not in preserved_set) *)
    ("List.list.size_list", true),
    ("List.list.size_list_inst.size_list", true),
    (* Should pass (preserved: constructors, case, map, etc.) *)
    ("List.list.Nil", false),
    ("List.list.Cons", false),
    ("List.list.case_list", false),
    ("List.map", false),
    ("List.set", false),
    (* Should be filtered (Abs_/Rep_ by name pattern) *)
    ("Product_Type.prod.Abs_prod", true),
    ("Product_Type.prod.Rep_prod", true),
    ("Multiset.multiset.Abs_multiset", true),
    ("Multiset.multiset.Rep_multiset", true),
    (* Should be filtered (quotient typedef infra) *)
    ("FSet.fset.Abs_fset", true),
    ("FSet.fset.Rep_fset", true),
    (* Should pass (BNF preserved: map/pred/rel/sets) *)
    ("Multiset.image_mset", false),
    ("Multiset.rel_mset", false),
    ("Multiset.pred_mset", false),
    ("FSet.fimage", false),
    ("FSet.fset_member", true) (* hidden name *)
  ]

  val _ = log "====== is_infra_const verification test ======"
  val all_pass = Synchronized.var "all_pass" true
  val _ = map (fn (name, expected) =>
    let val result = is_infra_const name
        val status = if result = expected then "PASS" else "FAIL"
        val _ = if result <> expected then Synchronized.change all_pass (K false) else ()
    in log (status ^ "  " ^ name ^
            "  is_infra=" ^ Bool.toString result ^
            "  expected=" ^ Bool.toString expected)
    end) test_consts

  val _ = log ""
  val _ = if Synchronized.value all_pass
          then log "ALL TESTS PASSED"
          else log "SOME TESTS FAILED"
  val _ = flush ()
in () end
\<close>

ML \<open>
let
  val out_path = Path.explode "~/.isabelle/Isabelle2024/log/infra_filter_broad_test.log"
  val lines : string list Synchronized.var = Synchronized.var "log_lines" []
  fun log s = Synchronized.change lines (fn ls => ls @ [s])
  fun flush () =
    File.write out_path (String.concatWith "\n" (Synchronized.value lines) ^ "\n")

  val context = Context.Proof \<^context>
  val thy = Proof_Context.theory_of \<^context>
  val {is_infra_const, is_infra_thm, is_infra_type, is_infra_class, is_infra_locale, ...} =
    Infra_Filter.gen_infra_filters context

  val consts = Sign.consts_of thy
  val all_const_names = #constants (Consts.dest consts) |> map fst
  val const_space = Consts.space_of consts

  val _ = log "====== Broad infra_filter test ======"
  val _ = log ""

  (* --- Constants --- *)
  val _ = log "=== CONSTANTS ==="
  val total_consts = length all_const_names
  val (infra_consts, pass_consts) = List.partition is_infra_const all_const_names
  val n_infra = length infra_consts
  val n_pass = length pass_consts
  val _ = log (String.concat ["Total: ", Int.toString total_consts,
    "  Infra: ", Int.toString n_infra,
    "  Pass: ", Int.toString n_pass,
    "  Ratio: ", Int.toString (100 * n_infra div total_consts), "%"])

  (* Break down infra consts by reason *)
  val _ = log ""
  val _ = log "--- Infra constant breakdown (first matching reason) ---"
  val fact_space = Facts.space_of (Global_Theory.facts_of thy)
  fun is_hidden space name =
    Long_Name.is_hidden (Name_Space.intern space name)
  val n_concealed = length (filter (fn n => Name_Space.is_concealed const_space n) all_const_names)
  val n_hidden = length (filter (fn n => is_hidden const_space n) all_const_names)
  val _ = log (String.concat ["  concealed: ", Int.toString n_concealed])
  val _ = log (String.concat ["  hidden: ", Int.toString n_hidden])

  (* Spot-check: lift_definition constants that should NOT be filtered *)
  val _ = log ""
  val _ = log "--- Spot-check: known lift_definition constants ---"
  val lift_consts = [
    "Multiset.multiset.count",
    "Finite_Map.fmap.fmlookup",
    "Finite_Map.fmap.fmran'",
    "Finite_Map.fmap.fmmap",
    "Finite_Map.fmap.fmrel",
    "Product_Type.prod.swap",
    "FSet.fset.fset"
  ]
  val _ = map (fn name =>
    let val result = is_infra_const name
        val status = if result then "FILTERED (unexpected?)" else "pass"
    in log (String.concat ["  ", status, "  ", name]) end) lift_consts

  (* Spot-check: BNF infra constants that SHOULD be filtered *)
  val _ = log ""
  val _ = log "--- Spot-check: known BNF infra constants ---"
  val bnf_infra_consts = [
    "List.list.size_list",
    "List.list.size_list_inst.size_list",
    "Sum_Type.sum.size_sum",
    "Product_Type.prod.size_prod",
    "Option.option.size_option"
  ]
  val _ = map (fn name =>
    let val result = is_infra_const name
        val status = if result then "filtered" else "PASS (unexpected?)"
    in log (String.concat ["  ", status, "  ", name]) end) bnf_infra_consts

  (* Spot-check: preserved BNF constants (names from BNF registration) *)
  val _ = log ""
  val _ = log "--- Spot-check: BNF-registered preserved constants ---"
  val preserved_consts = [
    (* List BNF *)
    "List.list.Nil", "List.list.Cons", "List.list.case_list",
    "List.list.map", "List.list.list_all", "List.list.list_all2", "List.list.set",
    (* Option BNF *)
    "Option.option.None", "Option.option.Some", "Option.option.case_option",
    "Option.map_option", "Option.pred_option", "Option.rel_option",
    (* Sum BNF *)
    "Sum_Type.Inl", "Sum_Type.Inr", "Sum_Type.sum.case_sum",
    "Sum_Type.map_sum",
    (* Prod BNF *)
    "Product_Type.Pair", "Product_Type.prod.case_prod",
    "Product_Type.map_prod",
    (* Multiset/FSet lifted *)
    "Multiset.image_mset", "Multiset.rel_mset", "Multiset.pred_mset",
    "FSet.fimage"
  ]
  val _ = map (fn name =>
    let val result = is_infra_const name
        val status = if result then "FILTERED (unexpected?)" else "pass"
    in log (String.concat ["  ", status, "  ", name]) end) preserved_consts

  (* Spot-check: Abs_/Rep_ constants that SHOULD be filtered *)
  val _ = log ""
  val _ = log "--- Spot-check: Abs_/Rep_ typedef morphisms ---"
  val absrep_consts = [
    "Product_Type.prod.Abs_prod", "Product_Type.prod.Rep_prod",
    "Multiset.multiset.Abs_multiset", "Multiset.multiset.Rep_multiset",
    "FSet.fset.Abs_fset", "FSet.fset.Rep_fset",
    "Sum_Type.sum.Abs_sum", "Sum_Type.sum.Rep_sum",
    "Option.option.Abs_option", "Option.option.Rep_option",
    "List.list.Abs_list", "List.list.Rep_list"
  ]
  val _ = map (fn name =>
    let val result = is_infra_const name
        val status = if result then "filtered" else "PASS (unexpected?)"
    in log (String.concat ["  ", status, "  ", name]) end) absrep_consts

  (* --- Sample: passed constants under ADT prefixes --- *)
  val _ = log ""
  val _ = log "--- Passed constants under common ADT type prefixes (sample) ---"
  val type_prefixes = ["List.list.", "Product_Type.prod.", "Sum_Type.sum.",
    "Option.option.", "Multiset.multiset.", "FSet.fset.", "Finite_Map.fmap.",
    "Set.set.", "Nat.nat.", "Int.int."]
  val _ = map (fn pfx =>
    let val under = filter (fn n => String.isPrefix pfx n) pass_consts
        val _ = log (String.concat ["  ", pfx, "* : ", Int.toString (length under), " passed"])
        val _ = map (fn n => log (String.concat ["    ", n])) (List.take (under, Int.min (10, length under)))
        val _ = if length under > 10 then log "    ..." else ()
    in () end) type_prefixes

  (* --- Theorems --- *)
  val _ = log ""
  val _ = log "=== THEOREMS ==="
  val all_facts = Facts.dest_static true [] (Proof_Context.facts_of \<^context>)
  val total_thms_count = Synchronized.var "total_thms" 0
  val infra_thms_count = Synchronized.var "infra_thms" 0
  val pass_thms_count = Synchronized.var "pass_thms" 0
  val _ = map (fn (name, thms) =>
    map (fn thm =>
      let val _ = Synchronized.change total_thms_count (fn n => n + 1)
      in if is_infra_thm (name, thm)
         then Synchronized.change infra_thms_count (fn n => n + 1)
         else Synchronized.change pass_thms_count (fn n => n + 1)
      end) thms) all_facts
  val total_t = Synchronized.value total_thms_count
  val infra_t = Synchronized.value infra_thms_count
  val pass_t = Synchronized.value pass_thms_count
  val _ = log (String.concat ["Total: ", Int.toString total_t,
    "  Infra: ", Int.toString infra_t,
    "  Pass: ", Int.toString pass_t,
    "  Ratio: ", Int.toString (if total_t > 0 then 100 * infra_t div total_t else 0), "%"])

  (* --- Types --- *)
  val _ = log ""
  val _ = log "=== TYPES ==="
  val type_space = Sign.type_space thy
  val all_type_names = Name_Space.get_names type_space
  val (infra_types, pass_types) = List.partition is_infra_type all_type_names
  val _ = log (String.concat ["Total: ", Int.toString (length all_type_names),
    "  Infra: ", Int.toString (length infra_types),
    "  Pass: ", Int.toString (length pass_types),
    "  Ratio: ", Int.toString (100 * length infra_types div length all_type_names), "%"])

  (* --- Classes --- *)
  val _ = log ""
  val _ = log "=== CLASSES ==="
  val class_space = Sign.class_space thy
  val all_class_names = Name_Space.get_names class_space
  val (infra_classes, pass_classes) = List.partition is_infra_class all_class_names
  val _ = log (String.concat ["Total: ", Int.toString (length all_class_names),
    "  Infra: ", Int.toString (length infra_classes),
    "  Pass: ", Int.toString (length pass_classes),
    "  Ratio: ", Int.toString (if length all_class_names > 0 then 100 * length infra_classes div length all_class_names else 0), "%"])

  (* --- Locales --- *)
  val _ = log ""
  val _ = log "=== LOCALES ==="
  val locale_space = Locale.locale_space thy
  val all_locale_names = Name_Space.get_names locale_space
  val (infra_locales, pass_locales) = List.partition is_infra_locale all_locale_names
  val _ = log (String.concat ["Total: ", Int.toString (length all_locale_names),
    "  Infra: ", Int.toString (length infra_locales),
    "  Pass: ", Int.toString (length pass_locales),
    "  Ratio: ", Int.toString (if length all_locale_names > 0 then 100 * length infra_locales div length all_locale_names else 0), "%"])

  (* --- Diagnostic: WHY are specific constants filtered? --- *)
  val _ = log ""
  val _ = log "=== DIAGNOSTIC: filter reasons for suspicious constants ==="

  val internal_prefixes = ["Lifting.", "BNF_Def.", "Transfer.", "BNF_Cardinal_Order_Relation.",
        "HOL.equal", "ATP.", "Code_Evaluation."]

  fun diagnose_const name =
    let
      fun check tests =
        case tests of
          [] => "UNKNOWN"
        | (label, test) :: rest => if test () then label else check rest
      val reason = check [
        ("concealed", fn () => Name_Space.is_concealed const_space name),
        ("hidden", fn () => is_hidden const_space name),
        ("internal_prefix", fn () => exists (fn pfx => String.isPrefix pfx name) internal_prefixes),
        ("has_class_variant", fn () =>
          let val all_cn = #constants (Consts.dest consts) |> map fst
              val has_cv = exists (fn cname =>
                if String.isSubstring "_class." cname then
                  let val qual = Long_Name.qualifier cname
                      val base = Long_Name.base_name cname
                  in if String.isSuffix "_class" qual then
                       String.concat [
                         String.substring (qual, 0, size qual - 6), ".", base] = name
                     else false
                  end
                else false) all_cn
          in has_cv end),
        ("quotient_typedef_infra", fn () => false),
        ("Abs_Rep_name", fn () =>
          let val base = Long_Name.base_name name
          in String.isPrefix "Abs_" base orelse String.isPrefix "Rep_" base end),
        ("adt_prefix+bnf_pos+not_preserved", fn () => false)
      ]
    in reason end

  (* Diagnostic: hidden constants from Consts.dest that are filtered *)
  val hidden_filtered = filter (fn n =>
    is_infra_const n andalso is_hidden const_space n
    andalso not (Name_Space.is_concealed const_space n)) all_const_names
  val _ = log (String.concat ["  Hidden (non-concealed) constants filtered: ",
    Int.toString (length hidden_filtered)])
  val _ = map (fn n => log (String.concat ["    ", n]))
    (List.take (hidden_filtered, Int.min (30, length hidden_filtered)))
  val _ = if length hidden_filtered > 30 then log "    ..." else ()

  val _ = log ""
  val _ = log "====== END ======"
  val _ = flush ()
in () end
\<close>

end
