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
  val out_path = Path.explode "$ISABELLE_HOME_USER/log/infra_filter_pos_test.log"
  val lines : string list Synchronized.var = Synchronized.var "log_lines" []
  fun log s = Synchronized.change lines (fn ls => ls @ [s])
  fun flush () =
    File.write out_path (String.concatWith "\n" (Synchronized.value lines) ^ "\n")

  val context = Context.Proof \<^context>
  val {is_uninterpreted_const, ...} = Infra_Filter.gen_infra_filters context

  val test_consts = [
    (* Should NOT be filtered (lift_definition / user constants) *)
    (\<^const_name>\<open>Multiset.multiset.count\<close>, false),
    (\<^const_name>\<open>Finite_Map.fmap.fmlookup\<close>, false),
    (\<^const_name>\<open>Product_Type.prod.swap\<close>, false),
    (* The size family is KEPT since the 2026-08-25 rulings -- `size_list` is
       cited by ordinary induction proofs.  Its `instantiation` companion is
       still machinery and dies on the `inst_infix` rule. *)
    (\<^const_name>\<open>List.list.size_list\<close>, false),
    (\<^const_name>\<open>List.size_list_inst.size_list\<close>, true),
    (* Should pass (preserved: constructors, case, map, etc.) *)
    (\<^const_name>\<open>List.list.Nil\<close>, false),
    (\<^const_name>\<open>List.list.Cons\<close>, false),
    (\<^const_name>\<open>List.list.case_list\<close>, false),
    (\<^const_name>\<open>List.list.map\<close>, false),
    (\<^const_name>\<open>List.list.set\<close>, false),
    (* Typedef morphisms are KEPT since the 2026-08-25 deletion of the
       `abs_rep_name` rule: an Abs_/Rep_ name pattern is no longer a verdict on
       its own.  The Rep morphisms of multiset and fset are named `count` and
       `fset` (`morphisms count Abs_multiset`, `morphisms fset Abs_fset`). *)
    (\<^const_name>\<open>Product_Type.prod.Abs_prod\<close>, false),
    (\<^const_name>\<open>Product_Type.prod.Rep_prod\<close>, false),
    (\<^const_name>\<open>Multiset.multiset.Abs_multiset\<close>, false),
    (\<^const_name>\<open>Multiset.multiset.count\<close>, false),
    (\<^const_name>\<open>FSet.fset.Abs_fset\<close>, false),
    (\<^const_name>\<open>FSet.fset.fset\<close>, false),
    (* Should pass (BNF preserved: map/pred/rel/sets) *)
    (\<^const_name>\<open>Multiset.image_mset\<close>, false),
    (\<^const_name>\<open>Multiset.rel_mset\<close>, false),
    (\<^const_name>\<open>Multiset.pred_mset\<close>, false),
    (\<^const_name>\<open>FSet.fimage\<close>, false),
    (* hidden: Product_Type.thy `hide_const internal_case_prod`; \<^const_name> cannot read a
       hidden name *)
    (\<^unchecked_name>\<open>Product_Type.internal_case_prod\<close>, true)
  ]

  val _ = log "====== is_uninterpreted_const verification test ======"
  val all_pass = Synchronized.var "all_pass" true
  (*a name that is no constant fails: an unknown name would pass on the `hidden` rule*)
  val consts = Proof_Context.consts_of \<^context>
  val _ = map (fn (name, expected) =>
    let val declared = can (Consts.the_constraint consts) name
        val result = is_uninterpreted_const name
        val ok = declared andalso result = expected
        val status = if ok then "PASS" else "FAIL"
        val _ = if ok then () else Synchronized.change all_pass (K false)
    in log (status ^ "  " ^ name ^ (if declared then "" else "  (no such constant)") ^
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
  val out_path = Path.explode "$ISABELLE_HOME_USER/log/infra_filter_broad_test.log"
  val lines : string list Synchronized.var = Synchronized.var "log_lines" []
  fun log s = Synchronized.change lines (fn ls => ls @ [s])
  fun flush () =
    File.write out_path (String.concatWith "\n" (Synchronized.value lines) ^ "\n")

  val context = Context.Proof \<^context>
  val thy = Proof_Context.theory_of \<^context>
  val {is_uninterpreted_const, is_infra_thm, is_infra_type, is_infra_class, is_infra_locale, ...} =
    Infra_Filter.gen_infra_filters context

  val consts = Sign.consts_of thy
  val all_const_names = #constants (Consts.dest consts) |> map fst
  val const_space = Consts.space_of consts

  val _ = log "====== Broad infra_filter test ======"
  val _ = log ""

  (* --- Constants --- *)
  val _ = log "=== CONSTANTS ==="
  val total_consts = length all_const_names
  val (infra_consts, pass_consts) = List.partition is_uninterpreted_const all_const_names
  val n_infra = length infra_consts
  val n_pass = length pass_consts
  val _ = log (String.concat ["Total: ", Int.toString total_consts,
    "  Infra: ", Int.toString n_infra,
    "  Pass: ", Int.toString n_pass,
    "  Ratio: ", Int.toString (100 * n_infra div total_consts), "%"])

  (* Break down infra consts by reason *)
  val _ = log ""
  val _ = log "--- Infra constant breakdown (first matching reason) ---"
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
    \<^const_name>\<open>Multiset.multiset.count\<close>,
    \<^const_name>\<open>Finite_Map.fmap.fmlookup\<close>,
    \<^const_name>\<open>Finite_Map.fmap.fmran'\<close>,
    \<^const_name>\<open>Finite_Map.fmap.fmmap\<close>,
    \<^const_name>\<open>Finite_Map.fmap.fmrel\<close>,
    \<^const_name>\<open>Product_Type.prod.swap\<close>,
    \<^const_name>\<open>FSet.fset.fset\<close>
  ]
  val _ = map (fn name =>
    let val result = is_uninterpreted_const name
        val status = if result then "FILTERED (unexpected?)" else "pass"
    in log (String.concat ["  ", status, "  ", name]) end) lift_consts

  (* Spot-check: the size plugin's constants.  The size functions themselves are
     KEPT since the 2026-08-25 rulings; only their `instantiation` companions are
     machinery.  The sum/prod size functions are declared in `HOL.Basic_BNF_LFPs`,
     NOT under a `Sum_Type.sum.` / `Product_Type.prod.` qualifier -- querying the
     latter spellings asks about names that do not exist in this distribution,
     and a verdict on a non-existent name is meaningless. *)
  val _ = log ""
  val _ = log "--- Spot-check: size-plugin constants ---"
  val size_consts = [
    (\<^const_name>\<open>List.list.size_list\<close>, false),
    (\<^const_name>\<open>Basic_BNF_LFPs.sum.size_sum\<close>, false),
    (\<^const_name>\<open>Basic_BNF_LFPs.prod.size_prod\<close>, false),
    (\<^const_name>\<open>Option.option.size_option\<close>, false),
    (\<^const_name>\<open>List.size_list_inst.size_list\<close>, true),
    (\<^const_name>\<open>Basic_BNF_LFPs.size_sum_inst.size_sum\<close>, true),
    (\<^const_name>\<open>Basic_BNF_LFPs.size_prod_inst.size_prod\<close>, true)
  ]
  val _ = map (fn (name, expected) =>
    let val result = is_uninterpreted_const name
        val status = if result = expected then (if result then "filtered" else "pass")
                     else "UNEXPECTED"
    in log (String.concat ["  ", status, "  ", name]) end) size_consts

  (* Spot-check: preserved BNF constants (names from BNF registration) *)
  val _ = log ""
  val _ = log "--- Spot-check: BNF-registered preserved constants ---"
  val preserved_consts = [
    (* List BNF *)
    \<^const_name>\<open>List.list.Nil\<close>, \<^const_name>\<open>List.list.Cons\<close>, \<^const_name>\<open>List.list.case_list\<close>,
    \<^const_name>\<open>List.list.map\<close>, \<^const_name>\<open>List.list.list_all\<close>, \<^const_name>\<open>List.list.list_all2\<close>, \<^const_name>\<open>List.list.set\<close>,
    (* Option BNF *)
    \<^const_name>\<open>Option.option.None\<close>, \<^const_name>\<open>Option.option.Some\<close>, \<^const_name>\<open>Option.option.case_option\<close>,
    \<^const_name>\<open>Option.option.map_option\<close>, \<^const_name>\<open>Option.option.pred_option\<close>, \<^const_name>\<open>Option.option.rel_option\<close>,
    (* Sum BNF *)
    \<^const_name>\<open>Sum_Type.Inl\<close>, \<^const_name>\<open>Sum_Type.Inr\<close>, \<^const_name>\<open>Sum_Type.sum.case_sum\<close>,
    \<^const_name>\<open>Sum_Type.map_sum\<close>,
    (* Prod BNF *)
    \<^const_name>\<open>Product_Type.Pair\<close>, \<^const_name>\<open>Product_Type.prod.case_prod\<close>,
    \<^const_name>\<open>Product_Type.map_prod\<close>,
    (* Multiset/FSet lifted *)
    \<^const_name>\<open>Multiset.image_mset\<close>, \<^const_name>\<open>Multiset.rel_mset\<close>, \<^const_name>\<open>Multiset.pred_mset\<close>,
    \<^const_name>\<open>FSet.fimage\<close>
  ]
  val _ = map (fn name =>
    let val result = is_uninterpreted_const name
        val status = if result then "FILTERED (unexpected?)" else "pass"
    in log (String.concat ["  ", status, "  ", name]) end) preserved_consts

  (* Spot-check: Abs_/Rep_ typedef morphisms.  Since the `abs_rep_name` rule was
     deleted (2026-08-25) these are KEPT unless another rule reaches them -- the
     ones the datatype package conceals (Option/List) on `concealed`.  The Rep
     morphisms of multiset and fset are `count` and `fset`. *)
  val _ = log ""
  val _ = log "--- Spot-check: Abs_/Rep_ typedef morphisms ---"
  val absrep_consts = [
    (\<^const_name>\<open>Product_Type.prod.Abs_prod\<close>, false), (\<^const_name>\<open>Product_Type.prod.Rep_prod\<close>, false),
    (\<^const_name>\<open>Multiset.multiset.Abs_multiset\<close>, false), (\<^const_name>\<open>Multiset.multiset.count\<close>, false),
    (\<^const_name>\<open>FSet.fset.Abs_fset\<close>, false), (\<^const_name>\<open>FSet.fset.fset\<close>, false),
    (\<^const_name>\<open>Sum_Type.sum.Abs_sum\<close>, false), (\<^const_name>\<open>Sum_Type.sum.Rep_sum\<close>, false),
    (\<^const_name>\<open>Option.option.Abs_option\<close>, true), (\<^const_name>\<open>Option.option.Rep_option\<close>, true),
    (\<^const_name>\<open>List.list.Abs_list\<close>, true), (\<^const_name>\<open>List.list.Rep_list\<close>, true)
  ]
  val _ = map (fn (name, expected) =>
    let val result = is_uninterpreted_const name
        val status = if result = expected then (if result then "filtered" else "pass")
                     else "UNEXPECTED"
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

  (* --- Diagnostic: which constants die on the `hidden` rule --- *)
  val _ = log ""
  val _ = log "=== DIAGNOSTIC: hidden (non-concealed) constants rejected ==="

  val hidden_filtered = filter (fn n =>
    is_uninterpreted_const n andalso is_hidden const_space n
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
