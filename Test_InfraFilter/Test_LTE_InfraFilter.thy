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

end
