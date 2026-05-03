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

  val const_space = Consts.space_of (Proof_Context.consts_of \<^context>)
  val type_space = Proof_Context.type_space \<^context>

  fun pos_str pos =
    let val file = case Position.file_of pos of SOME f => f | NONE => "?"
        val line = case Position.line_of pos of SOME l => Int.toString l | NONE => "?"
    in file ^ ":" ^ line end

  fun get_const_pos name =
    \<^try>\<open>#pos (Name_Space.the_entry const_space name)
      catch _ => Position.none\<close>
  fun get_type_pos name =
    \<^try>\<open>#pos (Name_Space.the_entry type_space name)
      catch _ => Position.none\<close>

  fun same_line p1 p2 =
    Position.file_of p1 = Position.file_of p2
    andalso Position.line_of p1 = Position.line_of p2
    andalso Position.file_of p1 <> NONE

  val all_const_names = #constants (Consts.dest (Proof_Context.consts_of \<^context>)) |> map fst

  val test_types = [
    "List.list", "Multiset.multiset", "Finite_Map.fmap", "Product_Type.prod",
    "Set.set", "Option.option", "Sum_Type.sum", "FSet.fset",
    "Tree.tree", "RBT.rbt"
  ]

  val _ = log "====== Position Diagnostic: type pos vs const pos ======"
  val _ = map (fn T =>
    let
      val t_pos = get_type_pos T
      val prefix = T ^ "."
      val consts_under = filter (fn c => String.isPrefix prefix c) all_const_names
      val _ = log ""
      val _ = log ("====== " ^ T ^ " ======")
      val _ = log ("  type position: " ^ pos_str t_pos)
      val _ = log ("  constants under prefix (" ^ Int.toString (length consts_under) ^ "):")
      val _ = map (fn c =>
        let val c_pos = get_const_pos c
            val concealed = Name_Space.is_concealed const_space c
            val match = same_line t_pos c_pos
        in log ("    " ^ (if match then "SAME" else "DIFF") ^
                (if concealed then " [concealed]" else "") ^
                "  " ^ c ^ "  @ " ^ pos_str c_pos)
        end) consts_under
    in () end) test_types
  val _ = flush ()
in () end
\<close>

end
