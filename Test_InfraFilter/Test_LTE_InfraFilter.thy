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
  val const_space = Consts.space_of (Proof_Context.consts_of \<^context>)
  val type_space = Proof_Context.type_space \<^context>

  fun pos_str pos =
    let val file = case Position.file_of pos of SOME f => f | NONE => "?"
        val line = case Position.line_of pos of SOME l => Int.toString l | NONE => "?"
        val off = case Position.offset_of pos of SOME o_ => Int.toString o_ | NONE => "?"
        val eoff = case Position.end_offset_of pos of SOME o_ => Int.toString o_ | NONE => "?"
    in file ^ ":" ^ line ^ " off=" ^ off ^ " eoff=" ^ eoff end

  fun get_const_pos name =
    \<^try>\<open>#pos (Name_Space.the_entry const_space name)
      catch _ => Position.none\<close>
  fun get_type_pos name =
    \<^try>\<open>#pos (Name_Space.the_entry type_space name)
      catch _ => Position.none\<close>
  fun get_const_group name =
    \<^try>\<open>#group (Name_Space.the_entry const_space name)
      catch _ => 0\<close>

  fun same_line p1 p2 =
    Position.file_of p1 = Position.file_of p2
    andalso Position.line_of p1 = Position.line_of p2
    andalso Position.file_of p1 <> NONE

  fun try_const_name t =
    case try (fst o Term.dest_Const) t of
      SOME name => SOME (name, get_const_pos name)
    | NONE => NONE

  fun bnf_const_positions T =
    let
      val bnf_pos = case Context.cases BNF_Def.bnf_of_global BNF_Def.bnf_of context T of
          NONE => []
        | SOME bnf =>
            map_filter try_const_name
              ([BNF_Def.map_of_bnf bnf, BNF_Def.pred_of_bnf bnf, BNF_Def.rel_of_bnf bnf]
               @ BNF_Def.sets_of_bnf bnf)
      val ctr_pos = case Context.cases Ctr_Sugar.ctr_sugar_of_global Ctr_Sugar.ctr_sugar_of context T of
          NONE => []
        | SOME cs =>
            map_filter try_const_name
              (#ctrs cs @ List.concat (#selss cs) @ [#casex cs] @ #discs cs)
      val fp_pos = case Context.cases BNF_FP_Def_Sugar.fp_sugar_of_global BNF_FP_Def_Sugar.fp_sugar_of context T of
          NONE => []
        | SOME fp =>
            let val res = #fp_res fp
                val co_rec_pos = case #fp_co_induct_sugar fp of
                    NONE => []
                  | SOME sugar => map_filter try_const_name [#co_rec sugar]
            in
              map_filter try_const_name
                (#ctors res @ #dtors res @ #xtor_un_folds res @ #xtor_co_recs res)
              @ co_rec_pos
            end
      val pre_bnf_pos = case Context.cases BNF_FP_Def_Sugar.fp_sugar_of_global BNF_FP_Def_Sugar.fp_sugar_of context T of
          NONE => []
        | SOME fp =>
            let val pre = #pre_bnf fp
            in map_filter try_const_name
                ([BNF_Def.map_of_bnf pre] @ BNF_Def.sets_of_bnf pre)
            end
    in bnf_pos @ ctr_pos @ fp_pos @ pre_bnf_pos end

  val all_const_names = #constants (Consts.dest (Proof_Context.consts_of \<^context>)) |> map fst

  val thy = Context.theory_of context
  fun has_typedef T = not (null (Typedef.get_info_global thy T))
  fun has_record T = is_some (Record.get_info thy T)
  fun has_quotient T = is_some (Quotient_Info.lookup_quotients_global thy T)

  val test_types = [
    "List.list", "Multiset.multiset", "Finite_Map.fmap", "Product_Type.prod",
    "Option.option", "Sum_Type.sum", "FSet.fset", "Tree.tree",
    (* Records *)
    "Congruence.partial_object_ext", "Group.monoid_ext", "Ring.ring_ext",
    (* Types with typedef but maybe no quotient *)
    "Nat.nat", "Int.int"
  ]

  val _ = log "====== Position Diagnostic v2: BNF const positions ======"
  val _ = map (fn T =>
    let
      val t_pos = get_type_pos T
      val prefix = T ^ "."
      val consts_under = filter (fn c => String.isPrefix prefix c) all_const_names

      val bnf_positions = bnf_const_positions T
      val bnf_lines = map_filter (fn (_, p) =>
        case (Position.file_of p, Position.line_of p) of
          (SOME f, SOME l) => SOME (f, l)
        | _ => NONE) bnf_positions
        |> distinct (op =)

      val has_bnf = is_some (Context.cases BNF_Def.bnf_of_global BNF_Def.bnf_of context T)
      val has_ctr = is_some (Context.cases Ctr_Sugar.ctr_sugar_of_global Ctr_Sugar.ctr_sugar_of context T)
      val has_fp = is_some (Context.cases BNF_FP_Def_Sugar.fp_sugar_of_global BNF_FP_Def_Sugar.fp_sugar_of context T)

      val _ = log ""
      val _ = log ("====== " ^ T ^ " ======")
      val _ = log ("  type position: " ^ pos_str t_pos)
      val _ = log ("  flags: " ^ String.concatWith " " (map_filter I [
        if has_bnf then SOME "BNF" else NONE,
        if has_ctr then SOME "ctr_sugar" else NONE,
        if has_fp then SOME "fp_sugar" else NONE,
        if has_typedef T then SOME "typedef" else NONE,
        if has_record T then SOME "record" else NONE,
        if has_quotient T then SOME "quotient" else NONE]))

      val _ = log ("  BNF/ctr_sugar/fp_sugar constant positions:")
      val _ = map (fn (name, pos) =>
        log ("    " ^ name ^ "  @ " ^ pos_str pos ^ "  group=" ^ Int.toString (get_const_group name))
      ) bnf_positions

      val _ = log ("  BNF origin lines: " ^ String.concatWith ", "
        (map (fn (f, l) => f ^ ":" ^ Int.toString l) bnf_lines))

      fun is_bnf_origin_line pos =
        case (Position.file_of pos, Position.line_of pos) of
          (SOME f, SOME l) => exists (fn (f', l') => f = f' andalso l = l') bnf_lines
        | _ => false

      val _ = log ("  constants under prefix (" ^ Int.toString (length consts_under) ^ "):")
      val _ = map (fn c =>
        let val c_pos = get_const_pos c
            val concealed = Name_Space.is_concealed const_space c
            val on_bnf_line = is_bnf_origin_line c_pos
            val grp = get_const_group c
        in log ("    " ^ (if on_bnf_line then "BNF_LINE" else "OTHER  ") ^
                (if concealed then " [concealed]" else "          ") ^
                "  " ^ c ^ "  @ " ^ pos_str c_pos ^
                "  group=" ^ Int.toString grp)
        end) consts_under
    in () end) test_types
  val _ = flush ()
in () end
\<close>

end
