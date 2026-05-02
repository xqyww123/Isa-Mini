theory Test_LTE_InfraFilter
  imports
    "Lifting_the_Exponent.LTE"
    "Performant_Isabelle_ML.Performant_Isabelle_ML"
    "HOL-Number_Theory.Number_Theory"
    "HOL-Algebra.Ring"
    "Catalan_Numbers.Catalan_Numbers"
    "Bernoulli.Bernoulli"
    "Bell_Numbers_Spivey.Bell_Numbers"
    "Polynomial_Factorization.Gauss_Lemma"
    "Gauss_Jordan.Rank"
    "HOL-Analysis.Derivative"
begin

ML_file \<open>../../Semantic_Embedding/Tools/infra_filter.ML\<close>

ML \<open>
let
  val out_path = Path.explode "~/.isabelle/Isabelle2024/log/infra_filter_broad_test.log"
  val lines : string list Synchronized.var = Synchronized.var "log_lines" []
  fun log s = Synchronized.change lines (fn ls => ls @ [s])
  fun flush () =
    File.write out_path (String.concatWith "\n" (Synchronized.value lines) ^ "\n")

  val context = Context.Proof \<^context>
  val {is_infra_thm, is_infra_const, ...} = Infra_Filter.gen_infra_filters context

  val fact_space = Facts.space_of (Proof_Context.facts_of \<^context>)
  val consts = Proof_Context.consts_of \<^context>

  val infra_theory_prefixes = ["Code_Evaluation.", "Num."]
  fun check_infra_theory name =
    exists (fn pfx => String.isPrefix pfx name) infra_theory_prefixes

  val type_space = Proof_Context.type_space \<^context>
  val type_names = Name_Space.get_names type_space
    |> filter (fn name =>
        name <> "fun"
        andalso not (Name_Space.is_concealed type_space name)
        andalso not (Long_Name.is_hidden (Name_Space.intern type_space name)))
  val type_name_prefixes = map (fn T => T ^ ".") type_names

  fun check_ADT name =
    String.isSuffix "_def" name
    andalso exists (fn pfx => String.isPrefix pfx name) type_name_prefixes

  val ctxt = \<^context>
  val is_inductive = can (Inductive.the_inductive_global ctxt)
  fun check_inductive_infra name =
    let val base = Long_Name.base_name name
    in if String.isSuffix "_def" base
       then is_inductive (String.substring (name, 0, size name - 4))
            orelse is_inductive (String.substring (name, 0, size name - 4) ^ "p")
       else if base = "cong"
       then is_inductive (Long_Name.qualifier name)
       else false
    end

  fun check_internal_constants thm =
    let val found : string list Synchronized.var = Synchronized.var "found" []
        val _ = Term.exists_Const (fn (name, _) =>
          let val result = is_infra_const name
              val _ = if result then Synchronized.change found (fn fs => fs @ [name]) else ()
          in result end) (Thm.prop_of thm)
    in Synchronized.value found end

  fun check_internal_class thm =
    let fun is_ic (Const(name1, _) $ Const(\<^const_name>\<open>Pure.type\<close>, _)) =
              String.isSuffix "_class" name1
          | is_ic (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ A $ B) = is_ic A orelse is_ic B
          | is_ic (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = is_ic X
          | is_ic (Const(\<^const_name>\<open>Pure.conjunction\<close>, _) $ A $ B) = is_ic A orelse is_ic B
          | is_ic _ = false
    in is_ic (Thm.prop_of thm) end

  fun clean s = YXML.content_of s

  val all_ancestors = Theory.nodes_of \<^theory>
  fun find_thy name = List.find (fn t =>
    let val ln = Context.theory_long_name t
    in ln = name orelse Long_Name.base_name ln = name end) all_ancestors

  fun diagnose_theory' thy_name =
    case find_thy thy_name of
      NONE => (log ("====== " ^ thy_name ^ " ======");
               log "  [SKIP] theory not found in ancestor graph"; ())
    | SOME thy =>
      let
        val _ = log ("====== " ^ thy_name ^ " ======")
        val thy_context = Context.Theory thy
        val thy_global_facts = Global_Theory.facts_of thy
        val thy_parent_facts = map Global_Theory.facts_of (Theory.parents_of thy)
        val thy_new_facts = Facts.dest_static false thy_parent_facts thy_global_facts

        val thy_filters = Infra_Filter.gen_infra_filters thy_context
        val thy_is_infra = #is_infra_thm thy_filters
        val thy_fact_space = Facts.space_of thy_global_facts

        val (infra_facts, non_infra_facts) = List.partition
          (fn (name, thms) => List.all (fn thm => thy_is_infra (name, thm)) thms)
          thy_new_facts

        val _ = log ("  total new facts: " ^ Int.toString (length thy_new_facts))
        val _ = log ("  infra-filtered: " ^ Int.toString (length infra_facts))
        val _ = log ("  surviving: " ^ Int.toString (length non_infra_facts))

        val _ = if null infra_facts then ()
          else (
            log "  --- filtered facts with reasons ---";
            map (fn (name, thms) =>
              let val thm = hd thms
                  val concealed = Name_Space.is_concealed thy_fact_space name
                  val hidden = (Long_Name.is_hidden (Name_Space.intern thy_fact_space name)
                                handle ERROR _ => false)
                  val infra_thy = check_infra_theory name
                  val adt = check_ADT name
                  val inductive = check_inductive_infra name
                  val ic_names = check_internal_constants thm
                  val int_class = check_internal_class thm
                  val sz = Infra_Filter.smart_size_of_term (Thm.prop_of thm)
                  val reasons = String.concatWith ", " (map_filter I [
                    if concealed then SOME "concealed" else NONE,
                    if hidden then SOME "hidden" else NONE,
                    if infra_thy then SOME "infra_theory" else NONE,
                    if adt then SOME "ADT" else NONE,
                    if inductive then SOME "inductive" else NONE,
                    if not (null ic_names) then
                      SOME ("internal_const[" ^ String.concatWith "," ic_names ^ "]")
                    else NONE,
                    if int_class then SOME "internal_class" else NONE,
                    if sz > 1000 then SOME ("size=" ^ Int.toString sz) else NONE])
                  val prop_short =
                    let val s = clean (Syntax.string_of_term ctxt (Thm.prop_of thm))
                    in if size s > 150 then String.substring (s, 0, 150) ^ "..." else s end
              in log ("    " ^ name ^ "  [" ^ reasons ^ "]  size=" ^ Int.toString sz);
                 log ("      " ^ prop_short)
              end) infra_facts;
            ())
      in () end

  val test_theories = [
    "LTE",
    "Cong",
    "Residues",
    "Totient",
    "Fib",
    "Euler_Criterion",
    "Catalan_Numbers",
    "Bernoulli",
    "Bell_Numbers",
    "Gauss_Lemma",
    "Rank",
    "Derivative",
    "Ring"
  ]

  val _ = log "====== Broad InfraFilter Diagnostic ======"
  val _ = log ("Testing " ^ Int.toString (length test_theories) ^ " theories")
  val _ = log ""
  val _ = map diagnose_theory' test_theories
  val _ = flush ()
in () end
\<close>

end
