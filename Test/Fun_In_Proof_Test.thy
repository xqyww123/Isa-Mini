theory Fun_In_Proof_Test
  imports Main Minilang.Minilang
begin

section \<open>Working method_setup tests (Variable.set_body false)\<close>

method_setup test_fun = \<open>
  Scan.succeed (fn ctxt =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      let
        val fixes = [(\<^binding>\<open>my_fact\<close>, SOME "nat \<Rightarrow> nat", NoSyn)]
        val specs : Specification.multi_specs_cmd =
          [(((Binding.empty, []), "my_fact 0 = 1"), [], []),
           (((Binding.empty, []), "my_fact (Suc n) = (Suc n) * my_fact n"),
            [], [(\<^binding>\<open>n\<close>, SOME "nat", NoSyn)])]
        val ctxt' = ctxt
          |> Variable.set_body false
          |> Function_Fun.add_fun_cmd fixes specs
               Function_Fun.fun_config false
        val _ = writeln "test_fun: defined my_fact"
      in
        Seq.single (Seq.Result (ctxt', st))
      end))
\<close>

lemma "True \<and> True"
  apply test_fun
  by simp


method_setup test_fun2 = \<open>
  Scan.succeed (fn ctxt =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      let
        val fixes = [(\<^binding>\<open>my_sum\<close>, SOME "nat \<Rightarrow> nat", NoSyn)]
        val specs : Specification.multi_specs_cmd =
          [(((Binding.empty, []), "my_sum 0 = 0"), [], []),
           (((Binding.empty, []), "my_sum (Suc n) = Suc n + my_sum n"),
            [], [(\<^binding>\<open>n\<close>, SOME "nat", NoSyn)])]
        val ctxt' = ctxt
          |> Variable.set_body false
          |> Function_Fun.add_fun_cmd fixes specs
               Function_Fun.fun_config false
          |> Variable.restore_body ctxt
        val _ = writeln "test_fun2: defined my_sum"
      in
        Seq.single (Seq.Result (ctxt', st))
      end))
\<close>

lemma "True \<and> True"
  apply test_fun2
  by simp

lemma \<open>\<exists>f:: nat \<Rightarrow> nat. f (Suc (Suc 0)) = 3\<close>
  subgoal
    apply test_fun2
    apply (rule exI[where x=\<open>my_sum\<close>])
    by simp


section \<open>Test: proof-local target (no theory fork)\<close>

ML \<open>
(* A proof-local foundation: instead of writing to the background theory,
   use Local_Defs to create local abbreviations *)
(* Proof-local foundation: return lhs ≡ rhs as an assumed theorem.
   Generic_Target.define will call Local_Defs.define afterwards
   to create the Free abbreviation. No theory modification. *)
fun proof_local_foundation (((b, U), mx), (b_def, rhs)) (type_params, term_params) lthy =
  let
    val params = type_params @ term_params
    val lhs = Term.list_comb (Free (Binding.name_of b, U), params)
    val eq = Logic.mk_equals (lhs, rhs)
    val global_def = Thm.assume (Thm.cterm_of lthy eq)
  in ((lhs, global_def), lthy) end

fun proof_local_notes kind facts lthy =
  Attrib.local_notes kind facts lthy

val proof_local_operations : Local_Theory.operations =
  {define = Generic_Target.define proof_local_foundation,
   notes = proof_local_notes,
   abbrev = Generic_Target.theory_abbrev,
   declaration = fn (_: {syntax: bool, pervasive: bool, pos: Position.T}) =>
                 fn (_: Morphism.declaration_entity) => I,
   theory_registration = fn (_: Locale.registration) => I,
   locale_dependency = fn (_: Locale.registration) => I,
   pretty = fn (_: Proof.context) => ([] : Pretty.T list)}
\<close>

ML \<open>
(* Create a proof-local target on the background theory,
   run an operation, then exit back *)
fun with_proof_local_target (f : local_theory -> Proof.context) (ctxt : Proof.context) =
  let
    val thy = Proof_Context.theory_of ctxt
    val lthy = Local_Theory.init
      {background_naming = Sign.naming_of thy,
       setup = Proof_Context.init_global,
       conclude = I}
      proof_local_operations thy
    val result_ctxt = f lthy
    val thy' = Proof_Context.theory_of result_ctxt
    val _ = writeln ("theory forked? " ^
      Bool.toString (not (Context.eq_thy (thy, thy'))))
  in result_ctxt end
\<close>

method_setup test_fun3 = \<open>
  Scan.succeed (fn ctxt =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      let
        val fixes = [(\<^binding>\<open>my_f3\<close>, SOME "nat \<Rightarrow> nat", NoSyn)]
        val specs : Specification.multi_specs_cmd =
          [(((Binding.empty, []), "my_f3 0 = 0"), [], []),
           (((Binding.empty, []), "my_f3 (Suc n) = Suc n + my_f3 n"),
            [], [(\<^binding>\<open>n\<close>, SOME "nat", NoSyn)])]

        val ctxt' = ctxt
          |> Variable.set_body false
          |> with_proof_local_target
               (Function_Fun.add_fun_cmd fixes specs
                  Function_Fun.fun_config false)

        val thy0 = Proof_Context.theory_of ctxt
        val thy1 = Proof_Context.theory_of ctxt'
        val _ = writeln ("same theory? " ^ Bool.toString (Context.eq_thy (thy0, thy1)))
        val _ = writeln "test_fun3: defined my_f3"
      in
        Seq.single (Seq.Result (ctxt', st))
      end))
\<close>

lemma "True \<and> True"
  apply test_fun3
  by simp

lemma \<open>\<exists>f:: nat \<Rightarrow> nat. f (Suc (Suc 0)) = 3\<close>
  subgoal
    apply test_fun3
    apply (rule exI[where x=\<open>my_f3\<close>])
    by simp


section \<open>Diagnostic: what does fun change?\<close>

ML \<open>val thy_before = \<^theory>\<close>

method_setup test_fun_diag = \<open>
  Scan.succeed (fn ctxt =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      let
        val thy0 = Proof_Context.theory_of ctxt
        val _ = writeln ("=== BEFORE fun ===")
        val _ = writeln ("theory: " ^ Context.theory_id_name {long = false} (Context.theory_id thy0))
        val consts0 = Sign.consts_of thy0 |> Consts.dest |> #constants |> length
        val _ = writeln ("num consts: " ^ string_of_int consts0)

        val fixes = [(\<^binding>\<open>diag_f\<close>, SOME "nat \<Rightarrow> nat", NoSyn)]
        val specs : Specification.multi_specs_cmd =
          [(((Binding.empty, []), "diag_f 0 = 0"), [], []),
           (((Binding.empty, []), "diag_f (Suc n) = Suc n + diag_f n"),
            [], [(\<^binding>\<open>n\<close>, SOME "nat", NoSyn)])]
        val ctxt' = ctxt
          |> Variable.set_body false
          |> Function_Fun.add_fun_cmd fixes specs
               Function_Fun.fun_config false
          |> Variable.restore_body ctxt

        val thy1 = Proof_Context.theory_of ctxt'
        val _ = writeln ("=== AFTER fun ===")
        val _ = writeln ("theory: " ^ Context.theory_id_name {long = false} (Context.theory_id thy1))
        val consts1_all = Sign.consts_of thy1 |> Consts.dest |> #constants
        val consts1 = length consts1_all
        val _ = writeln ("num consts: " ^ string_of_int consts1)
        val _ = writeln ("new consts: " ^ string_of_int (consts1 - consts0))
        val consts0_names = Sign.consts_of thy0 |> Consts.dest |> #constants
                            |> map fst |> Symtab.make_set
        val new_const_names = consts1_all
                            |> filter (fn (n, _) => not (Symtab.defined consts0_names n))
        val _ = new_const_names |> map (fn (n, (T, _)) =>
          writeln ("  + " ^ n ^ " :: " ^ Syntax.string_of_typ ctxt' T))

        (* Check: are these real Consts or Frees in the context? *)
        (* Check: are these real Consts or Frees in the context? *)
        val _ = writeln ("=== Checking representations ===")
        val _ = ["diag_f", "Fun_In_Proof_Test.diag_f",
                 "diag_f_graph", "Fun_In_Proof_Test.diag_f_graph",
                 "diag_f_sumC", "Fun_In_Proof_Test.diag_f_sumC",
                 "diag_f_dom", "Fun_In_Proof_Test.diag_f_dom",
                 "diag_f_rel", "Fun_In_Proof_Test.diag_f_rel"]
          |> map (fn name =>
            \<^try>\<open>
              let val t = Syntax.read_term ctxt' name
              in writeln (name ^ " => " ^
                (case t of
                  Const (n, _) => "Const " ^ quote n
                | Free (n, _) => "Free " ^ quote n
                | _ => Syntax.string_of_term ctxt' t))
              end
            catch exn => writeln (name ^ " => NOT FOUND")\<close>)
        val _ = writeln ("same theory? " ^
          Bool.toString (Context.eq_thy (thy0, thy1)))
        val _ = writeln ("thy0 subthy thy1? " ^
          Bool.toString (Context.proper_subthy (thy0, thy1)))

        (* Check: is the goal thm in the old or new theory? *)
        val _ = writeln ("goal thm theory: " ^
          Context.theory_id_name {long = false} (Thm.theory_id st))
        val _ = writeln ("goal in thy0? " ^
          Bool.toString (Context.subthy_id (Thm.theory_id st, Context.theory_id thy0)))
        val _ = writeln ("goal in thy1? " ^
          Bool.toString (Context.subthy_id (Thm.theory_id st, Context.theory_id thy1)))
      in
        Seq.single (Seq.Result (ctxt', st))
      end))
\<close>

lemma "True \<and> True"
  apply test_fun_diag
  by simp


section \<open>Recursive functions (fun path)\<close>

text \<open>Basic recursion\<close>
lemma "P \<Longrightarrow> \<exists>f :: nat \<Rightarrow> nat. f 3 = 6"
  by (min_script \<open>  
  INTRO
  FUN my_fact :: "nat \<Rightarrow> nat"
    where "my_fact 0 = 1"
        | "my_fact (Suc n) = (Suc n) * my_fact n"
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f 3 = 6"
  CHOOSE my_fact
  END
  END
\<close>)

text \<open>Fibonacci\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f 5 = 8"
  by (min _script \<open>
  FUN fib :: "nat \<Rightarrow> nat"
    where "fib 0 = 0"
        | "fib (Suc 0) = 1"
        | "fib (Suc (Suc n)) = fib n + fib (Suc n)"
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f 5 = 8"
  CRUSH
\<close>)

text \<open>Mutual-style single function with accumulator\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 4 0 = 10"
  by (min_script \<open>
  FUN sum_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where "sum_acc 0 a = a"
        | "sum_acc (Suc n) a = sum_acc n (a + Suc n)"
  HAVE "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 4 0 = 10"
  CRUSH
\<close>)


section \<open>Non-recursive with simple args (definition path)\<close>

text \<open>Simple arithmetic\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f 3 = 6"
  by (min_script \<open>
  FUN double :: "nat \<Rightarrow> nat"
    where "double n = n + n"
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f 3 = 6"
  CRUSH
\<close>)

text \<open>Multi-argument non-recursive\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 2 3 = 5"
  by (min_script \<open>
  FUN my_add :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where "my_add x y = x + y"
  HAVE "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 2 3 = 5"
  CRUSH
\<close>)

text \<open>Boolean function\<close>
lemma "\<exists>f :: nat \<Rightarrow> bool. f 0 = True"
  by (min_script \<open>
  FUN is_zero :: "nat \<Rightarrow> bool"
    where "is_zero n = (n = 0)"
  HAVE "\<exists>f :: nat \<Rightarrow> bool. f 0 = True"
  CRUSH
\<close>)


section \<open>Non-recursive with patterns (fun path, not definition)\<close>

text \<open>Pattern matching without recursion\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f 0 = 0 \<and> f 5 = 4"
  by (min_script \<open>
  FUN pred :: "nat \<Rightarrow> nat"
    where "pred 0 = 0"
        | "pred (Suc n) = n"
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f 0 = 0 \<and> f 5 = 4"
  CRUSH
\<close>)

text \<open>Boolean pattern matching\<close>
lemma "\<exists>f :: bool \<Rightarrow> nat. f True = 1 \<and> f False = 0"
  by (min_script \<open>
  FUN bool_to_nat :: "bool \<Rightarrow> nat"
    where "bool_to_nat True = 1"
        | "bool_to_nat False = 0"
  HAVE "\<exists>f :: bool \<Rightarrow> nat. f True = 1 \<and> f False = 0"
  CRUSH
\<close>)


section \<open>List functions\<close>

text \<open>Recursive list function\<close>
lemma "\<exists>f :: nat list \<Rightarrow> nat. f [1,2,3] = 6"
  by (min_script \<open>
  FUN my_sum :: "nat list \<Rightarrow> nat"
    where "my_sum [] = 0"
        | "my_sum (x # xs) = x + my_sum xs"
  HAVE "\<exists>f :: nat list \<Rightarrow> nat. f [1,2,3] = 6"
  CRUSH
\<close>)

text \<open>Non-recursive list pattern (fun path due to patterns)\<close>
lemma "\<exists>f :: nat list \<Rightarrow> nat. f [] = 0 \<and> f [5] = 5"
  by (min_script \<open>
  FUN my_head :: "nat list \<Rightarrow> nat"
    where "my_head [] = 0"
        | "my_head (x # xs) = x"
  HAVE "\<exists>f :: nat list \<Rightarrow> nat. f [] = 0 \<and> f [5] = 5"
  CRUSH
\<close>)


section \<open>Function used in subsequent proof steps\<close>

text \<open>Define function then use its simp rules\<close>
lemma "1 + 1 = (2 :: nat)"
  by (min_script \<open>
  FUN inc :: "nat \<Rightarrow> nat"
    where "inc n = Suc n"
  HAVE "inc 1 = 2"
  CRUSH
  HAVE "1 + 1 = (2 :: nat)"
  CRUSH
\<close>)

text \<open>Define recursive function and use induction\<close>
lemma "\<forall>n :: nat. 0 + n = n"
  by (min_script \<open>
  FUN my_plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where "my_plus 0 y = y"
        | "my_plus (Suc x) y = Suc (my_plus x y)"
  HAVE "\<forall>n :: nat. 0 + n = n"
  CRUSH
\<close>)


section \<open>Edge cases\<close>

text \<open>Constant function (no arguments besides the fixed one)\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat. f 42 = 0"
  by (min_script \<open>
  FUN always_zero :: "nat \<Rightarrow> nat"
    where "always_zero n = 0"
  HAVE "\<exists>f :: nat \<Rightarrow> nat. f 42 = 0"
  CRUSH
\<close>)

text \<open>Higher-order result\<close>
lemma "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 3 4 = 7"
  by (min_script \<open>
  FUN mk_adder :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    where "mk_adder x y = x + y"
  HAVE "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 3 4 = 7"
  CRUSH
\<close>)

end
