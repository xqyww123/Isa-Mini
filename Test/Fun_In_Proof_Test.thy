theory Fun_In_Proof_Test
  imports Main Minilang.Minilang
begin

section \<open>Test 1: add_fun_cmd with Variable.set_body false\<close>

text \<open>
  The root cause: inside a proof, Variable.is_body is true, so
  add_fixes_binding skolemizes variable names (adding __ suffix).
  Fix: temporarily set body to false before calling add_fun_cmd.
\<close>

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


section \<open>Test 2: Visibility inside and after proof\<close>

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
  apply test_fun2
  apply (rule exI[where x=\<open>my_sum\<close>])
  by simp

ML \<open>Variable.restore_body\<close>

proof -
  ML_prf \<open>
    val is_known =
      (Syntax.read_term \<^context> "my_sum"; true)
      handle ERROR _ => false
    val _ = writeln ("my_sum visible in next proof step = " ^
                     Bool.toString is_known)
  \<close>
  show "True \<and> True" by simp
qed

ML \<open>
  val is_known =
    (Syntax.read_term \<^context> "my_sum"; true)
    handle ERROR _ => false
  val _ = writeln ("my_sum visible after proof = " ^ Bool.toString is_known)
\<close>

end
