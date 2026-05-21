theory Test_Explain_Term_Printer
  imports Semantic_Embedding.Semantic_Embedding
begin

text \<open>Test: compact\_term on user-defined constant\<close>

definition my_fun :: "nat \<Rightarrow> nat" where
  "my_fun x = x + 1"

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "map my_fun [1,2,3::nat]"
  in
    writeln ("--- compact: map my_fun [...] ---");
    writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test: locale abbreviation contraction\<close>

locale test_locale =
  fixes y :: nat
begin

definition g :: "nat \<Rightarrow> nat" where
  "g x = y + x"

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "g (Suc 0)"
  in
    writeln ("--- locale g (Suc 0) ---");
    writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

end

end
