theory Uncheck_Experiment
  imports Semantic_Embedding.Semantic_Embedding
begin

text \<open>Test 1: simple locale\<close>

locale my_locale =
  fixes y :: nat
begin

definition f :: "nat \<Rightarrow> nat" where
  "f x = y + x"

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "f x"
  in writeln "--- locale f x ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

end

text \<open>Test 2: complex expression\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "map Suc (filter (\<lambda>x. x > 0) [1,2,3::nat])"
  in writeln "--- map/filter ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 3: quantifiers\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "\<forall>x::nat. \<exists>y. x + y = 0"
  in writeln "--- quantifiers ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 4: set comprehension\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "{x::nat. x \<in> S \<and> x > 0}"
  in writeln "--- set comprehension ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 5: abbreviation\<close>

abbreviation my_add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "my_add x y \<equiv> x + y + 1"

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "my_add a b"
  in writeln "--- abbreviation ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 6: case expression\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "case xs of [] \<Rightarrow> 0 | (x#rest) \<Rightarrow> Suc (f rest)"
  in writeln "--- case list ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 7: let + case\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "let a = Suc 0 in case a of 0 \<Rightarrow> True | Suc n \<Rightarrow> False"
  in writeln "--- let/case ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 8: chained let\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt "let x = (1::nat); y = x + 2 in x * y"
  in writeln "--- chained let ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 9: lambda as head\<close>

ML \<open>
  let val ctxt = \<^context>
      val lam = Abs("x", \<^typ>\<open>nat\<close>,
        \<^Const>\<open>plus \<^Type>\<open>nat\<close>\<close> $ Bound 0 $ HOLogic.mk_number \<^typ>\<open>nat\<close> 1)
      val term = lam $ HOLogic.mk_number \<^typ>\<open>nat\<close> 5
  in writeln "--- lambda head ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 10: nested case (flattened by strip\_case)\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt
        "case p of (x, y) \<Rightarrow> case x of 0 \<Rightarrow> y | Suc n \<Rightarrow> n + y"
  in writeln "--- nested case (flattened) ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 11: case in case RHS (independent scrutinee, not flattened)\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt
        "case x of 0 \<Rightarrow> (case y of True \<Rightarrow> (1::nat) | False \<Rightarrow> 2) | Suc n \<Rightarrow> 3"
  in writeln "--- case in case RHS ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 12: let in let value\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt
        "let x = (let y = (1::nat) in y + 1) in x * 2"
  in writeln "--- let in let value ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

text \<open>Test 13: case as scrutinee\<close>

ML \<open>
  let val ctxt = \<^context>
      val term = Syntax.read_term ctxt
        "case (case b of True \<Rightarrow> (0::nat) | False \<Rightarrow> 1) of 0 \<Rightarrow> True | Suc n \<Rightarrow> False"
  in writeln "--- case as scrutinee ---";
     writeln (Explain_Term.raw_lambda_printer ctxt term)
  end
\<close>

end
