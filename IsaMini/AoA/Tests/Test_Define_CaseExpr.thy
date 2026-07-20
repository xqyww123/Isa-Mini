theory Test_Define_CaseExpr
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_CaseExpr"]]

(* Reproducer for fastype_of: Bound.
   Defining a recursive function whose RHS uses a `case` expression
   triggers check_looping_simp_rules -> matches_subterm_of, which
   descends into the Abs body of the case without substituting
   the bound variable, leaving loose de Bruijn indices that crash
   fastype_of inside Pattern.match. *)

lemma define_case_expr_test:
  "\<exists>f :: nat \<Rightarrow> nat \<times> nat. fst (f (Suc 0)) = 2"
  by  aoa

end
