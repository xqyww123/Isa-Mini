theory Test_Define_SucPattern
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_SucPattern"]]

(* Test: Define with Suc constructor patterns.

   In imo_1974_p3 (imports Complex_Main + HOL-Number_Theory +
   HOL-Computational_Algebra), the LLM's Define with Suc patterns was
   rejected with "Non-constructor pattern not allowed in sequential
   mode".  This test verifies the same equations WORK in the standard
   Minilang_AoA context — proving the bug is theory-import-dependent,
   not a universal Define defect.
*)

lemma define_suc_pattern_test:
  "\<exists>f :: nat \<Rightarrow> nat. f 3 = 8"
  by  aoa

end
