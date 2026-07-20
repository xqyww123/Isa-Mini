theory Test_UnfoldSyntax
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

abbreviation my_conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "my_conj a b \<equiv> a \<and> b"

definition my_op :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "my_op x y = x + y"

notation my_op (infixl "\<oplus>" 65)

definition my_bind :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option" where
  "my_bind m f = Option.bind m f"

notation my_bind (infixl "\<bind>" 55)

definition my_forall :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "my_forall S P = (\<forall>x\<in>S. P x)"

syntax "_my_forall" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("\<forall>\<^sub>m _ \<in> _./ _" [0, 0, 10] 10)
translations "\<forall>\<^sub>m x \<in> S. P" \<rightleftharpoons> "CONST my_forall S (\<lambda>x. P)"

definition my_sum :: "nat set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "my_sum S f = (\<Sum>x\<in>S. f x)"

syntax "_my_sum" :: "pttrn \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat" ("\<Sigma>\<^sub>m _ \<in> _./ _" [0, 0, 10] 10)
translations "\<Sigma>\<^sub>m x \<in> S. t" \<rightleftharpoons> "CONST my_sum S (\<lambda>x. t)"

(* A local abbreviation whose expansion head (my_op) is a local definition with
   no Semantic_DB interpretation -- exercises the layer-4 "no semantics anywhere"
   path. RHS deliberately distinct from any term elsewhere in this theory so it
   does not contract unrelated test lines. *)
abbreviation my_twice :: "nat \<Rightarrow> nat" where
  "my_twice x \<equiv> my_op x (Suc x)"

declare [[AoA_driver="test.UnfoldSyntax"]]

lemma unfold_syntax_test: "even (n::nat) \<Longrightarrow> n mod 2 = 0"
  by  aoa

end
