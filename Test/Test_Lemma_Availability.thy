theory Test_Lemma_Availability
  imports "HOL-Analysis.Analysis"
begin

(* Goal 1: Archimedean property *)
thm ex_less_of_nat_mult
(* 0 < ?x \<Longrightarrow> \<exists>n. ?y < of_nat n * ?x *)

thm reals_Archimedean2
(* \<exists>n. ?x < of_nat n *)

(* Goal 3: sum reindex *)
thm sum.reindex
(* inj_on ?h ?A \<Longrightarrow> sum ?g (?h ` ?A) = sum (?g \<circ> ?h) ?A *)

thm sum.reindex_bij_witness
(* ... *)

thm sum.reindex_bij_betw
(* bij_betw ?h ?S ?T \<Longrightarrow> (\<Sum>x\<in>?S. ?g (?h x)) = sum ?g ?T *)

(* Goal 3: Gauss sum *)
thm gauss_sum_from_Suc_0
(* (\<Sum>i = Suc 0..?n. of_nat i) = of_nat ?n * (of_nat ?n + 1) div 2 *)

thm double_gauss_sum_from_Suc_0
(* 2 * (\<Sum>i = Suc 0..?n. of_nat i) = of_nat ?n * (of_nat ?n + 1) *)

(* Quick check: 1+2+...+28 = 406 *)
lemma "(\<Sum>i = Suc 0..(28::nat). i) = 406"
  by eval

end
