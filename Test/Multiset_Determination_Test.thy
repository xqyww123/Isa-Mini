theory Multiset_Determination_Test
  imports MathBench_Prover.MathBench_Prover
begin

section \<open>Check accessibility of key lemmas from MathBench\_Prover\<close>

thm sum_mset_mono
thm size_eq_sum_mset
thm dvd_imp_le
thm nat_dvd_not_less
thm dvd_prod_mset
thm multiset_eq_iff
thm multiset_eqI
thm multiset_partition
thm filter_eq_replicate_mset
thm set_mset_subset_singletonD
thm sum_mset_replicate_mset
thm size_replicate_mset
thm prod_mset_replicate_mset
thm multi_member_split
thm count_eq_zero_iff
thm size_Diff_singleton
thm sum_mset.add_mset
thm prod_mset.add_mset
thm in_diffD

end
