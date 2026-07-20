theory Test_BranchSorryNextFail
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Branch_SorryNextFail_Real"]]

definition hfinf :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "hfinf f \<equiv> (\<forall>x. 0 \<le> f x) \<and> continuous_on {0..} f"

definition hf :: "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "hf e f \<equiv> (\<forall>x. 0 \<le> f x) \<and> continuous_on {0..<e} f"

lemma
  "\<forall>f \<in> {(g::real \<Rightarrow> real). \<exists>(a::real) (c::real). 0 \<le> a \<and> g = (\<lambda>x. a / (1 - c * x)\<^sup>2)}.
   hfinf f \<or> (\<exists>e>0. hf e f)"
  by   aoa

end
