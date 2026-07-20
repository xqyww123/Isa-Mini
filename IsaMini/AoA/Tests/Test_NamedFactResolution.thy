theory Test_NamedFactResolution
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin
declare [[AoA_driver="test.NamedFactResolution"]]

definition NF_XXX where "NF_XXX (a::int) b = (a + b)"

lemma NF_XXX_alt: "NF_XXX a b = b + a"
  unfolding NF_XXX_def
  by auto

lemma named_fact_test: "0 < (x::real) \<Longrightarrow> ln (x ^ n) = real n * ln x"
  by  aoa

end
