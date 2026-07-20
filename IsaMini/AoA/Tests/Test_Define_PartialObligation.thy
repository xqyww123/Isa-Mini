theory Test_Define_PartialObligation
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_PartialObligation"]]

setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma define_partial_obligation_test: "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc (Suc 0)))) = Suc (Suc 0)"
  by  aoa

end
