theory Test_Define_WorkerConfineReject
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_WorkerConfineReject"]]

setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma define_worker_confine_test: "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc (Suc 0)))) = Suc (Suc 0)"
  by  aoa

end
