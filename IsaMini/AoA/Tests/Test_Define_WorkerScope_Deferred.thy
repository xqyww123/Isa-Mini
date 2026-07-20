theory Test_Define_WorkerScope_Deferred
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_WorkerScope_Deferred"]]

setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma define_worker_scope_test: "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc (Suc 0)))) = Suc (Suc 0)"
  by  aoa

end
