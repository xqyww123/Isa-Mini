theory Test_Define_DeleteOracle
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Define_DeleteOracle"]]

(* Generic Define setup: we DELETE the Define after using halve as the
   witness. Probes whether `halve` survives deletion in the live state. *)
setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma define_delete_oracle_test: "\<exists>f :: nat \<Rightarrow> nat. f 0 = f 0"
  by  aoa

end
