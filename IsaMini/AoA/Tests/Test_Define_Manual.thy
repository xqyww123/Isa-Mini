theory Test_Define_Manual
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_Manual"]]

(* Force the Define node's auto-prove path (default prover + BY_METRIC
   sledge fallback + auto+termination_simp simplification) to fail,
   so the termination residuals — `wf (measure (\<lambda>n. n))` and the raw
   decrease obligation — are pushed onto the minilang stack as a
   deferred block. The agent then discharges each residual with
   Obvious. *)
setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma define_manual_test: "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc (Suc 0)))) = Suc (Suc 0)"
  by  aoa

end
