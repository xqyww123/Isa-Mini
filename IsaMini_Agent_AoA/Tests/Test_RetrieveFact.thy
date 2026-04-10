theory Test_RetrieveFact
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin
 
declare [[agent_AoA_driver="test.SemanticKNN_patterns"]]

lemma retrieve_fact_test: "0 < (x::real) \<Longrightarrow> ln (x ^ n) = real n * ln x"
  by  aoa


term \<open>Num.pow a b\<close>
term \<open>power2 1\<close>
ML \<open>@{term \<open>x ^ b\<close>}\<close>
term Power.power_class.power

declare [[smt_nat_as_int]]
lemma "2 * (x::nat) \<noteq> 1" by smt
  






term \<open>ln_class.ln\<close>
term \<open>ln_class\<close>
term \<open>Transcendental.class.ln\<close>









ML \<open>Seman tic_Store.query_semantics   (Context.Theory @{theory})
      (Universal_Key.Constant "SMT.z3mod") false\<close>

term Power.power.power
term Power.power_class.power
term \<open>Num.pow (3::nat) (4::nat)\<close>



term Transcendental.powr_real
term String.char.digit2
term String.linordered_euclidean_semiring_bit_operations_class.char_of


lemma \<open>log (2::real) (8::real) = (3::real)\<close>
proof -
  have t1: "8 = (2::real) ^ 3" by auto
  show "log (2::real) (8::real) = (3::real)"
    using log_nat_power t1
    by (metis log2_of_power_eq of_nat_numeral of_nat_power) 

end
