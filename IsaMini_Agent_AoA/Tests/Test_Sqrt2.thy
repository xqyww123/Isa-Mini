theory Test_Sqrt2
  imports Minilang_Agent.Minilang_Agent
begin

lemma \<open>sqrt(2) \<notin> \<rat>\<close>
  by      AgentAoA

thm Groebner_Basis.bool_simps(27)

end