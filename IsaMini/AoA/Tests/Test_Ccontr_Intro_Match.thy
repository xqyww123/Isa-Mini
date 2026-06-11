theory Test_Ccontr_Intro_Match imports
MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin

declare [[auto_interpret_for_embedding=false]]
declare [[agent_AoA_driver="test.CcontrIntroMatch"]]

theorem rabinowitz:
  fixes p :: nat
    and f :: "nat \<Rightarrow> nat"
  assumes h0 : "\<And>x. f x = x^2 + x + p"
    and h1 : "\<And>(k::nat). (k\<le>floor(sqrt (p/3))) \<Longrightarrow> prime (f k)"
  shows "\<And>i. (i \<le> p - 2) \<Longrightarrow> prime (f i)"
  by ao a

term Minilang.TAG

end
