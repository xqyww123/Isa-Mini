
session Minilang = Auto_Sledgehammer +
  theories
    Minilang_Base
    Minilang

session Minilang_Agent in Agent = Minilang +
  sessions
    Isabelle_RPC
    Semantic_Embedding
  theories
    Minilang_Agent

session Minilang_Agent_Injector in "Agent/Injector" = Minilang_Agent +
  theories
    Minilang_Agent_Injector

(*
session Infra_Filter_Test in Test_InfraFilter = "HOL-Analysis" +
  sessions
    Performant_Isabelle_ML
    "HOL-Algebra"
    "HOL-Number_Theory"
    "HOL-IMP"
    "HOL-Data_Structures"
    "HOL-Computational_Algebra"
    Lifting_the_Exponent
    Gauss_Jordan
    Polynomial_Factorization
    Catalan_Numbers
    Bernoulli
    Bell_Numbers_Spivey
  theories
    Test_LTE_InfraFilter
*)
