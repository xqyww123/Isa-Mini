
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

(* Minilang_Agent_Injector lives in Agent/Injector/ROOT, NOT here: it needs
   `Sign.map_syn`, which only exists with my-better-isabelle-prover's `expose_map_syn`
   patch -- a `dev`-category patch that the published conda `isabelle` package
   deliberately does not carry.  `isabelle components -u` exposes this whole ROOT, so
   declaring it here makes it fail for every user of that package.  See that file. *)

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
