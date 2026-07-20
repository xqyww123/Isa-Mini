theory Test_HavePowerParsing
  imports Complex_Main MathBench_Prover.MathBench_Prover Minilang_AoA.Minilang_AoA
begin

declare [[auto_interpret_for_embedding=false, AoA_interactive_retrieval="no"]]

lemma power_parse_test:
  fixes a b c :: real
  shows "a * b * (a^2 - b^2) + b *c * (b^2 - c^2) + c * a * (c^2 - a^2) \<le> (9::real) * sqrt 2 / 32 * (a^2 + b^2 + c^2)^2"
  by a oa

end
