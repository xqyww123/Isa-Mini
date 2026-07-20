theory Test_ResolveContextAt
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ResolveContextAt"]]

lemma resolve_context_at_test:
  fixes x :: "int"
  assumes h1: "y = x + 0"
      and h2: "z = y * 1"
  shows "x = z"
  by  aoa

end
