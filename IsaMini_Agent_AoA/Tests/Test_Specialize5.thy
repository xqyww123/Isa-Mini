theory Test_Specialize5
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Derive5"]]

lemma specialize_test5:
  assumes h1: "(x::int) mod q = y mod q"
      and h2: "coprime q (2::int)"
    shows "x mod q = y mod q"
thm mult_mod_cancel_left[OF _ h2]
  by aoa



end
