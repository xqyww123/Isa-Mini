theory Test_Obvious_partial_solve imports
  Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Obvious_partial_solve"]]

theorem aime_1988_p3:
  fixes x :: real
  assumes h0 : "0 < x"
    and h1 : "log 2 (log 8 x) = log 8 (log 2 x)"
    and valid: "0 < log 8 x" "0 < log 2 x"
  shows "(log 2 x)^2 = 27"
  by  aoa

end
