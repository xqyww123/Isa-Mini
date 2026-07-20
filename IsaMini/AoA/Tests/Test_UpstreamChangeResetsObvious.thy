theory Test_UpstreamChangeResetsObvious
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.UpstreamChangeResetsObvious"]]

lemma upstream_change_test:
  assumes h1: "x = (1::nat)"
      and h2: "y = (2::nat)"
  shows "x + y = 3"
  by aoa

end
