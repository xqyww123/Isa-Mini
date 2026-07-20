theory Test_RewriteFlipForall
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RewriteFlipForall"]]

lemma rewrite_flip_forall_test:
  assumes h: "\<forall>z::nat. f z = z + 1"
  shows "(3::nat) + 1 = f 3"
  by aoa

end
