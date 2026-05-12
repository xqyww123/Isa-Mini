theory Test_RewriteFlipForall
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RewriteFlipForall"]]

lemma rewrite_flip_forall_test:
  assumes h: "\<forall>z::nat. f z = z + 1"
  shows "(3::nat) + 1 = f 3"
  by aoa

end
