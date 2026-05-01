theory Test_RenameIntroVar
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RenameIntroVar"]]

lemma "\<forall>x::nat. x = x"
  by   aoa

end
