theory Test_UnfoldSyntaxOp
  imports Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.UnfoldSyntaxOp"]]

lemma unfold_syntax_op_test: "(n::nat) = n"
  by aoa

end
