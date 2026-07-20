theory Test_QueryExactNameOp
  imports Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.QueryExactNameOp"]]

lemma query_exact_name_op_test: "(n::nat) = n"
  by aoa

end
