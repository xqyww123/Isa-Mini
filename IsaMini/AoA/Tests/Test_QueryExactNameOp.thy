theory Test_QueryExactNameOp
  imports Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.QueryExactNameOp"]]

lemma query_exact_name_op_test: "(n::nat) = n"
  by aoa

end
