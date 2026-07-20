theory Test_QueryWholeFileDump
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.QueryWholeFileDump"]]

lemma query_whole_file_dump_test: "(n::nat) = n"
  by aoa

end
