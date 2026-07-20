theory Test_Specialize2
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Specialize2"]]

lemma specialize_test2:
  assumes h1: "P (0::nat)"
      and h2: "P (0::nat) \<longrightarrow> Q (0::nat)"
  shows "Q (0::nat)"
  by   aoa

ML \<open>Par_Exn.release_first\<close>

end
