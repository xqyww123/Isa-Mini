theory Define_Suc_Conflict_Test
  imports Main
begin

lemma fixes n :: nat shows "True"
proof -
  define g where "g n = n + (1::nat)"
  show ?thesis ..
qed

end
