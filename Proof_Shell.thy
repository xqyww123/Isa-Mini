theory Proof_Shell
  imports HOL.HOL
begin

ML_file \<open>./library/proof.ML\<close>

ML \<open>Pattern.match \<^theory> (Var (("a",0),\<^typ>\<open>prop\<close>), Free ("aaa", \<^typ>\<open>prop\<close>)) (Vartab.empty, Vartab.empty)\<close>

  obtain

lemma True
  apply induct

end