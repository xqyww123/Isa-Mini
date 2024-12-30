text \<open>Driven by AI purely and only.\<close>

theory Proof_Shell
  imports HOL.HOL Auto_Sledgehammer.Auto_Sledgehammer
begin

thm exE

(*definition Ex   where \<open>Ex   \<equiv> HOL.Ex\<close> 
definition disj where \<open>disj \<equiv> HOL.disj\<close>
definition conj where \<open>conj \<equiv> HOL.conj\<close> *)

thm exE
thm exE[OF exE]
thm conjE
ML \<open>
   Thm.biresolution NONE false [(true, @{thm exE})] 2 exE |> Seq.hd
 \<close>

ML \<open>

\<close>

ML \<open>mk_rule \<^context> 3 3\<close>

lemma XX:
  \<open>True\<close>
  unfolding Ex_def
proof -
  consider (a) "Q" | (b) x :: bool where "\<not> Q \<or> x" by blast
  then show ?thesis
    thm a
    apply cases
ML_val \<open>Proof_Context.check_case \<^context> true ("a", \<^here>) []\<close>
proof -
  ML_val \<open>Proof_Context.check_case \<^context> false ("a", \<^here>) []\<close>
  case aa: a
  thm aa
    then show ?thesis by simp
  next
ML_val \<open>Proof_Context.check_case \<^context> false ("b", \<^here>) []\<close>
  case aa: (b v)
  thm aa
  term \<open>?case\<close>
    then show ?thesis sorry
  qed


  apply (rule conjI)
  by blast

declare [[ML_debugger, ML_exception_trace]]

ML_file \<open>./library/proof.ML\<close>




notepad begin

  assume RULE: "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D"
     and RULE': "AA \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D"
  assume A: "A" and B: "B"
  have "D"
    apply (rule RULE[OF A B])
    using A B apply (rule RULE' RULE)

end


end