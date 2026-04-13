theory Test_Specialize4
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Specialize4"]]

lemma specialize_test4:
  assumes h1: "P (0::nat)"
      and h2: "\<forall>x::nat. P x \<longrightarrow> Q x"
  shows "Q (1 - (1::nat))"
  by  a oa

notepad
begin
  assume A: \<open>AAA\<close>
  ML_val \<open>Thm.get_name_hint @{thm A}\<close>
end

ML \<open>Proof_Context.note_thms "" ((\<^binding>\<open>AA\<close>, []), [(@{thms allI}, [])]) \<^context>
  |> fst |> snd |> hd |> Thm.get_name_hint\<close>

end
