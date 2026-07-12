theory Test_Interpret_UnknownLocale
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Interpret_UnknownLocale"]]

(* Error path: a locale name that does not exist. The locale-expression parser
   inside `interpret_i` rejects it, which must surface as a plain (retryable)
   operation FAILURE on the node -- not as a crash of the proof session. The
   slot stays fillable, so the agent can recover. *)

lemma "(0::nat) < 1"
  by aoa

end
