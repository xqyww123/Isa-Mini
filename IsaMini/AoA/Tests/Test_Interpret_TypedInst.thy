theory Test_Interpret_TypedInst
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Interpret_TypedInst"]]

(* Multi-token instantiation values (the cartouche path). Inside a locale
   expression, `where p = v` reads `v` with `Parse.term`, which consumes exactly
   ONE outer token, so a type-annotated term such as `(0::int)` or `1 + (1::int)`
   would not parse bare -- `interpret_i` must wrap every value in a cartouche. *)

locale it_ord = fixes lo :: int and hi :: int assumes it_lt: "lo < hi"
begin
lemma it_le: "lo \<le> hi" using it_lt by simp
end

lemma "(0::int) \<le> 1 + 1"
  by aoa

end
