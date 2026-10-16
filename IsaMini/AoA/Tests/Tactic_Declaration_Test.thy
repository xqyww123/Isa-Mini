theory Tactic_Declaration_Test
  imports User_Operation_Test_Base
begin

text \<open>
  The \<open>AoA_tactics\<close> declaration (docs/TACTIC_DESIGN.md, section 5.1): the
  design's own example as a top-level declaration, then, applied from ML so
  that the theory stays error-free, the mode defaulting to \<open>add:\<close>, a missing
  interpretation, \<open>shown_in\<close> defaulting to \<open>query\<close>, \<open>del:\<close>, the last
  declaration of a name winning, and a misspelt name.
\<close>

declare [[AoA_tactics add: simp \<open>rewrite the goal with the simplifier\<close>
                           induction \<open>prove by induction on a variable\<close> shown_in: prompt]]

ML \<open>
local
open User_Operation_Test
val ctxt = \<^context>
val full = Method.check_name ctxt o rpair Position.none
fun names ctxt = map #name (MiniLang_Agent_AoA.tactics_of ctxt)
fun the_entry ctxt name =
  (case find_first (fn e => #name e = name) (MiniLang_Agent_AoA.tactics_of ctxt) of
     SOME e => e
   | NONE => error (name ^ " is not in the whitelist"))
val declared = declared "AoA_tactics"
in

(*1: the design's example, declared above: two entries in whitelist order*)
val _ = assert "the names, in whitelist order" (names ctxt = ["induction", "simp"])
val _ = assert "simp: the full name" (#full (the_entry ctxt "simp") = full "simp")
val _ = assert "simp: the interpretation, verbatim"
          (#interpretation (the_entry ctxt "simp") = "rewrite the goal with the simplifier")
val _ = assert "simp: shown_in omitted = query" (not (#in_prompt (the_entry ctxt "simp")))
val _ = assert "induction: shown_in: prompt" (#in_prompt (the_entry ctxt "induction"))
val _ = assert "induction: the full name" (#full (the_entry ctxt "induction") = full "induction")
val _ = assert "the key is the method's universal key"
          (#key (the_entry ctxt "simp") = #1 (Universal_Key.key_of_method (Context.Proof ctxt) "simp"))
val _ = writeln ("full names: " ^ commas (map #full (MiniLang_Agent_AoA.tactics_of ctxt)))

(*2: the mode omitted is add:*)
val ctxt2 = declared ctxt "auto \<open>prove by classical reasoning and rewriting\<close>"
val _ = assert "add: omitted adds" (names ctxt2 = ["auto", "induction", "simp"])
val _ = assert "the entry is a query entry" (not (#in_prompt (the_entry ctxt2 "auto")))

(*3: a missing interpretation is a parse error (the next name is not taken for
  it), as is a shown_in value other than prompt/query; a failed parse yields no
  context at all, so a partial whitelist cannot happen*)
val _ = fails_with "Bad arguments for attribute \"AoA_tactics\"" (fn () => declared ctxt "add: blast auto")
val _ = fails_with "Bad arguments for attribute \"AoA_tactics\""
          (fn () => declared ctxt "simp \<open>simplify\<close> shown_in: nowhere")

(*4: del:*)
val _ = assert "del: removes" (names (declared ctxt "del: simp") = ["induction"])

(*5: the last declaration of a name wins*)
val ctxt5 = declared ctxt "simp \<open>simplify\<close> shown_in: prompt"
val _ = assert "last wins: still one entry" (names ctxt5 = ["induction", "simp"])
val _ = assert "last wins: the interpretation" (#interpretation (the_entry ctxt5 "simp") = "simplify")
val _ = assert "last wins: shown_in" (#in_prompt (the_entry ctxt5 "simp"))

(*6: a misspelt name is an error of the declaration*)
val _ = fails_with "Undefined method" (fn () => declared ctxt "smip \<open>simplify\<close>")

(*7: the ML entry: the same entries as the declaration, the last of a name
  winning, a misspelt name an error*)
fun added ctxt entries =
  Context.the_proof (MiniLang_Agent_AoA.add_tactics entries (Context.Proof ctxt))
val ctxt7 =
  added ctxt
    [("auto", {interpretation = "prove by classical reasoning and rewriting", in_prompt = false}),
     ("simp", {interpretation = "simplify", in_prompt = true})]
val _ = assert "ML entry: adds" (names ctxt7 = ["auto", "induction", "simp"])
val _ = assert "ML entry: the full name" (#full (the_entry ctxt7 "auto") = full "auto")
val _ = assert "ML entry: the interpretation, verbatim"
          (#interpretation (the_entry ctxt7 "auto") = "prove by classical reasoning and rewriting")
val _ = assert "ML entry: a query entry" (not (#in_prompt (the_entry ctxt7 "auto")))
val _ = assert "ML entry: last wins: the interpretation"
          (#interpretation (the_entry ctxt7 "simp") = "simplify")
val _ = assert "ML entry: last wins: shown_in" (#in_prompt (the_entry ctxt7 "simp"))
val _ = assert "ML entry: nothing added is nothing changed"
          (names (added ctxt []) = names ctxt)
val _ = fails_with "Undefined method"
          (fn () => added ctxt [("smip", {interpretation = "simplify", in_prompt = false})])

val _ = writeln "ALL PASS: Tactic_Declaration_Test"
end
\<close>

end
