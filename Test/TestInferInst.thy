theory TestInferInst
  imports Main
begin

(* A schematic rule mimicking the shape of setCTE_ko_at'_pde. *)
lemma my_rule: "P x \<Longrightarrow> P x"
  by assumption

(* A rule with a concrete type (?n::nat) to exercise the pde/asidpool shape
   from /tmp/t3. *)
lemma my_rule2: "Suc n > n"
  by simp

ML \<open>
(* ---- Simulate the planned fix ----

   1. `try_inst_schematic` wraps `Drule.infer_instantiate` and catches
      THM, stripping the internal prefix and re-raising as ERROR.

   2. `try_specialize` wraps the whole thing, catches ERROR, and
      prepends the rule name / appends the rule statement, mimicking
      the OPR_FAIL message produced by SPECIALIZE' in proof.ML.
*)

fun try_inst_schematic ctxt insts thm =
  let val ct_insts = map (fn (idx, t) => (idx, Thm.cterm_of ctxt t)) insts
  in Drule.infer_instantiate ctxt ct_insts thm
     handle THM (msg, _, _) =>
       let val cleaned =
             perhaps (try (unprefix "infer_instantiate_types: ")) msg
           val indented =
             String.translate (fn #"\n" => "\n  " | c => str c) cleaned
       in error ("type mismatch in instantiation:\n  " ^ indented) end
  end

fun try_specialize ctxt rule_name insts thm =
  try_inst_schematic ctxt insts thm
  handle ERROR msg =>
    error (String.concat [
      "cannot instantiate rule \<open>", rule_name, "\<close>:\n",
      msg, "\n",
      "the rule is:\n  ", Thm.string_of_thm ctxt thm])

(* Pretty-print the final ERROR (which is what SPECIALIZE' would raise
   via OPR_FAIL — the agent sees the `msg` string). *)
fun show ctxt f =
  (f (); writeln "SUCCEEDED unexpectedly")
  handle ERROR msg => writeln ("--- agent sees ---\n" ^ msg ^ "\n------------------")
       | e => writeln ("--- unexpected: " ^ exnMessage e)

val ctxt = \<^context>
val rule  = @{thm my_rule}
val rule2 = @{thm my_rule2}

val _ = writeln "\n### Case 1: ?P := id  (on my_rule)"
val _ = show ctxt (fn () =>
  try_specialize ctxt "my_rule"
    [(("P", 0), @{term "id :: 'a \<Rightarrow> 'a"})] rule)

val _ = writeln "\n### Case 2: ?P := (\<lambda>n::nat. n)  (on my_rule)"
val _ = show ctxt (fn () =>
  try_specialize ctxt "my_rule"
    [(("P", 0), @{term "\<lambda>n::nat. n"})] rule)

val _ = writeln "\n### Case 3: batch [?x := 0, ?P := id]  (on my_rule)"
val _ = show ctxt (fn () =>
  try_specialize ctxt "my_rule"
    [(("x", 0), @{term "0::nat"}),
     (("P", 0), @{term "id :: 'a \<Rightarrow> 'a"})] rule)

val _ = writeln "\n### Case 4: ?n := True  (on my_rule2 — pde/asidpool shape)"
val _ = show ctxt (fn () =>
  try_specialize ctxt "my_rule2"
    [(("n", 0), @{term "True"})] rule2)

val _ = writeln "\n### Case 5: ?P := (\<lambda>b::bool. b)  (on my_rule — well-typed, should SUCCEED)"
val _ = show ctxt (fn () =>
  try_specialize ctxt "my_rule"
    [(("P", 0), @{term "\<lambda>b::bool. b"})] rule)
\<close>

end
