theory Test_NA_Rename_Debug2
  imports Main
begin

text \<open>Exact Isar replay of: outer lemma with f, p, i fixed, then a
  Have with ⋀n. n ≤ p-2 ⟹ f n < p, Intro-like fix n, then induction
  on n using nat_less_induct.\<close>

lemma probe:
  fixes f :: "nat \<Rightarrow> nat" and p :: nat and i :: nat
  shows True
proof -
  have gen: "\<And>n::nat. n \<le> p - 2 \<Longrightarrow> f n < p"
  proof -
    fix n :: nat
    assume "n \<le> p - 2"
    show "f n < p"
    proof (induct n rule: nat_less_induct)
      case (1 n)
      ML_val \<open>
        let
          val ctxt = @{context}
          val fixes = Variable.dest_fixes ctxt
          val n_fixes = filter (fn (ext, _) => ext = "n") fixes
          val intern_n = Variable.intern_fixed ctxt "n"
        in
          writeln "=== at case 1 of nat_less_induct, inside Have sub-proof ===";
          writeln ("  fixes with ext='n':");
          List.app (fn (e, i) => writeln ("    " ^ e ^ "  <->  " ^ i)) n_fixes;
          writeln ("  intern_fixed ctxt \"n\" = \"" ^ intern_n ^ "\"");
          List.app (fn (_, i) =>
            writeln ("  Syntax.string_of_term Free(\"" ^ i ^ "\", nat)  =  "
                     ^ Syntax.string_of_term ctxt (Free (i, @{typ nat}))))
            n_fixes;
          writeln ("  IH (1.IH) pretty:");
          List.app (fn th =>
            writeln ("    " ^ Syntax.string_of_term ctxt (Thm.prop_of th)))
            (Proof_Context.get_thms ctxt "1.IH"
              handle ERROR _ => (Proof_Context.get_thms ctxt "IH"
                                  handle ERROR _ => []))
        end
      \<close>
      show ?case sorry
    qed
  qed
  show ?thesis by simp
qed

end
