theory Test_Minilang_Ctxt_Probe
  imports Minilang.Minilang
begin

text \<open>
  Probe: mirror the agent path (Have -> Intro -> Induction with
  nat_less_induct, generalizing n) using the Minilang library
  directly, then inspect what Minilang.context_of returns and how
  the IH term prints under it.
\<close>

lemma probe:
  fixes f :: "nat \<Rightarrow> nat" and p :: nat and i :: nat
  shows "True"
proof -
  have gen: "\<And>n::nat. n \<le> p - 2 \<Longrightarrow> f n < p"
  proof -
    fix n :: nat
    assume premise0: "n \<le> p - 2"
    show "f n < p"
      apply (tactic \<open>
        fn st => let
          val ctxt = @{context}
          val s0 = Minilang.INIT ctxt st
          (* Run Minilang INDUCT: target = n, arbitrary = [n], rule = nat_less_induct *)
          val rule_thm = @{thm nat_less_induct}
          val arbitrary : term list list = [[@{term "n::nat"}]]
          val vars = [] : (binding option * (term * bool)) option list list
          val insts : (binding option * (term * bool)) option list list =
            [[SOME (NONE, (@{term "n::nat"}, false))]]
          val induct_args =
            (false, (insts, ((arbitrary, []), SOME [rule_thm])))
          val s1 = Minilang.INDUCT induct_args [] {using=[], insertion=[]} s0

          val ctxt' = Minilang.context_of s1
          val n_fixes = filter (fn (e,_) => e = "n")
                              (Variable.dest_fixes ctxt')
          fun show_fix (e,i) = "    " ^ e ^ "  <->  " ^ i
          val intern_n = Variable.intern_fixed ctxt' "n"
          val all_fixes = Variable.dest_fixes ctxt'
        in
          writeln "=== MINILANG path: Minilang.context_of s1 (POST Induction) ===";
          writeln ("  ALL dest_fixes count: " ^ string_of_int (length all_fixes));
          writeln ("  n-fixes:");
          List.app (writeln o show_fix) n_fixes;
          writeln ("  intern_fixed \"n\" = \"" ^ intern_n ^ "\"");
          List.app (fn (_, internal_nm) =>
            writeln ("  Syntax.string_of_term Free(\"" ^ internal_nm
                    ^ "\", nat) with ctxt' = "
                    ^ Syntax.string_of_term ctxt' (Free (internal_nm, @{typ nat}))))
            n_fixes;
          Seq.single st   (* leave the goal untouched; we only want the probe output *)
        end
      \<close>)
      oops
qed
  oops

end
