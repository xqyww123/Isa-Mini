theory Test_SimpRoles_Debug
  imports Complex_Main
begin

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0"
| "double (Suc n) = Suc (Suc (double n))"

ML \<open>
let
  val ctxt = \<^context>
  val thy = Proof_Context.theory_of ctxt
  val facts = Proof_Context.facts_of ctxt
  val f = TextIO.openOut "/tmp/simp_roles_debug.log"

  fun lookup_thm name idx =
    let val full = Facts.intern facts name
    in case Facts.lookup (Context.Proof ctxt) facts full of
         SOME {thms, ...} => SOME (nth thms idx)
       | NONE => NONE
    end

  fun test_thm label thm =
    let
      val name_hint = Thm.get_name_hint thm
      val maxidx = Thm.maxidx_of thm
      val nprems = Thm.nprems_of thm
      val concl_head = case Thm.concl_of thm of
          Const (c, _) $ _ => c | Const (c, _) => c | _ => "<other>"

      val mksimps_result = try (Raw_Simplifier.mksimps ctxt) thm
      val mksimps_count = case mksimps_result of SOME ths => length ths | NONE => ~1

      val transferred = Thm.transfer thy thm
      val mksimps_transferred = try (Raw_Simplifier.mksimps ctxt) transferred
      val mksimps_tr_count = case mksimps_transferred of SOME ths => length ths | NONE => ~1

      val gen = Variable.gen_all ctxt thm
      val mksimps_gen = try (Raw_Simplifier.mksimps ctxt) gen
      val mksimps_gen_count = case mksimps_gen of SOME ths => length ths | NONE => ~1
    in
      TextIO.output (f, label ^ ":\n");
      TextIO.output (f, "  name_hint=" ^ name_hint ^ "\n");
      TextIO.output (f, "  maxidx=" ^ string_of_int maxidx ^ "\n");
      TextIO.output (f, "  nprems=" ^ string_of_int nprems ^ "\n");
      TextIO.output (f, "  concl_head=" ^ concl_head ^ "\n");
      TextIO.output (f, "  mksimps=" ^ string_of_int mksimps_count ^ "\n");
      TextIO.output (f, "  mksimps(transferred)=" ^ string_of_int mksimps_tr_count ^ "\n");
      TextIO.output (f, "  mksimps(gen_all)=" ^ string_of_int mksimps_gen_count ^ "\n")
    end

  val compile_add0 = @{thm add_0}
  val fact_add0 = the (lookup_thm "add_0" 0)

  val compile_double1 = @{thm double.simps(1)}
  val fact_double1 = the (lookup_thm "double.simps" 0)

  val _ = TextIO.output (f, "=== Comparing compile-time vs fact-table theorems ===\n\n")
  val _ = test_thm "@{thm add_0}" compile_add0
  val _ = test_thm "Facts.lookup add_0" fact_add0
  val _ = TextIO.output (f, "  props aconv=" ^
            Bool.toString (Thm.prop_of compile_add0 aconv Thm.prop_of fact_add0) ^ "\n")
  val _ = TextIO.output (f, "  eq_thm=" ^
            Bool.toString (Thm.eq_thm (compile_add0, fact_add0)) ^ "\n\n")

  val _ = test_thm "@{thm double.simps(1)}" compile_double1
  val _ = test_thm "Facts.lookup double.simps(1)" fact_double1
  val _ = TextIO.output (f, "  props aconv=" ^
            Bool.toString (Thm.prop_of compile_double1 aconv Thm.prop_of fact_double1) ^ "\n")
  val _ = TextIO.output (f, "  eq_thm=" ^
            Bool.toString (Thm.eq_thm (compile_double1, fact_double1)) ^ "\n\n")

  (* Build simp_rule_net like agent_server.ML does *)
  val ss_simps = #simps (Raw_Simplifier.dest_ss (Raw_Simplifier.simpset_of ctxt))
  val simp_rule_net =
    fold (fn (_, thm) =>
      let val p = Thm.prop_of thm
      in Net.insert_term_safe (op aconv) (p, p) end) ss_simps Net.empty
  fun in_rule_net net prop =
    exists (fn stored => prop aconv stored) (Net.match_term net prop)

  (* Test the full thm_roles pipeline with transfer fix *)
  fun test_roles label thm =
    let val simp_props =
          the_default []
            (try (map Thm.prop_of o Raw_Simplifier.mksimps ctxt
                  o Thm.transfer thy) thm)
        val is_simp = exists (in_rule_net simp_rule_net) simp_props
    in TextIO.output (f, label ^ ": is_simp=" ^ Bool.toString is_simp ^
         " simp_props_count=" ^ string_of_int (length simp_props) ^ "\n")
    end

  val _ = TextIO.output (f, "\n=== Full pipeline test (with Thm.transfer fix) ===\n")
  val _ = test_roles "fact add_0" fact_add0
  val _ = test_roles "fact double.simps(1)" fact_double1
  val _ = test_roles "compile add_0" compile_add0
  val _ = test_roles "compile double.simps(1)" compile_double1

in TextIO.closeOut f end
\<close>

end
