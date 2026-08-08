theory My_Object_Logic_E2E_Test
  imports Minilang.Minilang
begin

(* MY_OBJECT_LOGIC_PLAN.md section 8-1 end-to-end example.  Red baseline on the
   unswitched tree: PRINT showed  res : CC \<longrightarrow> All RR5 \<longrightarrow> BB  (binder name and
   eta-redex lost).  Expected after the aux.ML:292 switch:
   res : CC \<longrightarrow> (\<forall>yyy. RR5 yyy) \<longrightarrow> BB *)

axiomatization
      AA BB CC :: bool
  and RR5 :: "nat \<Rightarrow> bool"
where
      e2e_rule2 : "AA \<longrightarrow> (\<forall>yyy. RR5 yyy) \<longrightarrow> BB"
  and fA        : "CC \<Longrightarrow> AA"

lemma "True"
  by (min_script \<open>SPECIALIZE res: e2e_rule2 WITH fA  PRINT  END\<close>)

(* Machine-checked form of the same pipeline (review finding A1): the lemma
   above passes whether PRINT shows the repaired or the damaged form, because
   the two are alpha/eta-equivalent.  Here the identical SPECIALIZE runs via
   the ML API and the result is pinned STRUCTURALLY: the expected term is
   ML-built (Syntax.read_* would eta-contract it at parse time), compared with
   aconv AND a positional binder-name walk, so both the eta-redex body and the
   binder name `yyy` are asserted. *)
ML \<open>
local
  val base_ctxt = Named_Target.theory_init \<^theory>;
  val st = Minilang.INIT base_ctxt (Goal.init (Thm.cterm_of base_ctxt \<^prop>\<open>True\<close>));
  val st' = Minilang.parse_cmds (Minilang.lex_cmds "SPECIALIZE res: e2e_rule2 WITH fA") st;
  val res = Proof_Context.get_thm (Minilang.context_of st') "res";

  fun binder_names (Abs (n, _, b)) = n :: binder_names b
    | binder_names (f $ x) = binder_names f @ binder_names x
    | binder_names _ = [];

  val expected =
    HOLogic.mk_Trueprop
      (HOLogic.mk_imp (\<^term>\<open>CC\<close>,
         HOLogic.mk_imp
           (HOLogic.mk_all ("yyy", \<^typ>\<open>nat\<close>, \<^term>\<open>RR5\<close> $ Bound 0),
            \<^term>\<open>BB\<close>)));
in
val _ =
  if Thm.prop_of res aconv expected
     andalso binder_names (Thm.prop_of res) = ["yyy"]
  then writeln "E2E ASSERTION: OK (eta-redex body and binder name yyy preserved)"
  else error ("E2E ASSERTION FAILED\n  GOT  " ^ @{make_string} (Thm.prop_of res) ^
              "\n  WANT " ^ @{make_string} expected)
end
\<close>

end
