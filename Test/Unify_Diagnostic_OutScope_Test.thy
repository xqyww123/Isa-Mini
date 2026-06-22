theory Unify_Diagnostic_OutScope_Test
  imports Minilang.Minilang
begin

text \<open>Direct ML-level regression test for the out-of-scope-variable case of
  @{ML Unify_Diagnostic.format_diag_body}.

  When a unification failure's clashing head symbol is an out-of-scope fixed
  variable — a skolem name the current context can no longer revert (as happens
  to a stale fact after an @{ML Minilang.INDUCT} generalizes its variable away) —
  the body must read \<open>because of the out-of-scope variable <internal>\<close> instead of
  dumping the raw \<open>head symbol X clashes with Y\<close>. The AoA Python layer
  (\<open>_postprocess_outbound_text\<close>) then rewrites \<open><internal>\<close> to the variable's
  original name plus the discarding step. A clash with no out-of-scope side must
  be reported unchanged. This guards that ML branch independently of the
  Python/Agent pipeline.\<close>

ML \<open>
let
  val ctxt0 = \<^context>
  (* A body-mode fixed variable gets a skolem internal name (e.g. "n__") which is
     out of scope when reverted in ctxt0 itself — exactly the post-induction
     stranded-variable shape. *)
  val ([nb], _) = Variable.add_fixes ["n"] (Variable.set_body true ctxt0)
  val _ = Name.is_skolem nb andalso Variable.revert_fixed ctxt0 nb = nb
            orelse error ("test precondition broken: " ^ quote nb ^
                          " is not an out-of-scope skolem var in ctxt0")

  val outscope = Unify_Diagnostic.format_diag_body ctxt0 (Unify_Diagnostic.Clash (nb, "na__"))
  val normal   = Unify_Diagnostic.format_diag_body ctxt0 (Unify_Diagnostic.Clash ("foo", "bar"))

  val _ = outscope = "because of the out-of-scope variable " ^ nb
            orelse error ("out-of-scope clash diagnostic wrong: " ^ quote outscope)
  val _ = normal = "because head symbol foo clashes with bar"
            orelse error ("normal clash diagnostic changed: " ^ quote normal)
  val _ = writeln ("Unify_Diagnostic out-of-scope diagnostic OK: " ^ quote outscope)
in () end
\<close>

end
