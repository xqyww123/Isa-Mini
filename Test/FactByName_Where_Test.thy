theory FactByName_Where_Test
  imports Minilang.Minilang
begin

declare [[quick_and_dirty]]

section \<open>Tests for FactByName with [where ...] attribute via read_fact path\<close>

text \<open>
  Tests that fact references with [where ...] attributes work when parsed
  by the agent's read_fact pipeline (Token.tokenize with Pure keywords,
  then Parse.thm, then Attrib.eval_thms).

  This is the path exercised when Python's IsabelleFact_Presented.pack()
  sends "name[where x = \<open>val\<close>]" through the RPC channel.
\<close>

ML \<open>
(* Replicate read_fact's tokenization + Parse.thm, then evaluate *)
fun test_read_fact_where ctxt src =
  let
    val keywords = Thy_Header.get_keywords \<^theory>\<open>Pure\<close>
    val symbols = Input.source_explode (Input.string src)
    val toks = Token.tokenize keywords {strict = true} symbols
               |> filter Token.is_proper
    val fact = case Scan.read Token.stopper Parse.thm toks of
                 SOME f => f
               | NONE => error ("Cannot parse \"" ^ src ^ "\" as a fact reference")
  in Attrib.eval_thms ctxt [fact] end
\<close>


subsection \<open>Schematic variable instantiation\<close>

text \<open>spec: \<open>\<forall>x. ?P x \<Longrightarrow> ?P ?a\<close> \<emdash> ?x is schematic\<close>
ML \<open>
let
  val ctxt = \<^context>
  val thms = test_read_fact_where ctxt "spec[where ?x = \<open>0 :: nat\<close>]"
  val prop = Thm.prop_of (hd thms)
  val has_zero = Term.exists_subterm
    (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
in
  if has_zero then writeln "T1 schematic via read_fact: ok"
  else error ("T1 failed: " ^ Thm.string_of_thm ctxt (hd thms))
end
\<close>


subsection \<open>HOL.All bound variable (bare name, no ?)\<close>

lemma forall_fact: \<open>\<forall>x :: nat. P x \<longrightarrow> P x\<close> for P sorry

ML \<open>
let
  val ctxt = \<^context>
  val thms = test_read_fact_where ctxt "forall_fact[where x = \<open>0 :: nat\<close>]"
  val prop = Thm.prop_of (hd thms)
  val has_zero = Term.exists_subterm
    (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
in
  if has_zero then writeln "T2 HOL.All bare name via read_fact: ok"
  else error ("T2 failed: " ^ Thm.string_of_thm ctxt (hd thms))
end
\<close>


subsection \<open>Mixed: schematic + HOL.All in one call\<close>

lemma mixed_fact: \<open>R \<Longrightarrow> \<forall>x :: nat. P x\<close> for R P sorry

ML \<open>
let
  val ctxt = \<^context>
  val thms = test_read_fact_where ctxt
    "mixed_fact[where ?R = \<open>True\<close> and x = \<open>7 :: nat\<close>]"
  val prop = Thm.prop_of (hd thms)
  val has_true = Term.exists_subterm
    (fn \<^Const_>\<open>True\<close> => true | _ => false) prop
  val has_seven = Term.exists_subterm
    (fn t => (case try HOLogic.dest_number t of SOME (_, 7) => true | _ => false)) prop
in
  if has_true andalso has_seven then writeln "T3 mixed via read_fact: ok"
  else error ("T3 failed: " ^ Thm.string_of_thm ctxt (hd thms))
end
\<close>


subsection \<open>Multi-variable instantiation\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thms = test_read_fact_where ctxt
    "conjI[where ?P = \<open>True\<close> and ?Q = \<open>False\<close>]"
  val prop = Thm.prop_of (hd thms)
  val has_true = Term.exists_subterm
    (fn \<^Const_>\<open>True\<close> => true | _ => false) prop
  val has_false = Term.exists_subterm
    (fn \<^Const_>\<open>False\<close> => true | _ => false) prop
in
  if has_true andalso has_false then writeln "T4 multi-var via read_fact: ok"
  else error ("T4 failed: " ^ Thm.string_of_thm ctxt (hd thms))
end
\<close>


subsection \<open>Error: nonexistent variable\<close>

ML \<open>
let
  val ctxt = \<^context>
  val raised = (test_read_fact_where ctxt "spec[where ?nonsense = \<open>True\<close>]"; false)
               handle ERROR _ => true
in
  if raised then writeln "T5 nonexistent var: ok (errored as expected)"
  else error "T5: should have errored for nonexistent variable"
end
\<close>


subsection \<open>Error: unparseable fact reference\<close>

ML \<open>
let
  val ctxt = \<^context>
  val raised = (test_read_fact_where ctxt "[where x = \<open>0\<close>]"; false)
               handle ERROR _ => true
in
  if raised then writeln "T6 no fact name: ok (errored as expected)"
  else error "T6: should have errored for missing fact name"
end
\<close>


subsection \<open>Local assumption via notepad\<close>

text \<open>Tests that local assumptions with [where] work through the read_fact path.\<close>

lemma local_where_test:
  assumes h: "\<forall>x :: nat. P x"
  shows "P (0 :: nat)"
proof -
  ML_val \<open>
    let
      val ctxt = \<^context>
      val thms = test_read_fact_where ctxt "h[where x = \<open>0 :: nat\<close>]"
      val prop = Thm.prop_of (hd thms)
      val has_zero = Term.exists_subterm
        (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in
      if has_zero then writeln "T7 local assumption via read_fact: ok"
      else error ("T7 failed: " ^ Thm.string_of_thm ctxt (hd thms))
    end
  \<close>
  show ?thesis using h by auto
qed

end
