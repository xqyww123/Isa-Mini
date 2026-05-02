theory xOF_Skip_Test
  imports Minilang.Minilang
begin

declare [[quick_and_dirty]]

section \<open>Tests for xOF with NONE (skip) support\<close>

subsection \<open>Basic: skip first premise, discharge second\<close>

text \<open>conjI: ?P \<Longrightarrow> ?Q \<Longrightarrow> ?P \<and> ?Q.
  Skip ?P, discharge ?Q with TrueI. Result: ?P \<Longrightarrow> ?P \<and> True.\<close>
ML \<open>
let
  val ctxt = \<^context>
  val result = Minilang_Aux.xOF false ctxt [NONE, SOME @{thm TrueI}] @{thm conjI}
  val _ = writeln ("T1 result: " ^ Thm.string_of_thm ctxt result)
  val nprems = Thm.nprems_of result
  val has_true = Term.exists_subterm
    (fn \<^Const_>\<open>True\<close> => true | _ => false) (Thm.prop_of result)
in
  if nprems = 1 andalso has_true
  then writeln "T1 skip first, discharge second: ok"
  else error ("T1 failed: nprems=" ^ string_of_int nprems)
end
\<close>


subsection \<open>Skip second premise, discharge first\<close>

text \<open>conjI: ?P \<Longrightarrow> ?Q \<Longrightarrow> ?P \<and> ?Q.
  Discharge ?P with TrueI, skip ?Q. Result: ?Q \<Longrightarrow> True \<and> ?Q.\<close>
ML \<open>
let
  val ctxt = \<^context>
  val result = Minilang_Aux.xOF false ctxt [SOME @{thm TrueI}, NONE] @{thm conjI}
  val _ = writeln ("T2 result: " ^ Thm.string_of_thm ctxt result)
  val nprems = Thm.nprems_of result
  val has_true = Term.exists_subterm
    (fn \<^Const_>\<open>True\<close> => true | _ => false) (Thm.prop_of result)
in
  if nprems = 1 andalso has_true
  then writeln "T2 skip second, discharge first: ok"
  else error ("T2 failed: nprems=" ^ string_of_int nprems)
end
\<close>


subsection \<open>Skip middle premise\<close>

lemma three_prems: "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> A \<and> B \<and> C" for A B C by auto

ML \<open>
let
  val ctxt = \<^context>
  val result = Minilang_Aux.xOF false ctxt
    [SOME @{thm TrueI}, NONE, SOME @{thm TrueI}] @{thm three_prems}
  val _ = writeln ("T3 result: " ^ Thm.string_of_thm ctxt result)
  val nprems = Thm.nprems_of result
in
  if nprems = 1
  then writeln "T3 skip middle: ok"
  else error ("T3 failed: nprems=" ^ string_of_int nprems)
end
\<close>


subsection \<open>All NONE = identity\<close>

ML \<open>
let
  val ctxt = \<^context>
  val result = Minilang_Aux.xOF false ctxt [NONE, NONE] @{thm conjI}
  val _ = writeln ("T4 result: " ^ Thm.string_of_thm ctxt result)
  val nprems = Thm.nprems_of result
in
  if nprems = 2
  then writeln "T4 all NONE = identity: ok"
  else error ("T4 failed: nprems=" ^ string_of_int nprems)
end
\<close>


subsection \<open>No NONE = same as before\<close>

ML \<open>
let
  val ctxt = \<^context>
  val result = Minilang_Aux.xOF false ctxt
    [SOME @{thm TrueI}, SOME @{thm TrueI}] @{thm conjI}
  val _ = writeln ("T5 result: " ^ Thm.string_of_thm ctxt result)
  val nprems = Thm.nprems_of result
  val prop = Thm.prop_of result
  val is_true_and_true = (prop aconv \<^prop>\<open>True \<and> True\<close>)
in
  if nprems = 0 andalso is_true_and_true
  then writeln "T5 no NONE = original behavior: ok"
  else error ("T5 failed: " ^ Thm.string_of_thm ctxt result)
end
\<close>


subsection \<open>Rulification with skip: HOL \<forall>/\<longrightarrow> premises\<close>

text \<open>Rule with HOL connectives that need rulification.
  \<forall>x. P x \<longrightarrow> Q x \<longrightarrow> P x \<and> Q x.
  Skip first, discharge second with TrueI.\<close>

lemma hol_prems: "\<forall>x :: nat. P x \<longrightarrow> Q x \<longrightarrow> P x \<and> Q x" for P Q by auto

ML \<open>
let
  val ctxt = \<^context>
  val result = Minilang_Aux.xOF false ctxt [NONE, SOME @{thm TrueI}] @{thm hol_prems}
  val _ = writeln ("T6 result: " ^ Thm.string_of_thm ctxt result)
  val nprems = Thm.nprems_of result
in
  if nprems = 0
  then writeln "T6 rulification with skip: ok"
  else error ("T6 failed: nprems=" ^ string_of_int nprems)
end
\<close>


subsection \<open>OF attribute with underscore\<close>

text \<open>Test the [OF ...] attribute parser with \<open>_\<close> for skip.\<close>

lemma of_attr_test:
  assumes h: "True"
  shows "True \<and> True"
  using conjI[OF h _] h by auto

text \<open>Test via read_fact path (same as agent pipeline).\<close>
ML \<open>
fun test_read_fact ctxt src =
  let
    val keywords = Thy_Header.get_keywords \<^theory>\<open>Pure\<close>
    val symbols = Input.source_explode (Input.string src)
    val toks = Token.tokenize keywords {strict = true} symbols
               |> filter Token.is_proper
  in case Scan.read Token.stopper Parse.thm toks of
       SOME fact => Attrib.eval_thms ctxt [fact]
     | NONE => error ("Cannot parse \"" ^ src ^ "\" as a fact reference")
  end
\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thms = test_read_fact ctxt "conjI[OF TrueI _]"
  val thm = hd thms
  val _ = writeln ("T7 result: " ^ Thm.string_of_thm ctxt thm)
  val nprems = Thm.nprems_of thm
in
  if nprems = 1
  then writeln "T7 OF attribute with _: ok"
  else error ("T7 failed: nprems=" ^ string_of_int nprems)
end
\<close>


subsection \<open>OF attribute: all underscores\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thms = test_read_fact ctxt "conjI[OF _ _]"
  val thm = hd thms
  val _ = writeln ("T8 result: " ^ Thm.string_of_thm ctxt thm)
  val nprems = Thm.nprems_of thm
in
  if nprems = 2
  then writeln "T8 OF attribute all _: ok"
  else error ("T8 failed: nprems=" ^ string_of_int nprems)
end
\<close>


subsection \<open>Combining [where ...] and [OF ...]\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thms = test_read_fact ctxt "spec[where ?x = \<open>0 :: nat\<close>, OF _]"
  val thm = hd thms
  val _ = writeln ("T9 result: " ^ Thm.string_of_thm ctxt thm)
  val has_zero = Term.exists_subterm
    (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) (Thm.prop_of thm)
  val nprems = Thm.nprems_of thm
in
  if has_zero andalso nprems = 1
  then writeln "T9 where + OF combined: ok"
  else error ("T9 failed: " ^ Thm.string_of_thm ctxt thm)
end
\<close>

end
