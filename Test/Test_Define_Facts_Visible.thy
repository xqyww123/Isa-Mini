theory Test_Define_Facts_Visible
  imports Minilang.Minilang
begin

lemma "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4"
  ML_val \<open>
let
  val ctxt0 = \<^context>
  val goal = Syntax.read_prop ctxt0 "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4"
  val st0 = Goal.init (Thm.cterm_of ctxt0 goal)
  val s0 = Minilang.INIT ctxt0 st0

  fun check ctxt label =
    writeln (label ^ ": " ^
      (if can (Proof_Context.get_thms ctxt) "double.simps"
       then "double.simps FOUND"
       else "double.simps NOT FOUND"))

  val fixes = [(\<^binding>\<open>double\<close>, SOME "nat \<Rightarrow> nat", NoSyn)]
  val specs : Specification.multi_specs_cmd =
    [((Binding.empty_atts, "double n = n + n"), [], [(\<^binding>\<open>n\<close>, SOME "nat", NoSyn)])]
  val s1 = Minilang.FUN'' fixes specs {metric = [], open_on_fail = false} s0
  val _ = check (Minilang.context_of s1) "After FUN"

  val double_term = Syntax.read_term (Minilang.context_of s1) "double"
  val s2 = Minilang.CHOOSE [double_term] s1
  val _ = check (Minilang.context_of s2) "After CHOOSE"
in () end
\<close>
  by (min_script \<open>
    FUN double :: "nat \<Rightarrow> nat"
      where "double n = n + n"
    CHOOSE double
    END
  \<close>)

end
