theory Iso_Shape
  imports Minilang
begin

axiomatization PP :: "nat \<Rightarrow> bool" and QQ :: "nat \<Rightarrow> bool" where
  ax_ex: "\<exists>z. PP z" and
  ax_pq: "PP n \<Longrightarrow> QQ 7"

ML \<open>
fun show_state st =
  (writeln ("STATE PROP: " ^ (Print_Mode.setmp [] (fn () =>
      Syntax.string_of_term \<^context> (Thm.prop_of st)) ())); Seq.single st)
\<close>

schematic_goal shapeA: "QQ (?x::nat)"
  apply (tactic \<open>show_state\<close>)
  oops

schematic_goal shapeB: "QQ (?x::nat) \<and> PP (?y::nat)"
  apply (tactic \<open>show_state\<close>)
  oops

schematic_goal shapeB2:
  shows s1: "QQ (?x::nat)" and s2: "PP (?y::nat)"
  apply (tactic \<open>show_state\<close>)
  oops

lemma shapeC:
  shows c1: "PP 3" and c2: "QQ 7"
  apply (tactic \<open>show_state\<close>)
  oops

lemma shapeD: "QQ 7"
  apply (tactic \<open>show_state\<close>)
  oops

end
