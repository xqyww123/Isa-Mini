theory Scratch_SchematicProbe_OneCase
  imports Minilang.Minilang
begin

text \<open>
  Exactly-one-case CASE_SPLIT / INDUCT.  `unit` has a single constructor,
  so `cases u` / `induct u` produce exactly one case.
\<close>

axiomatization SS :: "nat \<Rightarrow> bool" where
  ss7: "SS (7::nat)"

section \<open>Controls: one case, NO schematic anywhere\<close>

lemma ctl_cs: "SS 7 \<and> (u::unit) = ()"
  apply (min_script \<open>CASE_SPLIT u PRINT SORRY_END_ALL\<close>)
  done

lemma ctl_ind: "SS 7 \<and> (u::unit) = ()"
  apply (min_script \<open>INDUCT u PRINT SORRY_END_ALL\<close>)
  done

section \<open>One case, schematic present, sub-proof does NOT touch ?x\<close>

schematic_goal cs_untouched: "SS ?x \<and> (u::unit) = ()"
  apply (min_script \<open>CASE_SPLIT u PRINT SORRY_END_ALL\<close>)
  oops

schematic_goal ind_untouched: "SS ?x \<and> (u::unit) = ()"
  apply (min_script \<open>INDUCT u PRINT SORRY_END_ALL\<close>)
  oops

section \<open>One case whose sub-proof INSTANTIATES the schematic\<close>

text \<open>Controls first: identical script, no schematic (?x replaced by 7).\<close>

lemma ctl_cs_t: "(u::unit) = () \<Longrightarrow> SS 7"
  apply (min_script \<open>CASE_SPLIT u RULE ss7 END\<close>)
  done

lemma ctl_ind_t: "(u::unit) = () \<Longrightarrow> SS 7"
  apply (min_script \<open>INDUCT u RULE ss7 END\<close>)
  done

text \<open>Now with ?x: `RULE ss7` unifies SS ?x with SS 7, pinning ?x := 7
      inside the case.\<close>

schematic_goal cs_touched: "(u::unit) = () \<Longrightarrow> SS ?x"
  apply (min_script \<open>CASE_SPLIT u RULE ss7 END\<close>)
  oops

schematic_goal ind_touched: "(u::unit) = () \<Longrightarrow> SS ?x"
  apply (min_script \<open>INDUCT u RULE ss7 END\<close>)
  oops

text \<open>And the untouched counterpart in the same shape, for comparison.\<close>

schematic_goal cs_untouched2: "(u::unit) = () \<Longrightarrow> SS ?x"
  apply (min_script \<open>CASE_SPLIT u PRINT SORRY_END_ALL\<close>)
  oops

schematic_goal ind_untouched2: "(u::unit) = () \<Longrightarrow> SS ?x"
  apply (min_script \<open>INDUCT u PRINT SORRY_END_ALL\<close>)
  oops

section \<open>TWO cases, for contrast (bool has two constructors)\<close>

lemma ctl_cs2: "(b::bool) = b \<Longrightarrow> SS 7"
  apply (min_script \<open>CASE_SPLIT b PRINT SORRY_END_ALL\<close>)
  done

schematic_goal cs2_untouched: "(b::bool) = b \<Longrightarrow> SS ?x"
  apply (min_script \<open>CASE_SPLIT b PRINT SORRY_END_ALL\<close>)
  oops

lemma ctl_cs2_t: "(b::bool) = b \<Longrightarrow> SS 7"
  apply (min_script \<open>CASE_SPLIT b RULE ss7 NEXT RULE ss7 END\<close>)
  done

schematic_goal cs2_touched: "(b::bool) = b \<Longrightarrow> SS ?x"
  apply (min_script \<open>CASE_SPLIT b RULE ss7 NEXT RULE ss7 END\<close>)
  oops

end
