theory Have_Schematic_Vars_Test
  imports Minilang.Minilang HOL.Real
begin

text \<open>
  Regression coverage for the \<open>TERM ?v\<close> markers that Isar's \<open>generic_goal\<close>
  prepends to a goal carrying schematic variables (one \<open>Pure.term\<close> conjunct per
  variable, via \<open>implicit_vars\<close>, discharged immediately by \<open>refine_terms\<close> but
  surviving in the goal's protected conclusion).

  \<open>gen_HAVE'\<close> slices those conjuncts against \<open>shows\<close> in two places, and both must
  drop the markers first (\<open>is_term_marker\<close>), exactly as Isar's own \<open>generic_qed\<close>
  does via the \<open>tl\<close> on \<open>conclude_goal\<close>:

    \<^item> \<open>preruns\<close>, when the HAVE is OPENED;
    \<^item> \<open>CB\<close>, the block-closing continuation.

  \<open>unflat\<close> raises \<open>UnequalLengths\<close> only when the value list OUTRUNS the shape
  list (its \<open>chop\<close> silently truncates otherwise), so the two sites failed at
  different arities: one schematic variable slipped past \<open>preruns\<close> and crashed at
  block CLOSE, two or more crashed at block OPEN.

  These probes live at the Minilang level on purpose.  The AoA agent layer
  rejects schematic HAVE statements before a block can ever close
  (\<open>reject_schematic_goal\<close> in Agent/agent.ML), so the AoA model tests cannot
  exercise \<open>CB\<close> at all.
\<close>

subsection \<open>Opening and closing a HAVE, by number of schematic variables\<close>

text \<open>No schematic variable: the baseline that always worked.\<close>
lemma have_schematic_none: "True"
  by (min_script \<open>
    HAVE h: "(1::nat) = 1"  SORRY
    END
  \<close>)

text \<open>One schematic variable: \<open>preruns\<close> survived via \<open>chop\<close>, \<open>CB\<close> raised.\<close>
lemma have_schematic_one: "True"
  by (min_script \<open>
    HAVE h: "(?x::real) = ?x"  SORRY
    END
  \<close>)

text \<open>Two schematic variables: \<open>preruns\<close> itself overflowed.\<close>
lemma have_schematic_two: "True"
  by (min_script \<open>
    HAVE h: "?a + ?b = ?b + (?a::nat)"  SORRY
    END
  \<close>)

text \<open>The statement an AoA worker actually posed when this was discovered.\<close>
lemma have_schematic_wild: "True"
  by (min_script \<open>
    HAVE abs_max_identity: "\<bar>?x::real\<bar> = max ?x 0 + max (- ?x) 0"  SORRY
    END
  \<close>)

subsection \<open>The fact a closed schematic HAVE binds\<close>

text \<open>
  Self-checking: the HAVE is proved for real and its block is CLOSED, then \<open>h\<close>
  is used to discharge the enclosing goal.  Were \<open>CB\<close> to keep the marker, \<open>h\<close>
  would be bound to the vacuous \<open>TERM ?x\<close> and \<open>simp only: h\<close> could not close
  anything -- so this pins the marker filtering, not merely the absence of a
  crash.
\<close>
lemma have_schematic_binds_real_prop:
  "\<bar>(y::real)\<bar> = max y 0 + max (- y) 0"
  by (min_script \<open>
    HAVE h: "\<bar>?x::real\<bar> = max ?x 0 + max (- ?x) 0"
      APPLY (simp add: abs_real_def max_def)
    END
    APPLY (simp only: h)
    END
  \<close>)

end
