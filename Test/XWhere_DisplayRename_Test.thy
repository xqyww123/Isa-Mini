theory XWhere_DisplayRename_Test
  imports Minilang.Minilang
begin

declare [[quick_and_dirty]]

section \<open>Tests for xwhere with display-renamed bound variables\<close>

text \<open>
  When a theorem has HOL \<open>\<forall>n. ...\<close> and the proof context already has a free
  variable \<open>n\<close>, @{ML Minilang.deconflict_bound_names} renames the bound
  variable to \<open>n1\<close> (or similar) for display. The agent sees the display name
  and uses it in \<open>[where n1 = ...]\<close>, but the raw theorem still has bound
  name \<open>n\<close>.

  @{ML Minilang_Aux.xwhere} must accept display-renamed names by simulating
  the same renaming and mapping back to raw names.

  Bug: DFDD2C266_1BB5E6E — proof-local function .simps displayed as
  \<open>\<forall>(n1 :: nat). myf n1 = ...\<close> but \<open>[where n1 = ...]\<close> failed with
  "No such variable in theorem".
\<close>


subsection \<open>T1: Display-renamed HOL \<forall> variable\<close>

text \<open>
  Theorem has \<open>\<forall>n. P n\<close> and context has fixed \<open>n\<close>.
  Display shows \<open>\<forall>n1. P n1\<close>. Using \<open>n1\<close> in where must work.
\<close>

lemma forall_n: \<open>\<forall>n :: nat. P n\<close> for P sorry

notepad
begin
  fix n :: nat

  text \<open>Verify that deconflict_bound_names renames n \<rightarrow> n1 here.\<close>
  ML_val \<open>
    let val prop = Thm.prop_of @{thm forall_n}
        val display = Minilang.deconflict_bound_names \<^context> prop
        val display_str = Syntax.string_of_term
              (Config.put Printer.show_question_marks true \<^context>) display
    in if String.isSubstring "n1" display_str
       then writeln ("T1a deconflict renames n\<rightarrow>n1: ok (" ^ display_str ^ ")")
       else error ("T1a: expected n1 in display, got: " ^ display_str)
    end
  \<close>

  text \<open>xwhere with the display-renamed name n1 must succeed.\<close>
  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n1", 0), Position.none), ("nat", "0 :: nat"))] [] @{thm forall_n}
        val prop = Thm.prop_of thm
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in if has_zero then writeln "T1b xwhere display-renamed name: ok"
       else error ("T1b failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>

  text \<open>xwhere with the original raw name n must also still work.\<close>
  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n", 0), Position.none), ("nat", "0 :: nat"))] [] @{thm forall_n}
        val prop = Thm.prop_of thm
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in if has_zero then writeln "T1c xwhere original name: ok"
       else error ("T1c failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T2: Schematic takes priority over display-renamed HOL \<forall>\<close>

text \<open>
  If both a schematic \<open>?n\<close> and a HOL \<open>\<forall>n\<close> exist, schematic wins.
\<close>

lemma mixed_svar: \<open>Q \<Longrightarrow> \<forall>n :: nat. P n\<close> for Q P sorry

notepad
begin
  fix n :: nat

  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("Q", 0), Position.none), ("prop", "True"))] [] @{thm mixed_svar}
        val has_true = Term.exists_subterm
          (fn \<^Const_>\<open>True\<close> => true | _ => false) (Thm.prop_of thm)
    in if has_true then writeln "T2 schematic priority: ok"
       else error ("T2 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T3: Multiple HOL \<forall> variables, some renamed\<close>

lemma forall_nm: \<open>\<forall>(n :: nat) (m :: nat). P n m\<close> for P sorry

notepad
begin
  fix n :: nat

  text \<open>n is renamed to n1 in display, m stays as m.\<close>
  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n1", 0), Position.none), ("nat", "0 :: nat")),
               ((("m", 0), Position.none), ("nat", "1 :: nat"))] [] @{thm forall_nm}
        val prop = Thm.prop_of thm
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
        val has_one = Term.exists_subterm
          (fn t => (case try HOLogic.dest_number t of SOME (_, 1) => true | _ => false)) prop
    in if has_zero andalso has_one then writeln "T3 multi-var rename: ok"
       else error ("T3 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T4: No rename when context has no conflicting free\<close>

notepad
begin
  text \<open>No fixed n \<rightarrow> no rename. Using original name n must work.\<close>
  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n", 0), Position.none), ("nat", "0 :: nat"))] [] @{thm forall_n}
        val prop = Thm.prop_of thm
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in if has_zero then writeln "T4 no-rename baseline: ok"
       else error ("T4 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T5: Proof-local fun simps (the original bug pattern)\<close>

text \<open>
  Simulates the original bug: fun defined at theory level, proof context
  fixes n, agent uses the display-renamed variable name from retrieval.
\<close>

fun myf :: "nat \<Rightarrow> nat" where
  "myf n = n + 1"

notepad
begin
  fix n :: nat

  text \<open>myf.simps has schematic ?n. Display still shows ?n (not renamed).
  But test that xwhere accepts n anyway (tier 3: original HOL \<forall> fallback
  doesn't apply here since .simps is schematic, but standard where handles it).\<close>
  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n", 0), Position.none), ("nat", "0 :: nat"))] [] @{thm myf.simps}
        val prop = Thm.prop_of thm
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in if has_zero then writeln "T5 theory-level simps: ok"
       else error ("T5 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


section \<open>Corner cases\<close>

subsection \<open>T6: Mixed schematic + display-renamed HOL \<forall> in one call\<close>

text \<open>Schematic \<open>?Q\<close> + display-renamed \<open>n1\<close> (raw \<open>n\<close>) in one xwhere call.\<close>

notepad
begin
  fix n :: nat

  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("Q", 0), Position.none), ("prop", "True")),
               ((("n1", 0), Position.none), ("nat", "0 :: nat"))]
              [] @{thm mixed_svar}
        val prop = Thm.prop_of thm
        val has_true = Term.exists_subterm
          (fn \<^Const_>\<open>True\<close> => true | _ => false) prop
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in if has_true andalso has_zero
       then writeln "T6 mixed schematic + display-renamed: ok"
       else error ("T6 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T7: Mixed schematic + original HOL \<forall> in one call\<close>

notepad
begin
  text \<open>No conflicting free \<rightarrow> display names = raw names.
        Schematic \<open>?Q\<close> + original \<open>n\<close>.\<close>
  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("Q", 0), Position.none), ("prop", "True")),
               ((("n", 0), Position.none), ("nat", "0 :: nat"))]
              [] @{thm mixed_svar}
        val prop = Thm.prop_of thm
        val has_true = Term.exists_subterm
          (fn \<^Const_>\<open>True\<close> => true | _ => false) prop
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in if has_true andalso has_zero
       then writeln "T7 mixed schematic + original: ok"
       else error ("T7 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T8: All HOL \<forall> vars renamed (both n and m clash)\<close>

notepad
begin
  fix n m :: nat

  ML_val \<open>
    let val display = Minilang.deconflict_bound_names \<^context>
              (Thm.prop_of @{thm forall_nm})
        val s = Syntax.string_of_term
              (Config.put Printer.show_question_marks true \<^context>) display
    in writeln ("T8a display: " ^ s) end
  \<close>

  ML_val \<open>
    let val ctxt = \<^context>
        val display = Minilang.deconflict_bound_names ctxt
              (Thm.prop_of @{thm forall_nm})
        val s = Syntax.string_of_term
              (Config.put Printer.show_question_marks true ctxt) display
        (* Extract the display names from the string *)
        val n_name = if String.isSubstring "n1" s then "n1" else "na"
        val m_name = if String.isSubstring "m1" s then "m1" else
                     if String.isSubstring "ma" s then "ma" else "m1"
        val thm = Minilang_Aux.xwhere ctxt
              [((( n_name, 0), Position.none), ("nat", "0 :: nat")),
               (((m_name, 0), Position.none), ("nat", "1 :: nat"))]
              [] @{thm forall_nm}
        val prop = Thm.prop_of thm
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
        val has_one = Term.exists_subterm
          (fn t => (case try HOLogic.dest_number t of SOME (_, 1) => true | _ => false)) prop
    in if has_zero andalso has_one
       then writeln ("T8b all-renamed (" ^ n_name ^ "," ^ m_name ^ "): ok")
       else error ("T8b failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T9: Nonexistent variable name \<rightarrow> error\<close>

notepad
begin
  fix n :: nat

  ML_val \<open>
    let val raised = (Minilang_Aux.xwhere \<^context>
              [((("bogus", 0), Position.none), ("nat", "0 :: nat"))]
              [] @{thm forall_n}; false)
              handle ERROR _ => true
    in if raised then writeln "T9 nonexistent var: ok (errored)"
       else error "T9: should have errored for nonexistent variable"
    end
  \<close>
end


subsection \<open>T10: HOL \<forall> nested inside implication\<close>

text \<open>\<open>A \<longrightarrow> \<forall>n. P n\<close> — the \<forall> is inside an implication conclusion.\<close>

lemma impl_forall: \<open>A \<longrightarrow> (\<forall>n :: nat. P n)\<close> for A P sorry

notepad
begin
  fix n :: nat

  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n1", 0), Position.none), ("nat", "0 :: nat"))]
              [] @{thm impl_forall}
        val prop = Thm.prop_of thm
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in if has_zero then writeln "T10 forall inside implication: ok"
       else error ("T10 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T11: Pure.all wrapping HOL \<forall>\<close>

text \<open>\<open>\<And>x. \<forall>n. P x n\<close> — Pure quantifier wrapping HOL quantifier.\<close>

lemma pure_hol: \<open>\<And>x :: nat. \<forall>n :: nat. P x n\<close> for P sorry

notepad
begin
  fix n :: nat

  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n1", 0), Position.none), ("nat", "0 :: nat"))]
              [] @{thm pure_hol}
        val prop = Thm.prop_of thm
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) prop
    in if has_zero then writeln "T11 Pure.all wrapping HOL.All: ok"
       else error ("T11 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T12: Empty instantiation list (no-op)\<close>

notepad
begin
  fix n :: nat

  ML_val \<open>
    let val ctxt = \<^context>
        val thm0 = @{thm forall_n}
        val thm1 = Minilang_Aux.xwhere ctxt [] [] thm0
    in if Thm.prop_of thm0 aconv Thm.prop_of thm1
       then writeln "T12 empty instantiation: ok (no-op)"
       else error "T12: empty inst should be no-op"
    end
  \<close>
end


subsection \<open>T13: Chain of multiple implications before \<forall>\<close>

text \<open>\<open>A \<longrightarrow> B \<longrightarrow> \<forall>n. P n\<close> — foralls must look past multiple \<longrightarrow>.\<close>

lemma deep_impl: \<open>A \<longrightarrow> B \<longrightarrow> (\<forall>n :: nat. P n)\<close> for A B P sorry

notepad
begin
  fix n :: nat

  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n1", 0), Position.none), ("nat", "0 :: nat"))]
              [] @{thm deep_impl}
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) (Thm.prop_of thm)
    in if has_zero then writeln "T13 deep implication chain: ok"
       else error ("T13 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T14: Rename to \<open>na\<close> (not \<open>n1\<close>) when \<open>n1\<close> is also taken\<close>

notepad
begin
  fix n n1 :: nat

  ML_val \<open>
    let val display = Minilang.deconflict_bound_names \<^context>
              (Thm.prop_of @{thm forall_n})
        val s = Syntax.string_of_term
              (Config.put Printer.show_question_marks true \<^context>) display
    in writeln ("T14a display with n,n1 taken: " ^ s) end
  \<close>

  ML_val \<open>
    let val ctxt = \<^context>
        (* n and n1 are both taken, so deconflict should pick something else *)
        val display = Minilang.deconflict_bound_names ctxt
              (Thm.prop_of @{thm forall_n})
        val s = Syntax.string_of_term
              (Config.put Printer.show_question_marks true ctxt) display
        (* Extract whatever name deconflict chose *)
        val display_names = map fst (let
              fun foralls (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = foralls X
                | foralls (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, T, X)) = (name, T) :: foralls X
                | foralls _ = []
              in foralls display end)
        val dname = hd display_names
        val thm = Minilang_Aux.xwhere ctxt
              [(((dname, 0), Position.none), ("nat", "0 :: nat"))]
              [] @{thm forall_n}
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) (Thm.prop_of thm)
    in if has_zero
       then writeln ("T14b rename to " ^ dname ^ ": ok")
       else error ("T14b failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end


subsection \<open>T15: Theorem with premises (Pure.imp) wrapping HOL \<forall>\<close>

text \<open>\<open>A \<Longrightarrow> \<forall>n. P n\<close> — Pure implication, not HOL.\<close>

lemma pure_imp_forall: \<open>A \<Longrightarrow> \<forall>n :: nat. P n\<close> for A P sorry

notepad
begin
  fix n :: nat

  ML_val \<open>
    let val ctxt = \<^context>
        val thm = Minilang_Aux.xwhere ctxt
              [((("n1", 0), Position.none), ("nat", "0 :: nat"))]
              [] @{thm pure_imp_forall}
        val has_zero = Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) (Thm.prop_of thm)
    in if has_zero then writeln "T15 Pure.imp + HOL.All: ok"
       else error ("T15 failed: " ^ Thm.string_of_thm ctxt thm)
    end
  \<close>
end

end
