theory Where_Attribute_Test
  imports Minilang.Minilang HOL.Int
begin

section \<open>Tests for the Minilang \<open>where\<close> attribute\<close>

text \<open>
  Regression and corner-case tests for @{ML Minilang_Aux.xwhere}, which backs
  the Minilang override of where (see \<^file>\<open>../Minilang.thy\<close>).
  The override extends the stock where with the ability to
  instantiate HOL.All (\<open>\<forall>\<close>) bound variables in the conclusion in addition to
  ordinary schematic variables.

  Each test states the input shape, the expected post-instantiation shape,
  and uses ML-level assertions on @{ML Thm.prop_of} so that failures are
  loud rather than silent.
\<close>

ML \<open>
(* Helper: assert that a thm contains a particular Free, and contains no
   schematic var with the given name. *)
fun assert_free_inst label var_name T thm =
  let
    val prop = Thm.prop_of thm
    val has_free = Term.exists_subterm
                     (fn Free (n, T') => n = var_name andalso T' = T | _ => false) prop
    val has_var = Term.exists_subterm
                     (fn Var ((n, _), _) => n = var_name | _ => false) prop
  in
    if has_free andalso not has_var then writeln (label ^ ": ok")
    else error (label ^ ": expected Free \"" ^ var_name ^ "\" present and no Var\n  " ^
                 Thm.string_of_thm \<^context> thm)
  end

(* Helper: assert that a thm contains a particular schematic var (by name). *)
fun assert_var_present label var_name thm =
  let
    val has_var = Term.exists_subterm
                     (fn Var ((n, _), _) => n = var_name | _ => false) (Thm.prop_of thm)
  in
    if has_var then writeln (label ^ ": ok")
    else error (label ^ ": expected schematic ?" ^ var_name ^ " still present\n  " ^
                 Thm.string_of_thm \<^context> thm)
  end
\<close>


subsection \<open>Regression: free variable on RHS with same name as schematic LHS\<close>

text \<open>
  Previously broken: @{ML Minilang_Aux.xwhere} compared the textual content
  of the first RHS token to the LHS schematic name and silently dropped the
  instantiation when they matched. The user-reported failure was
  \<open>int_le_induct[where ?k = \<open>k\<close>]\<close> in a context with \<open>fix k :: int\<close>.
\<close>

notepad
begin
  fix k :: int

  text \<open>Cartouche RHS, same name.\<close>
  ML_val \<open>
    assert_free_inst "A1 cartouche-same-name" "k" \<^typ>\<open>int\<close>
      @{thm int_le_induct[where ?k = \<open>k\<close>]}
  \<close>

  text \<open>Bare identifier RHS, same name.\<close>
  ML_val \<open>
    assert_free_inst "A2 bare-same-name" "k" \<^typ>\<open>int\<close>
      @{thm int_le_induct[where ?k = k]}
  \<close>

  text \<open>The other schematics (\<open>?i\<close>, \<open>?P\<close>) must remain untouched.\<close>
  ML_val \<open>
    let val thm = @{thm int_le_induct[where ?k = \<open>k\<close>]}
    in assert_var_present "A3 ?i preserved" "i" thm;
       assert_var_present "A3 ?P preserved" "P" thm
    end
  \<close>
end


subsection \<open>Same-name on a tiny isolated rule (no \<open>int_le_induct\<close> noise)\<close>

lemma tiny_rule: \<open>P k \<Longrightarrow> Q k \<Longrightarrow> R k\<close> for P Q R k sorry

notepad
begin
  fix k :: nat

  ML_val \<open>
    assert_free_inst "B1 tiny same-name" "k" \<^typ>\<open>nat\<close>
      @{thm tiny_rule[where ?k = \<open>k\<close>]}
  \<close>

  ML_val \<open>
    assert_free_inst "B2 tiny different-name" "m" \<^typ>\<open>nat\<close>
      @{thm tiny_rule[where ?k = \<open>m :: nat\<close> for m]}
  \<close>
end


subsection \<open>Identity instantiation \<open>?x = ?x\<close> (the case the old filter aimed at)\<close>

text \<open>
  Should be a no-op rather than an error. Any change to the theorem prop
  fails the assertion.
\<close>

ML \<open>
let
  val thm0 = @{thm spec}
  val thm1 = @{thm spec[where ?x = \<open>?x\<close>]}
in
  if Thm.prop_of thm0 aconv Thm.prop_of thm1
  then writeln "C1 identity ?x = ?x: ok (no-op)"
  else error ("C1 identity changed the theorem:\n  before: " ^
              Thm.string_of_thm \<^context> thm0 ^ "\n  after:  " ^
              Thm.string_of_thm \<^context> thm1)
end
\<close>


subsection \<open>Multi-variable instantiation in one call\<close>

notepad
begin
  fix k i :: int

  ML_val \<open>
    let val thm = @{thm int_le_induct[where ?k = \<open>k\<close> and ?i = \<open>i\<close>]} in
      assert_free_inst "D1 ?k=k" "k" \<^typ>\<open>int\<close> thm;
      assert_free_inst "D1 ?i=i" "i" \<^typ>\<open>int\<close> thm;
      assert_var_present "D1 ?P preserved" "P" thm
    end
  \<close>
end


subsection \<open>Higher-order instantiation: \<open>?P\<close> with a \<open>\<lambda>\<close>-term\<close>

notepad
begin
  fix k :: int

  text \<open>Instantiate the predicate variable with \<open>\<lambda>x. 0 \<le> x\<close>.\<close>
  ML_val \<open>
    let
      val thm = @{thm int_le_induct[where ?P = \<open>\<lambda>x. 0 \<le> x\<close>]}
      val prop = Thm.prop_of thm
      val has_zero_le =
        Term.exists_subterm
          (fn Const (\<^const_name>\<open>less_eq\<close>, _) $ Const (\<^const_name>\<open>Groups.zero\<close>, _) $ _ => true
            | _ => false) prop
    in
      if has_zero_le then writeln "E1 lambda predicate: ok"
      else error ("E1: expected 0 \<le> _ subterm\n  " ^ Thm.string_of_thm \<^context> thm)
    end
  \<close>
end


subsection \<open>Complex term RHS (arithmetic, free vars from context)\<close>

notepad
begin
  fix k :: int and m :: int

  ML_val \<open>
    let val thm = @{thm int_le_induct[where ?k = \<open>k + m\<close>]}
    in
      \<^assert> (Term.exists_subterm
                  (fn Const (\<^const_name>\<open>plus\<close>, _) $ _ $ _ => true | _ => false)
                  (Thm.prop_of thm));
      writeln "F1 arithmetic RHS: ok"
    end
  \<close>
end


subsection \<open>\<open>for\<close>-fixes clause\<close>

text \<open>RHS uses \<open>f\<close> which is fixed in the attribute via \<open>for f\<close>.\<close>

ML_val \<open>
  let
    val thm = @{thm int_le_induct[where ?P = \<open>\<lambda>x. f x \<le> 0\<close> for f]}
    val has_f =
      Term.exists_subterm (fn Free ("f", _) => true | _ => false) (Thm.prop_of thm)
  in
    if has_f then writeln "G1 for-fixes: ok"
    else error ("G1: expected Free \"f\" present\n  " ^ Thm.string_of_thm \<^context> thm)
  end
\<close>


subsection \<open>HOL.All-bound variable instantiation (the ELSE branch of \<open>xwhere\<close>)\<close>

text \<open>
  When the LHS name matches a HOL.All quantifier in the conclusion (rather than
  an existing schematic var), Minilang's \<open>where\<close> first lifts that quantifier
  to a schematic via @{ML Minilang_Aux.inst_hol_alls}, then instantiates.
  Stock Isabelle \<open>where\<close> would error here.
\<close>

lemma forall_thm: \<open>\<forall>x :: nat. P x \<longrightarrow> P x\<close> for P sorry

notepad
begin
  ML_val \<open>
    let
      val thm = @{thm forall_thm[where x = \<open>0 :: nat\<close>]}
      val has_zero =
        Term.exists_subterm
          (fn Const (\<^const_name>\<open>Groups.zero\<close>, _) => true | _ => false) (Thm.prop_of thm)
    in
      if has_zero then writeln "H1 HOL.All branch: ok"
      else error ("H1: expected 0 in instantiated thm\n  " ^ Thm.string_of_thm \<^context> thm)
    end
  \<close>
end


subsection \<open>Mixed: schematic + HOL.All in one call\<close>

lemma mixed_thm: \<open>R \<Longrightarrow> \<forall>x :: nat. P x\<close> for R P sorry

notepad
begin
  ML_val \<open>
    let
      val thm = @{thm mixed_thm[where ?R = \<open>True\<close> and x = \<open>7 :: nat\<close>]}
      val prop = Thm.prop_of thm
      val has_true =
        Term.exists_subterm (fn \<^Const_>\<open>True\<close> => true | _ => false) prop
      val has_seven =
        Term.exists_subterm
          (fn t => (case try HOLogic.dest_number t of SOME (_, 7) => true | _ => false)) prop
    in
      if has_true andalso has_seven then writeln "I1 mixed: ok"
      else error ("I1: expected True and 7 in thm\n  " ^ Thm.string_of_thm \<^context> thm)
    end
  \<close>
end


subsection \<open>Error cases\<close>

text \<open>Instantiating a non-existent variable name should fail.\<close>

ML \<open>
let
  val good = (Attrib.thm \<^context> @{binding spec}; true) handle ERROR _ => false
  val _ = if good then () else error "sanity check: spec should be readable"
  val raised =
    (let val _ = @{thm spec[where ?nonsense = \<open>True\<close>]} in false end)
    handle _ => true
in
  if raised then writeln "J1 non-existent var: ok (errored as expected)"
  else error "J1: instantiation of non-existent var should have errored"
end
\<close>

text \<open>Type mismatch should fail.\<close>

ML \<open>
let
  val raised =
    (let val _ = @{thm spec[where ?x = \<open>True\<close>]} in false end)
    handle _ => true
in
  if raised then writeln "J2 type mismatch: ok (errored as expected)"
  else error "J2: type-mismatched instantiation should have errored"
end
\<close>


subsection \<open>Parity with stock Isabelle: cases the stock \<open>where\<close> already handles\<close>

text \<open>
  When all instantiations target ordinary schematic vars, the Minilang
  override should produce a thm with the same prop as a hand-built reference.
\<close>

ML \<open>
let
  val ref_thm = Drule.infer_instantiate \<^context>
                  [((("x", 0), \<^typ>\<open>nat\<close>), \<^cterm>\<open>0 :: nat\<close>)] @{thm spec}
  val mini_thm = @{thm spec[where ?x = \<open>0 :: nat\<close>]}
in
  if Thm.prop_of ref_thm aconv Thm.prop_of mini_thm
  then writeln "K1 parity vs infer_instantiate: ok"
  else error ("K1 parity mismatch:\n  reference: " ^ Thm.string_of_thm \<^context> ref_thm ^
              "\n  minilang:  " ^ Thm.string_of_thm \<^context> mini_thm)
end
\<close>

end
