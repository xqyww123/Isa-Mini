theory My_Object_Logic_Wraps_Test
  imports Minilang.Minilang
begin

(* MY_OBJECT_LOGIC_PLAN.md section 8-5 (wraps coverage) and 8-8 (strict site
   sample).  `wraps' (proof.ML) is reachable only through INDUCT with a dirty
   insertion fact; in the default configuration the regression suite never
   reaches it, and a Trueprop-headed dirty fact takes the short circuit, so the
   census cannot see it either.  The fact here is META-shaped, forcing the
   wraps call off the short circuit: the census MUST count it. *)

axiomatization PP QQ :: "nat \<Rightarrow> bool"

declare [[induct_auto_insert_facts]]

ML \<open>My_Object_Logic.reset_census ()\<close>

lemma
  assumes step: "\<And>k::nat. k < n \<Longrightarrow> PP k"
  shows "QQ (n::nat)"
  apply (min_script \<open>INDUCT n SORRY SORRY\<close>)
  done

ML \<open>
val {intact, repaired, fallback} = My_Object_Logic.census ();
val _ = writeln ("wraps census: intact=" ^ Int.toString intact ^
                 " repaired=" ^ Int.toString repaired ^
                 " fallback=" ^ Int.toString fallback);
val _ =
  if fallback = 0 andalso intact + repaired > 0
  then writeln "WRAPS COVERAGE: OK (site counted, no fallback)"
  else error "WRAPS COVERAGE: site not counted or fallback hit";
\<close>

(* 8-8: an incomplete (not fully atomizable) dirty fact -- {strict = true}
   at the wraps site must raise "Fail to atomize", and min_script must present
   it as a readable command failure, not kill the session.
   EXPECTED ERROR on the apply below (this is the assertion, not a defect):
     exception CTERM raised (my_object_logic.ML): Fail to atomize TERM n
   The theory continues past it (oops). *)
lemma
  assumes w: "TERM (n::nat)"
  shows "QQ (n::nat)"
  apply (min_script \<open>INDUCT n SORRY_END_ALL\<close>)
  oops

end
