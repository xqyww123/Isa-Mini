theory ScratchInfraStudy
  imports Minilang_AoA
begin

(* scratch theory for infra-constant study; safe to delete *)
find_theorems "Rat.of_int _"

ML \<open>
  val ctxt = Context.Proof \<^context>;
  val {is_infra_const, is_infra_thm, ...} = Infra_Filter.gen_infra_filters ctxt;
  val res_const = is_infra_const "Rat.of_int";
  val res_const_ri = is_infra_const "Int.ring_1_class.of_int";
  (* check the two named thms *)
  fun chk nm = (nm, is_infra_thm (nm, Global_Theory.get_thm \<^theory> nm));
  val res_def = chk "Rat.of_int_def";
  val res_qoi = chk "Rat.quotient_of_int";
  val res_qoi2 = chk "Rat.quotient_of_rat_of_int";
\<close>

end
