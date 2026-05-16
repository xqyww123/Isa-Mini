theory Test_FloorN28
  imports Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false, agent_AoA_driver="ClaudeCode"]]
(* Goal 2 from e1a98d264_3 step 25.2.2.1.3.1:
   Given the Archimedean bounds on N and the factored sum constraint,
   prove N = 28. Hammer failed even with harith (28*30=840, 29\<^sup>2=841). *)

lemma floor_N_is_28:
  fixes x0 :: real and a :: rat and N :: nat
  assumes hN_valid: "real N * (x0 - real_of_int \<lfloor>x0\<rfloor>) < real_of_int \<lfloor>x0\<rfloor>"
    and hN_max: "real_of_int \<lfloor>x0\<rfloor> \<le> real (N + 1) * (x0 - real_of_int \<lfloor>x0\<rfloor>)"
    and hfactored_sum: "real_of_int \<lfloor>x0\<rfloor> * 420 = x0 * (\<Sum>x | real_of_int \<lfloor>x\<rfloor> * (x - real_of_int \<lfloor>x\<rfloor>) = real_of_rat a * x\<^sup>2. real_of_int \<lfloor>x\<rfloor>)"
    and hfloor_ge1: "1 \<le> \<lfloor>x0\<rfloor>"
    and hx0_pos: "0 < x0"
    and hquad: "real_of_rat a * (x0 / real_of_int \<lfloor>x0\<rfloor>)\<^sup>2 - x0 / real_of_int \<lfloor>x0\<rfloor> + 1 = 0"
    and hc_gt1: "1 < x0 / real_of_int \<lfloor>x0\<rfloor>"
    and hc_lt2: "x0 / real_of_int \<lfloor>x0\<rfloor> < 2"
    and harith: "28 * (30::real) = 840 \<and> (29::real)\<^sup>2 = 841 \<and> 28 * 29 / 2 = (406::real)"
  shows "N = 28"
  by aoa

end
