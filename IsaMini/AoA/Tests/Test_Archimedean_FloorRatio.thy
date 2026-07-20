theory Test_Archimedean_FloorRatio
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false, AoA_driver="ClaudeCode"]]
(* Goal 1 from e1a98d264_3 step 25.2.2.1.2.1:
   Given x0 with 1 < x0/\<lfloor>x0\<rfloor> < 2, find N such that
   N*(x0 - \<lfloor>x0\<rfloor>) < \<lfloor>x0\<rfloor> \<le> (N+1)*(x0 - \<lfloor>x0\<rfloor>).
   Archimedean property instance that hammer failed on. *)

lemma archimedean_floor_ratio:
  fixes x0 :: real
  assumes hx0_pos: "0 < x0"
    and hc_gt1: "1 < x0 / real_of_int \<lfloor>x0\<rfloor>"
    and hc_lt2: "x0 / real_of_int \<lfloor>x0\<rfloor> < 2"
    and hfloor_ge1: "1 \<le> \<lfloor>x0\<rfloor>"
  shows "\<exists>(N::nat). real N * (x0 - real_of_int \<lfloor>x0\<rfloor>) < real_of_int \<lfloor>x0\<rfloor>
                   \<and> real_of_int \<lfloor>x0\<rfloor> \<le> real (N + 1) * (x0 - real_of_int \<lfloor>x0\<rfloor>)"
  by aoa

end
