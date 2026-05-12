theory Test_FloorSumK406
  imports Minilang_Agent.Minilang_Agent
begin

(* Goal 3 from e1a98d264_3 step 25.2.2.1.4.1:
   Prove the sum of floors over the solution set equals 406.
   Requires finite-set reindexing + arithmetic series 1+...+28 = 406.
   Hammer cannot bridge the abstract set characterization to concrete enumeration. *)

lemma floor_sum_is_406:
  fixes x0 :: real and a :: rat and N :: nat
  assumes hN28: "N = 28"
    and hN_valid: "real N * (x0 - real_of_int \<lfloor>x0\<rfloor>) < real_of_int \<lfloor>x0\<rfloor>"
    and hN_max: "real_of_int \<lfloor>x0\<rfloor> \<le> real (N + 1) * (x0 - real_of_int \<lfloor>x0\<rfloor>)"
    and hconsec: "\<And>m. 0 < m \<Longrightarrow> real m * (x0 - real_of_int \<lfloor>x0\<rfloor>) < real_of_int \<lfloor>x0\<rfloor> \<Longrightarrow>
        real_of_int \<lfloor>real m * x0 / real_of_int \<lfloor>x0\<rfloor>\<rfloor> * (real m * x0 / real_of_int \<lfloor>x0\<rfloor> - real_of_int \<lfloor>real m * x0 / real_of_int \<lfloor>x0\<rfloor>\<rfloor>) = real_of_rat a * (real m * x0 / real_of_int \<lfloor>x0\<rfloor>)\<^sup>2"
    and huniv: "\<And>y. real_of_int \<lfloor>y\<rfloor> * (y - real_of_int \<lfloor>y\<rfloor>) = real_of_rat a * y\<^sup>2 \<Longrightarrow> 0 < y \<Longrightarrow>
        y * real_of_int \<lfloor>x0\<rfloor> = real_of_int \<lfloor>y\<rfloor> * x0"
    and hfin: "finite {x :: real. real_of_int \<lfloor>x\<rfloor> * (x - real_of_int \<lfloor>x\<rfloor>) = real_of_rat a * x\<^sup>2}"
    and h_nonneg: "\<forall>x \<in> {x :: real. real_of_int \<lfloor>x\<rfloor> * (x - real_of_int \<lfloor>x\<rfloor>) = real_of_rat a * x\<^sup>2}. 0 \<le> x"
    and hfloor_ge1: "1 \<le> \<lfloor>x0\<rfloor>"
    and hx0_pos: "0 < x0"
    and hx0_in: "real_of_int \<lfloor>x0\<rfloor> * (x0 - real_of_int \<lfloor>x0\<rfloor>) = real_of_rat a * x0\<^sup>2"
    and hfactored_sum: "real_of_int \<lfloor>x0\<rfloor> * 420 = x0 * (\<Sum>x | real_of_int \<lfloor>x\<rfloor> * (x - real_of_int \<lfloor>x\<rfloor>) = real_of_rat a * x\<^sup>2. real_of_int \<lfloor>x\<rfloor>)"
  shows "(\<Sum>x | real_of_int \<lfloor>x\<rfloor> * (x - real_of_int \<lfloor>x\<rfloor>) = real_of_rat a * x\<^sup>2. real_of_int \<lfloor>x\<rfloor>) = 406"
  sorry

end
