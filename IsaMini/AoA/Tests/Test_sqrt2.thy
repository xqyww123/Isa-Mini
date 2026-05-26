theory Test_sqrt2
  imports Complex_Main
begin

theorem sqrt2_not_rational:
    "sqrt 2 \<notin> \<rat>"
proof
  assume "sqrt 2 \<in> \<rat>"
  then obtain m n :: nat where n: "n \<noteq> 0" and eq: "\<bar>sqrt 2\<bar> = real m / real n" and cop: "coprime m n"
    by (rule Rats_abs_nat_div_natE)
  have sq: "2 * n^2 = m^2"
  proof -
    have "sqrt 2 = real m / real n"
      using eq by simp
    then have "(sqrt 2)^2 = (real m / real n)^2"
      by simp
    then have "2 = (real m / real n)^2"
      by (simp add: real_sqrt_pow2)
    then have "2 * (real n)^2 = (real m)^2"
      using n by (simp add: field_simps power2_eq_square)
    then show ?thesis
      by (metis of_nat_eq_iff of_nat_mult of_nat_power of_nat_numeral)
  qed
  have even_m: "even m"
  proof -
    have "even (m^2)"
      using sq by simp
    then show ?thesis
      by (simp add: even_power)
  qed
  then obtain k where m: "m = 2 * k"
    by auto
  have even_n: "even n"
  proof -
    have "2 * n^2 = (2 * k)^2"
      using sq m by simp
    then have "n^2 = 2 * k^2"
      by simp
    then have "even (n^2)"
      by simp
    then show ?thesis
      by (simp add: even_power)
  qed
  have "2 dvd gcd m n"
    using even_m even_n by (simp add: gcd_greatest)
  then have "2 dvd 1"
    using cop by (simp add: coprime_iff_gcd_eq_1)
  then show False
    by simp
qed
end