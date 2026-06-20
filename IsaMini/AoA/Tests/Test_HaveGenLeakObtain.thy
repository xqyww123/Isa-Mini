theory Test_HaveGenLeakObtain
  imports Minilang_Agent.Minilang_Agent
begin

(* The set-subset goal {r. 0<r} \<subseteq> S is NOT introducible by Minilang INTRO
   (it is `subset_eq`, not a Pure/HOL quantifier/implication), so `r` is never
   fixed.  A subsequent Obtain whose constraint mentions `r` introduces it as a
   stray Free living in a hypothesis, and a Have referring to `r` then leaks the
   raw kernel exception `THM 0 ... generalize: variable free in assumptions`. *)
lemma have_gen_leak_obtain:
  fixes S :: "rat set"
  shows "{r. 0 < r} \<subseteq> S"
  by aoa

end
