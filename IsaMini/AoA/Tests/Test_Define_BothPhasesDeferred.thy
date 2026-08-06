theory Test_Define_BothPhasesDeferred
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_BothPhasesDeferred"]]

(* NO fun_fake_* debug switch here, on purpose. Stripping the datatype's
   structural rules is what a real environment does to a real definition,
   and it makes phase 1 (pattern completeness/compatibility) leave
   residuals. The function defined in the test then also defeats the
   default termination prover, and the metric it is given closes only
   part of phase 2 — so BOTH obligation phases end up deferred. *)
datatype rbz = ZA nat | ZB rbz | ZC rbz
declare rbz.inject[simp del, iff del]
declare rbz.distinct[simp del, iff del]

lemma define_both_phases_deferred_test: "(2::nat) = 2"
  by  aoa

end
