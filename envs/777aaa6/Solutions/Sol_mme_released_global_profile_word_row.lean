-- Prove2me | solution 1 for mme_released_global_profile_word_row
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:35:32.821228+00:00
-- url     : https://prove2.me/submissions/3b115d45-17c2-4be5-b3d8-5fd17a0f59d2

import Theorems.Thm_mme_released_global_word_counts_row_marginal

open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- Normalized global word masses equal the rational finite atom-row marginals. -/
theorem solution
    (owner : Fin 6) (i : Fin 3) (s : Fin 45) (w : Word) :
    (profile owner).2 i ⟨0, shapeEquiv s⟩ w =
      (((alpha owner s * ((jointRows owner s).map
        (fun a => if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℚ) /
          (denominator : ℚ) ^ 5 : ℚ) := by
  simp only [profile, mme_released_global_word_counts_row_marginal,
    Equiv.symm_apply_apply, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]


#print axioms solution
