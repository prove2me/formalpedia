-- Prove2me | solution 1 for mme_released_global_owner2_mode2_word_mass_row1
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T01:45:16.557007+00:00
-- url     : https://prove2.me/submissions/d451a1fb-bd24-4baf-a1ff-ccd0c36e0404

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 28406764603747267186207424393692969500000000000000000000000, 0, 28406764603747267186207424393692969500000000000000000000000, 0, 0, 0, 0, 0, 28406766815752732813792575606307030500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28406766815752732813792575606307030500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 1 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
