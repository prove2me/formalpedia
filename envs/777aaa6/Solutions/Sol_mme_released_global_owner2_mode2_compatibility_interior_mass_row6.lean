-- Prove2me | solution 1 for mme_released_global_owner2_mode2_compatibility_interior_mass_row6
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T01:54:44.030232+00:00
-- url     : https://prove2.me/submissions/bda06cd7-b192-423e-bc6e-4af41ea41ea0

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49233793709660117825533256665295010680000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75270951406339879919435746916566669409978640000000000000, 0, 0, 0, 0, 0, 126889658878748170993703236668810000000000000000000000000, 0, 126889658878748170993703236668810000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49233793709660117825533256665295010680000000000000, 0, 0, 0, 0, 0, 126889658878748170993703236668810000000000000000000000000, 0, 126889658878748170993703236668810000000000000000000000000, 0, 0, 0, 49233620314934336801000821532606856520000000000000, 0, 75270656143839386916842053340036934786286960000000000000, 0, 49233620314934336801000821532606856520000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 6 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
