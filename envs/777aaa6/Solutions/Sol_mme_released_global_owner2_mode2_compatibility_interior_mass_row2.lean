-- Prove2me | solution 1 for mme_released_global_owner2_mode2_compatibility_interior_mass_row2
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T01:53:14.956205+00:00
-- url     : https://prove2.me/submissions/8593f895-0d37-463a-9131-65b5970e6dd1

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 1610558939234668959615357510990668374957512288000000000000, 0, 49965619687056211566941750446759613250084975424000000000000, 0, 1610558939234668959615357510990668374957512288000000000000, 0, 0, 0, 45619581680938086047905845960945422500000000000000000000000, 0, 45619581680938086047905845960945422500000000000000000000000, 0, 0, 0, 0, 0, 1610558843517273344616479423509234538430725189000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45619581680938086047905845960945422500000000000000000000000, 0, 45619581680938086047905845960945422500000000000000000000000, 0, 0, 0, 0, 0, 49965622087687559632971191840458890923138549622000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1610558843517273344616479423509234538430725189000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 2 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
