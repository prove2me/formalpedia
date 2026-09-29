-- Prove2me | solution 1 for mme_released_global_owner1_mode2_compatibility_interior_mass_row2
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T01:20:18.309985+00:00
-- url     : https://prove2.me/submissions/26542764-bb9e-4257-adfd-df7741917edc

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 1610294628607218766189709290710097969999204400000000000000, 0, 49968517636619449577900804450957180060001591200000000000000, 0, 1610294628607218766189709290710097969999204400000000000000, 0, 0, 0, 45618231445831669821199793825936122500000000000000000000000, 0, 45618231445831669821199793825936122500000000000000000000000, 0, 0, 0, 0, 0, 1610294446066665741451539166063664068321683664000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45618231445831669821199793825936122500000000000000000000000, 0, 45618231445831669821199793825936122500000000000000000000000, 0, 0, 0, 0, 0, 49968518449706102122017523331750805863356632672000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1610294446066665741451539166063664068321683664000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 2 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
