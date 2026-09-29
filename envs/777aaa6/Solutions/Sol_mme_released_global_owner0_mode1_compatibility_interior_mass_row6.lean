-- Prove2me | solution 1 for mme_released_global_owner0_mode1_compatibility_interior_mass_row6
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T00:36:38.93271+00:00
-- url     : https://prove2.me/submissions/42dcc9c8-179b-423e-99fe-c5b5ed49c60b

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- Exact rational table identity for the released outer profile. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4332892174577221283621661424410707841378990000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146300343983338827237546072900290584317242020000000000000, 0, 0, 0, 0, 0, 213092046778830446386852851768514000000000000000000000000, 0, 213092046768323086873852851768514000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4332892067502224341621661424410707841378990000000000000, 0, 0, 0, 0, 0, 213092046775828343668852851768514000000000000000000000000, 0, 213092046736801008334852851768514000000000000000000000000, 0, 0, 0, 4338769958610247309860225292823362354565060000000000000, 0, 146571675760052063278078746591185275290869880000000000000, 0, 4338769996136531284860225292823362354565060000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 2).val = 0 ∧ (shape s).val 1 = 6 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
