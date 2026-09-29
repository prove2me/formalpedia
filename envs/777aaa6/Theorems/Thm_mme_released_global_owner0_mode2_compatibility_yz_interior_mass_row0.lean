-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row0
-- name    : mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row0
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T00:33:02.290891+00:00
-- url     : https://prove2.me/theorems/077fc227-32b4-4195-b7ca-706532eb8dc7
-- title:
--   owner0 mode2 compatibility interior mass row0
-- statement:
--   Exact released mode-2 compatibility mass identity. The boundary consists of cells with coordinate 0 equal to zero or coordinate 1 equal to zero; interior rows exclude both boundary cases. The integer table and rational atom sum are equal for every word.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row0 : ∀ w : Word,
    ((([22772078408000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 0 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
