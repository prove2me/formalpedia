-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_compatibility_interior_mass_row1
-- name    : mme_released_global_owner0_mode2_compatibility_interior_mass_row1
-- status  : Disproved
-- author  : @Robertboy18
-- created : 2026-09-24T00:21:55.187052+00:00
-- url     : https://prove2.me/theorems/b0baf01d-c434-456d-9b02-a51034397816
-- title:
--   owner0 mode2 compatibility interior mass row1
-- statement:
--   This unproved helper was generated with an incorrect boundary predicate: mode 2 requires coordinate 0 = 0 OR coordinate 1 = 0. It is superseded by mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row1. No proof of this incorrect statement was submitted. The original compatibility entropy theorem is unchanged.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_compatibility_interior_mass_row1 : ∀ w : Word,
    ((([0, 28398126275245566910706541358579060500000000000000000000000, 0, 28398126275245566910706541358579060500000000000000000000000, 0, 0, 0, 0, 0, 28398001395754433089293458641420939500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28398001395754433089293458641420939500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 1).val = 0 ∧ (shape s).val 2 = 1 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
