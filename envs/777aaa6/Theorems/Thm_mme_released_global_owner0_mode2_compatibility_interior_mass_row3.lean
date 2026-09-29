-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_compatibility_interior_mass_row3
-- name    : mme_released_global_owner0_mode2_compatibility_interior_mass_row3
-- status  : Disproved
-- author  : @Robertboy18
-- created : 2026-09-24T00:22:05.035331+00:00
-- url     : https://prove2.me/theorems/f7cb2d60-d679-4653-b719-38cbb0b42544
-- title:
--   owner0 mode2 compatibility interior mass row3
-- statement:
--   This unproved helper was generated with an incorrect boundary predicate: mode 2 requires coordinate 0 = 0 OR coordinate 1 = 0. It is superseded by mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row3. No proof of this incorrect statement was submitted. The original compatibility entropy theorem is unchanged.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_compatibility_interior_mass_row3 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 2209524917797719572244098332634472500000000000000000000000, 0, 2209524917797719572244098332634472500000000000000000000000, 0, 0, 0, 2610209072239182537989693746132600304344832772500000000000, 0, 78504771795687985104257424913264706391310334455000000000000, 0, 2610209072239182537989693746132600304344832772500000000000, 0, 0, 0, 2610208666733907536260837227146643335685494926000000000000, 0, 2610208666733907536260837227146643335685494926000000000000, 0, 0, 0, 0, 0, 0, 0, 2610209072239182537989693746132600304344832772500000000000, 0, 78504771795687985104257424913264706391310334455000000000000, 0, 2610209072239182537989693746132600304344832772500000000000, 0, 0, 0, 78504795062322160052963228384543060828629010148000000000000, 0, 78504795062322160052963228384543060828629010148000000000000, 0, 0, 0, 0, 0, 2209496640745955122034186422999273000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2610208666733907536260837227146643335685494926000000000000, 0, 2610208666733907536260837227146643335685494926000000000000, 0, 0, 0, 0, 0, 2209496640745955122034186422999273000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 1).val = 0 ∧ (shape s).val 2 = 3 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
