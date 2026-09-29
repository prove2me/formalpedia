-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode2_compatibility_interior_mass_row2
-- name    : mme_released_global_owner4_mode2_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:58:15.385832+00:00
-- url     : https://prove2.me/theorems/553e4381-8604-4234-86bb-f849d73540cb
-- title:
--   owner4 mode2 compatibility interior mass row2
-- statement:
--   For owner 4, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode2_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1610070955739111511996045147887709721574741994000000000000, 0, 49970185988634337499741091478621102556850516012000000000000, 0, 1610070955739111511996045147887709721574741994000000000000, 0, 0, 0, 45617883010857099419820640925596184250000000000000000000000, 0, 45617883010857099419820640925596184250000000000000000000000, 0, 0, 0, 0, 0, 1610070929091665070621783144234677843705477366000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45617883010857099419820640925596184250000000000000000000000, 0, 45617883010857099419820640925596184250000000000000000000000, 0, 0, 0, 0, 0, 49970187111275711655740688234749385312589045268000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1610070929091665070621783144234677843705477366000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 2 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
