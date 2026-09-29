-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode1_compatibility_interior_mass_row7
-- name    : mme_released_global_owner5_mode1_compatibility_interior_mass_row7
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:27:29.502992+00:00
-- url     : https://prove2.me/theorems/2aff8dc0-257d-4e1f-80a7-a25ad19c8821
-- title:
--   owner5 mode1 compatibility interior mass row7
-- statement:
--   For owner 5, mode 1, and coordinate pool 7, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode1_compatibility_interior_mass_row7 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4171340000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4171340000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 4171340000000000000000000000000000000000000000000000000, 0, 4171340000000000000000000000000000000000000000000000000, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 7 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
