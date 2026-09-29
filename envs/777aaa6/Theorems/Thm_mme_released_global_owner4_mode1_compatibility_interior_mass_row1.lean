-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode1_compatibility_interior_mass_row1
-- name    : mme_released_global_owner4_mode1_compatibility_interior_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:54:57.752976+00:00
-- url     : https://prove2.me/theorems/389ce6ad-7fd0-491b-8379-86dd971266c8
-- title:
--   owner4 mode1 compatibility interior mass row1
-- statement:
--   For owner 4, mode 1, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode1_compatibility_interior_mass_row1 : ∀ w : Word,
    ((([0, 28464880876489654892553593992761097000000000000000000000000, 0, 28464880876489654892553593992761097000000000000000000000000, 0, 0, 0, 0, 0, 28464643969510345107446406007238903000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28464643969510345107446406007238903000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 1 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
