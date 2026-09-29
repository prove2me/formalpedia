-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode1_compatibility_interior_mass_row7
-- name    : mme_released_global_owner2_mode1_compatibility_interior_mass_row7
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:43:06.263317+00:00
-- url     : https://prove2.me/theorems/0a9d6521-edb0-4260-89bc-78164a19c2a2
-- title:
--   owner2 mode1 compatibility interior mass row7
-- statement:
--   For owner 2, mode 1, and coordinate pool 7, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode1_compatibility_interior_mass_row7 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4168515000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4168515000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 4168515000000000000000000000000000000000000000000000000, 0, 4168515000000000000000000000000000000000000000000000000, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 7 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
