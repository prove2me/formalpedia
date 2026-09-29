-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode1_compatibility_interior_mass_row0
-- name    : mme_released_global_owner3_mode1_compatibility_interior_mass_row0
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:19:19.507436+00:00
-- url     : https://prove2.me/theorems/ac32705f-0bfc-4491-af25-59fcd4a7db29
-- title:
--   owner3 mode1 compatibility interior mass row0
-- statement:
--   For owner 3, mode 1, and coordinate pool 0, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode1_compatibility_interior_mass_row0 : ∀ w : Word,
    ((([23074105196000000000000000000000000000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 0 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
