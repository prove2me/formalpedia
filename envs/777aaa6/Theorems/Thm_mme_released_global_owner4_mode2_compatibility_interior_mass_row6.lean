-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode2_compatibility_interior_mass_row6
-- name    : mme_released_global_owner4_mode2_compatibility_interior_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:58:05.052475+00:00
-- url     : https://prove2.me/theorems/fee9b820-1424-4918-9161-50877d2bfbf8
-- title:
--   owner4 mode2 compatibility interior mass row6
-- statement:
--   For owner 4, mode 2, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode2_compatibility_interior_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77372531587847508355105497368223308082000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75216438052214607696127429824323263553383836000000000000, 0, 0, 0, 0, 0, 126723205369239898014732804919524000000000000000000000000, 0, 126723205369239898014732804919524000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77372531587847508355105497368223308082000000000000, 0, 0, 0, 0, 0, 126723205369239898014732804919524000000000000000000000000, 0, 126723205369239898014732804919524000000000000000000000000, 0, 0, 0, 77923563937607303362410832023556238838000000000000, 0, 75752088878634749335317915464921952887522324000000000000, 0, 77923563937607303362410832023556238838000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 6 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
