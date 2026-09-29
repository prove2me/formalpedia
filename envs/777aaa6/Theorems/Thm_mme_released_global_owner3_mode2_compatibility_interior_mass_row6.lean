-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode2_compatibility_interior_mass_row6
-- name    : mme_released_global_owner3_mode2_compatibility_interior_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:22:45.043458+00:00
-- url     : https://prove2.me/theorems/56be2201-c701-4355-9854-b646ebb3f389
-- title:
--   owner3 mode2 compatibility interior mass row6
-- statement:
--   For owner 3, mode 2, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode2_compatibility_interior_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 190095154734385083235851218098064936904000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75260994515795664059245866188939803870126192000000000000, 0, 0, 0, 0, 0, 126830798737739289841957940572859500000000000000000000000, 0, 126830798737739289841957940572859500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 190095154734385083235851218098064936904000000000000, 0, 0, 0, 0, 0, 126830798737739289841957940572859500000000000000000000000, 0, 126830798737739289841957940572859500000000000000000000000, 0, 0, 0, 190181652061730303567638115325096485394000000000000, 0, 75292263979633584342148764540955349807029212000000000000, 0, 190181652061730303567638115325096485394000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 6 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
