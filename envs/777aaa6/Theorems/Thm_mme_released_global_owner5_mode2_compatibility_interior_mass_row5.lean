-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode2_compatibility_interior_mass_row5
-- name    : mme_released_global_owner5_mode2_compatibility_interior_mass_row5
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:28:25.988844+00:00
-- url     : https://prove2.me/theorems/3b9d8f83-07bf-4a27-a911-032fdf3bad63
-- title:
--   owner5 mode2 compatibility interior mass row5
-- statement:
--   For owner 5, mode 2, and coordinate pool 5, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode2_compatibility_interior_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63845807867795584378829314202237000000000000000000000000, 0, 0, 0, 0, 0, 79224979929613396621325707076083196849517881000000000000, 0, 79224979929613396621325707076083196849517881000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63845807867795584378829314202237000000000000000000000000, 0, 0, 0, 0, 0, 4608660303497639351280434047779370606300964238000000000000, 0, 4608660303497639351280434047779370606300964238000000000000, 0, 0, 0, 79224753870267499885582805649477983218821188000000000000, 0, 4608645945113499650471875066204090033562357624000000000000, 0, 79224753870267499885582805649477983218821188000000000000, 0, 0, 0, 0, 0, 0, 0, 79224979929613396621325707076083196849517881000000000000, 0, 79224979929613396621325707076083196849517881000000000000, 0, 0, 0, 79224753870267499885582805649477983218821188000000000000, 0, 4608645945113499650471875066204090033562357624000000000000, 0, 79224753870267499885582805649477983218821188000000000000, 0, 0, 0, 63855078421303620855044546363180000000000000000000000000, 0, 63855078421303620855044546363180000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 5 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
