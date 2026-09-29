-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode2_compatibility_interior_mass_row5
-- name    : mme_released_global_owner3_mode2_compatibility_interior_mass_row5
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:22:32.995264+00:00
-- url     : https://prove2.me/theorems/b213e9cc-527a-47a4-bc19-8afe796afc3d
-- title:
--   owner3 mode2 compatibility interior mass row5
-- statement:
--   For owner 3, mode 2, and coordinate pool 5, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode2_compatibility_interior_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63825868027705115338276058435396500000000000000000000000, 0, 0, 0, 0, 0, 79226656097016699837377703823069905914043735000000000000, 0, 79226656097016699837377703823069905914043735000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63825868027705115338276058435396500000000000000000000000, 0, 0, 0, 0, 0, 4608675338499932014270381554585187688171912530000000000000, 0, 4608675338499932014270381554585187688171912530000000000000, 0, 0, 0, 79226681776254819526000870691722684554708196500000000000, 0, 4608677006359080350188148681197335130890583607000000000000, 0, 79226681776254819526000870691722684554708196500000000000, 0, 0, 0, 0, 0, 0, 0, 79226656097016699837377703823069905914043735000000000000, 0, 79226656097016699837377703823069905914043735000000000000, 0, 0, 0, 79226681776254819526000870691722684554708196500000000000, 0, 4608677006359080350188148681197335130890583607000000000000, 0, 79226681776254819526000870691722684554708196500000000000, 0, 0, 0, 63824657866739481476436556752495500000000000000000000000, 0, 63824657866739481476436556752495500000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 5 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
