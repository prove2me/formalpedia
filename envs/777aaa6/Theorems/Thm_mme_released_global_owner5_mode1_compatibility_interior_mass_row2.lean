-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode1_compatibility_interior_mass_row2
-- name    : mme_released_global_owner5_mode1_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:26:26.066097+00:00
-- url     : https://prove2.me/theorems/5f33a897-0fc6-4fd5-8931-7db00a260b84
-- title:
--   owner5 mode1 compatibility interior mass row2
-- statement:
--   For owner 5, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode1_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1728739181356370859372579545064550463898801676000000000000, 0, 49756541005858763906547936327414362072202396648000000000000, 0, 1728739181342538619300579545064550463898801676000000000000, 0, 0, 0, 45667029361150477393367523833416454500000000000000000000000, 0, 45667029360819985657361523833416454500000000000000000000000, 0, 0, 0, 0, 0, 1728738937248301017400162926099140548712110792000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45667029361128247007537523833416454500000000000000000000000, 0, 45667029361275461562589523833416454500000000000000000000000, 0, 0, 0, 0, 0, 49756519178722225574192483396592437902575778416000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1728738937097628402330162926099140548712110792000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 2 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
