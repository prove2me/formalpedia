-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode2_compatibility_interior_mass_row2
-- name    : mme_released_global_owner2_mode2_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:43:45.332982+00:00
-- url     : https://prove2.me/theorems/8b947c59-972d-46bc-9b75-de44a8d9a147
-- title:
--   owner2 mode2 compatibility interior mass row2
-- statement:
--   For owner 2, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode2_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1610558939234668959615357510990668374957512288000000000000, 0, 49965619687056211566941750446759613250084975424000000000000, 0, 1610558939234668959615357510990668374957512288000000000000, 0, 0, 0, 45619581680938086047905845960945422500000000000000000000000, 0, 45619581680938086047905845960945422500000000000000000000000, 0, 0, 0, 0, 0, 1610558843517273344616479423509234538430725189000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45619581680938086047905845960945422500000000000000000000000, 0, 45619581680938086047905845960945422500000000000000000000000, 0, 0, 0, 0, 0, 49965622087687559632971191840458890923138549622000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1610558843517273344616479423509234538430725189000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 2 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
