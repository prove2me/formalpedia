-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode2_word_mass_row6
-- name    : mme_released_global_owner4_mode2_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:54:26.818103+00:00
-- url     : https://prove2.me/theorems/b2c7a8cf-2f61-4ea2-bc14-a9b46f9035cf
-- title:
--   owner4 mode2 word mass row6
-- statement:
--   For owner 4, mode 2, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode2_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7896607075924685465508355105497368223308082000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244351433157684503286127429824323263553383836000000000000, 0, 0, 0, 0, 0, 280007329316127306192732804919524000000000000000000000000, 0, 280007328652321085229732804919524000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7896607119566573117508355105497368223308082000000000000, 0, 0, 0, 0, 0, 280007328334951047009732804919524000000000000000000000000, 0, 280007328607993413018732804919524000000000000000000000000, 0, 0, 0, 7896607258859364194303362410832023556238838000000000000, 0, 244707175282605243571317915464921952887522324000000000000, 0, 7896607193966778914303362410832023556238838000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 6 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
