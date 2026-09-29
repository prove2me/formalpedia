-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode2_word_mass_row1
-- name    : mme_released_global_owner5_mode2_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:24:00.838124+00:00
-- url     : https://prove2.me/theorems/0e347ef8-2758-47e7-bd7a-e1d21431868a
-- title:
--   owner5 mode2 word mass row1
-- statement:
--   For owner 5, mode 2, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode2_word_mass_row1 : ∀ w : Word,
    ((([0, 28406700588602792015594847786130216000000000000000000000000, 0, 28406700588602792015594847786130216000000000000000000000000, 0, 0, 0, 0, 0, 28406605492397207984405152213869784000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28406605492397207984405152213869784000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 1 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
