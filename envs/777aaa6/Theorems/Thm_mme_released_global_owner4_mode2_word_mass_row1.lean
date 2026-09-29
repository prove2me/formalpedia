-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode2_word_mass_row1
-- name    : mme_released_global_owner4_mode2_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:54:08.366672+00:00
-- url     : https://prove2.me/theorems/adb8f3f0-f28f-4e02-8eb7-21f6fe672dff
-- title:
--   owner4 mode2 word mass row1
-- statement:
--   For owner 4, mode 2, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode2_word_mass_row1 : ∀ w : Word,
    ((([0, 28406734129979293426528106466564954000000000000000000000000, 0, 28406734129979293426528106466564954000000000000000000000000, 0, 0, 0, 0, 0, 28406720422020706573471893533435046000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28406720422020706573471893533435046000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 1 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
