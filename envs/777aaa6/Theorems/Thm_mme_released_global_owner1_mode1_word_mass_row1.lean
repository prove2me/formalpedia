-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode1_word_mass_row1
-- name    : mme_released_global_owner1_mode1_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:05:30.396621+00:00
-- url     : https://prove2.me/theorems/3e877622-cc19-477c-a986-0ebe002bcd7b
-- title:
--   owner1 mode1 word mass row1
-- statement:
--   For owner 1, mode 1, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode1_word_mass_row1 : ∀ w : Word,
    ((([0, 28469009094657646639948376158731672500000000000000000000000, 0, 28469009094657646639948376158731672500000000000000000000000, 0, 0, 0, 0, 0, 28468724494842353360051623841268327500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28468724494842353360051623841268327500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 1 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
