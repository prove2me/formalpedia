-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode1_word_mass_row1
-- name    : mme_released_global_owner5_mode1_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:23:11.923377+00:00
-- url     : https://prove2.me/theorems/a1622b19-cad8-4f92-9731-ffad14ba4051
-- title:
--   owner5 mode1 word mass row1
-- statement:
--   For owner 5, mode 1, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode1_word_mass_row1 : ∀ w : Word,
    ((([0, 28468790523369379248761755622497401000000000000000000000000, 0, 28468790523369379248761755622497401000000000000000000000000, 0, 0, 0, 0, 0, 28468814970130620751238244377502599000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28468814970130620751238244377502599000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 1 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
