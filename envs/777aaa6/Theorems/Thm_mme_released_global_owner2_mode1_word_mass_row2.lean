-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode1_word_mass_row2
-- name    : mme_released_global_owner2_mode1_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:39:10.483441+00:00
-- url     : https://prove2.me/theorems/2464ff2f-2b46-424a-9f56-0df6ea0603d5
-- title:
--   owner2 mode1 word mass row2
-- statement:
--   For owner 2, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode1_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1733778823891507757550392392217492144816613826000000000000, 0, 49829695753829683103165130583953653710366772348000000000000, 0, 1733778824239327922832392392217492144816613826000000000000, 0, 0, 0, 45751022723414766674537504611130576750000000000000000000000, 0, 45751022723490226763966504611130576750000000000000000000000, 0, 0, 0, 0, 0, 1733779186919273316534162255277463680638607365000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45751022723396256312197504611130576750000000000000000000000, 0, 45751022723013699448721504611130576750000000000000000000000, 0, 0, 0, 0, 0, 49829694285879951449844741676534127638722785270000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1733779186925307250650162255277463680638607365000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 2 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
