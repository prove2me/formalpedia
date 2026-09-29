-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode1_word_mass_row1
-- name    : mme_released_global_owner2_mode1_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:39:03.965307+00:00
-- url     : https://prove2.me/theorems/c063d836-5944-44c6-92ad-c5ee45fdb525
-- title:
--   owner2 mode1 word mass row1
-- statement:
--   For owner 2, mode 1, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode1_word_mass_row1 : ∀ w : Word,
    ((([0, 28468951382995231818106663869776832000000000000000000000000, 0, 28468951382995231818106663869776832000000000000000000000000, 0, 0, 0, 0, 0, 28468953821004768181893336130223168000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28468953821004768181893336130223168000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 1 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
