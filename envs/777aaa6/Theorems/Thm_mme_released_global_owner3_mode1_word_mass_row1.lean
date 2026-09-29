-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode1_word_mass_row1
-- name    : mme_released_global_owner3_mode1_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:16:04.722805+00:00
-- url     : https://prove2.me/theorems/63546732-6f85-4a0d-a482-25e80c14e2a6
-- title:
--   owner3 mode1 word mass row1
-- statement:
--   For owner 3, mode 1, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode1_word_mass_row1 : ∀ w : Word,
    ((([0, 28468966199693409882099528520550393500000000000000000000000, 0, 28468966199693409882099528520550393500000000000000000000000, 0, 0, 0, 0, 0, 28468947850306590117900471479449606500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28468947850306590117900471479449606500000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 1 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
