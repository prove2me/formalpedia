-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode2_word_mass_row1
-- name    : mme_released_global_owner3_mode2_word_mass_row1
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:16:32.507285+00:00
-- url     : https://prove2.me/theorems/a307ff90-ce73-4c34-8ab3-569c3a69dab5
-- title:
--   owner3 mode2 word mass row1
-- statement:
--   For owner 3, mode 2, and coordinate pool 1, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode2_word_mass_row1 : ∀ w : Word,
    ((([0, 28407045878024294795856461290395884000000000000000000000000, 0, 28407045878024294795856461290395884000000000000000000000000, 0, 0, 0, 0, 0, 28406976564475705204143538709604116000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28406976564475705204143538709604116000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 1 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
