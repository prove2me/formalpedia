-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode1_word_mass_row6
-- name    : mme_released_global_owner4_mode1_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:53:11.769428+00:00
-- url     : https://prove2.me/theorems/1f41fa98-483e-4aed-b597-b5abb6124c40
-- title:
--   owner4 mode1 word mass row6
-- statement:
--   For owner 4, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode1_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8254527538375063449732149251037045209570336000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234811583540889836727113155691877909580859328000000000000, 0, 0, 0, 0, 0, 289272587127469632412900103268676000000000000000000000000, 0, 289272585752897443129900103268676000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8254527567492133511732149251037045209570336000000000000, 0, 0, 0, 0, 0, 289272587094066100890900103268676000000000000000000000000, 0, 289272587176549748666900103268676000000000000000000000000, 0, 0, 0, 8254527444071406330057184188786573142526528000000000000, 0, 234811580314120315233707764353770853714946944000000000000, 0, 8254527444068319647057184188786573142526528000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 6 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
