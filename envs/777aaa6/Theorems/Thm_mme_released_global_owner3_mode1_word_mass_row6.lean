-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode1_word_mass_row6
-- name    : mme_released_global_owner3_mode1_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:16:05.158669+00:00
-- url     : https://prove2.me/theorems/37b3c904-c230-4968-9f41-359bf4d4ea3a
-- title:
--   owner3 mode1 word mass row6
-- statement:
--   For owner 3, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode1_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8247586191565617063815359706874373087389030000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234880732118108473613524004483243253825221940000000000000, 0, 0, 0, 0, 0, 289230108011470013662790237399692000000000000000000000000, 0, 289230108259938954130790237399692000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8247586178042798757815359706874373087389030000000000000, 0, 0, 0, 0, 0, 289230107918650903732790237399692000000000000000000000000, 0, 289230108134629813738790237399692000000000000000000000000, 0, 0, 0, 8248259793808700039793317390823510874549936000000000000, 0, 234913336594154724744097691722592978250900128000000000000, 0, 8248259799630000515793317390823510874549936000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 6 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
