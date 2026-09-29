-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode1_word_mass_row2
-- name    : mme_released_global_owner3_mode1_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:16:37.215614+00:00
-- url     : https://prove2.me/theorems/600df024-1e13-48f8-a89e-9ac867e876e0
-- title:
--   owner3 mode1 word mass row2
-- statement:
--   For owner 3, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode1_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1732668790477631947726896972423236431105109627000000000000, 0, 49828910459505196083770072258408819137789780746000000000000, 0, 1732668790480631013558896972423236431105109627000000000000, 0, 0, 0, 45752336530813953821940347465501188000000000000000000000000, 0, 45752336530377554682766347465501188000000000000000000000000, 0, 0, 0, 0, 0, 1732668590699289338408395730048606443595973564000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45752336530725663568352347465501188000000000000000000000000, 0, 45752336530431710242406347465501188000000000000000000000000, 0, 0, 0, 0, 0, 49828914673125047752203952474642743112808052872000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1732668590363321548866395730048606443595973564000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 2 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
