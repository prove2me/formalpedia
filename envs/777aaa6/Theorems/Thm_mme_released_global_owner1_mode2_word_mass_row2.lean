-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode2_word_mass_row2
-- name    : mme_released_global_owner1_mode2_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:06:38.624331+00:00
-- url     : https://prove2.me/theorems/3e205eb5-c15c-4a7e-8a4f-0aaceb6ffd51
-- title:
--   owner1 mode2 word mass row2
-- statement:
--   For owner 1, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode2_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1616945077100562560046709290710097969999204400000000000000, 0, 50118887694281939955222804450957180060001591200000000000000, 0, 1616945077096319749597709290710097969999204400000000000000, 0, 0, 0, 45788702637632223988751793825936122500000000000000000000000, 0, 45788702637733314611483793825936122500000000000000000000000, 0, 0, 0, 0, 0, 1616944956534035512238539166063664068321683664000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45788702637615424462648793825936122500000000000000000000000, 0, 45788702637572591413302793825936122500000000000000000000000, 0, 0, 0, 0, 0, 50118890238896040971081523331750805863356632672000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1616944956537546775625539166063664068321683664000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 2 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
