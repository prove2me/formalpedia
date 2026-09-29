-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode2_word_mass_row2
-- name    : mme_released_global_owner3_mode2_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:16:41.486487+00:00
-- url     : https://prove2.me/theorems/b0babece-2f02-49c5-8a66-635266911537
-- title:
--   owner3 mode2 word mass row2
-- statement:
--   For owner 3, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode2_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1619818082076940719987910149129944975438504504000000000000, 0, 50111787066678807296002279755872920049122990992000000000000, 0, 1619818082009320142331910149129944975438504504000000000000, 0, 0, 0, 45789328633305654583650735568484452250000000000000000000000, 0, 45789328635474968152856735568484452250000000000000000000000, 0, 0, 0, 0, 0, 1619818269998991709286459339213102058490639908000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45789328635762448063139735568484452250000000000000000000000, 0, 45789328635438327390701735568484452250000000000000000000000, 0, 0, 0, 0, 0, 50111773126239055678009038993503176883018720184000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1619818270015486264033459339213102058490639908000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 2 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
