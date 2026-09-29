-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode2_word_mass_row6
-- name    : mme_released_global_owner1_mode2_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:06:48.215974+00:00
-- url     : https://prove2.me/theorems/87477151-280c-44f4-947e-85a3fcdffe12
-- title:
--   owner1 mode2 word mass row6
-- statement:
--   For owner 1, mode 2, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode2_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7898580274040976050754428925086352514787572000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244359116420422125043700603207597294970424856000000000000, 0, 0, 0, 0, 0, 279988577629532470098816588867073000000000000000000000000, 0, 279988577596010433180816588867073000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7898580337474511874754428925086352514787572000000000000, 0, 0, 0, 0, 0, 279988576561482030150816588867073000000000000000000000000, 0, 279988577128939560380816588867073000000000000000000000000, 0, 0, 0, 7898580647751569439552953875839540887118366000000000000, 0, 244717650819941166208418275722258918225763268000000000000, 0, 7898580584405157571552953875839540887118366000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 6 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
