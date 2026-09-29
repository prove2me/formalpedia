-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode2_word_mass_row6
-- name    : mme_released_global_owner5_mode2_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:25:19.63901+00:00
-- url     : https://prove2.me/theorems/c7637613-f9e4-41af-8ab1-84535b195be1
-- title:
--   owner5 mode2 word mass row6
-- statement:
--   For owner 5, mode 2, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode2_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7898206839755884619968527589969464096013569000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244419209152072051718614011053837071807972862000000000000, 0, 0, 0, 0, 0, 280091507184863772866479657428947250000000000000000000000, 0, 280091507301203820356479657428947250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7898207113648833345968527589969464096013569000000000000, 0, 0, 0, 0, 0, 280091507130342921598479657428947250000000000000000000000, 0, 280091507021739976560479657428947250000000000000000000000, 0, 0, 0, 7898206959711453766099319644288439707525708000000000000, 0, 244392493336319769935331664761858120584948584000000000000, 0, 7898206960341515232099319644288439707525708000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 6 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
