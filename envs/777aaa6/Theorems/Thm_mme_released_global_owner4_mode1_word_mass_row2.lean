-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode1_word_mass_row2
-- name    : mme_released_global_owner4_mode1_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:53:30.549661+00:00
-- url     : https://prove2.me/theorems/a200904f-421b-4374-973f-c8160419f499
-- title:
--   owner4 mode1 word mass row2
-- statement:
--   For owner 4, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode1_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1730317310167609705897504141764261459762202400000000000000, 0, 49835570937644078803300546657393516080475595200000000000000, 0, 1730317310510537307755504141764261459762202400000000000000, 0, 0, 0, 45751775529379934810489727825301639000000000000000000000000, 0, 45751775529120791894444727825301639000000000000000000000000, 0, 0, 0, 0, 0, 1730317591418458139526368574732504761970680308000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45751775529169100362474727825301639000000000000000000000000, 0, 45751775529640721506280727825301639000000000000000000000000, 0, 0, 0, 0, 0, 49835656134495774962691796608406395476058639384000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1730317591452992507138368574732504761970680308000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 2 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
