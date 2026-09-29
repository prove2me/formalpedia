-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode1_word_mass_row2
-- name    : mme_released_global_owner5_mode1_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:23:44.618166+00:00
-- url     : https://prove2.me/theorems/f7b7f3d3-ec96-45ea-8f18-44350c250804
-- title:
--   owner5 mode1 word mass row2
-- statement:
--   For owner 5, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode1_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1732200911076438630473579545064550463898801676000000000000, 0, 49834643757534194240526936327414362072202396648000000000000, 0, 1732200911328983176171579545064550463898801676000000000000, 0, 0, 0, 45750165676145328683997523833416454500000000000000000000000, 0, 45750165675822375913626523833416454500000000000000000000000, 0, 0, 0, 0, 0, 1732200667590082154534162926099140548712110792000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45750165676116564527950523833416454500000000000000000000000, 0, 45750165676650276721223523833416454500000000000000000000000, 0, 0, 0, 0, 0, 49834621955291823032650483396592437902575778416000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1732200667443932918845162926099140548712110792000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 2 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
