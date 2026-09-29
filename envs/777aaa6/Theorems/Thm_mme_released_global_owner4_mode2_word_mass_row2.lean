-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode2_word_mass_row2
-- name    : mme_released_global_owner4_mode2_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:53:30.816795+00:00
-- url     : https://prove2.me/theorems/b08d3bde-f116-42c0-8c9a-5ab7b4144139
-- title:
--   owner4 mode2 word mass row2
-- statement:
--   For owner 4, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode2_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1616722933598948422419045147887709721574741994000000000000, 0, 50120555840627431245455091478621102556850516012000000000000, 0, 1616722933594358747757045147887709721574741994000000000000, 0, 0, 0, 45788373452052431789820640925596184250000000000000000000000, 0, 45788373452061946383273640925596184250000000000000000000000, 0, 0, 0, 0, 0, 1616722907077274705724783144234677843705477366000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45788373452274508983405640925596184250000000000000000000000, 0, 45788373452137026224616640925596184250000000000000000000000, 0, 0, 0, 0, 0, 50120556959463785721563688234749385312589045268000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1616722907112287775963783144234677843705477366000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 2 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
