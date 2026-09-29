-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode2_word_mass_row2
-- name    : mme_released_global_owner5_mode2_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:23:36.948987+00:00
-- url     : https://prove2.me/theorems/3c5636f0-7551-4078-ad6f-39480e704355
-- title:
--   owner5 mode2 word mass row2
-- statement:
--   For owner 5, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode2_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1617432091113470226816707121468465917928857311000000000000, 0, 50116188934236379434292981405413447164142285378000000000000, 0, 1617432090977577890791707121468465917928857311000000000000, 0, 0, 0, 45789903343471953296246723529449118250000000000000000000000, 0, 45789903341387697415225723529449118250000000000000000000000, 0, 0, 0, 0, 0, 1617431615069884702287506798688765653799024032000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45789903341450183431348723529449118250000000000000000000000, 0, 45789903341393201373465723529449118250000000000000000000000, 0, 0, 0, 0, 0, 50116174879796760624618696636475616692401951936000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1617431615102891604905506798688765653799024032000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 2 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
