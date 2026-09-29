-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode1_word_mass_row6
-- name    : mme_released_global_owner1_mode1_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:06:06.852989+00:00
-- url     : https://prove2.me/theorems/4400fa6b-7246-4f98-98dc-2007adb42b73
-- title:
--   owner1 mode1 word mass row6
-- statement:
--   For owner 1, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode1_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8253290007476012602686242278045805038633300000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 234850607501536983904181113168908389922733400000000000000, 0, 0, 0, 0, 0, 289251742967448297889867407097100000000000000000000000000, 0, 289251743100018326591867407097100000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8253290013418793302686242278045805038633300000000000000, 0, 0, 0, 0, 0, 289251743120586631671867407097100000000000000000000000000, 0, 289251743044852670850867407097100000000000000000000000000, 0, 0, 0, 8253137493525226504321133744916576124923900000000000000, 0, 234843243313132986001334506396766847750152200000000000000, 0, 8253137438004070680321133744916576124923900000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 6 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
