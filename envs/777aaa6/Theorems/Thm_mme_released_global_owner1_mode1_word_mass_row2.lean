-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode1_word_mass_row2
-- name    : mme_released_global_owner1_mode1_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:05:28.557457+00:00
-- url     : https://prove2.me/theorems/7c36ef34-96ac-4380-ad40-686852ab1d17
-- title:
--   owner1 mode1 word mass row2
-- statement:
--   For owner 1, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode1_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1732554199852915044815782533138162627455489280000000000000, 0, 49831548190216377381238460551991309745089021440000000000000, 0, 1732554199829707355064782533138162627455489280000000000000, 0, 0, 0, 45751396361837706517865999751066515250000000000000000000000, 0, 45751396363637551995501999751066515250000000000000000000000, 0, 0, 0, 0, 0, 1732553990359796814959198739706126807016130545000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45751396362970310561727999751066515250000000000000000000000, 0, 45751396362942055759400999751066515250000000000000000000000, 0, 0, 0, 0, 0, 49831638999369954066730577898054050385967738910000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1732553989983624502694198739706126807016130545000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 1 = 2 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
