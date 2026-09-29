-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode2_word_mass_row6
-- name    : mme_released_global_owner2_mode2_word_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:40:28.045021+00:00
-- url     : https://prove2.me/theorems/9bd35614-8bac-4d21-9830-ce9bc7b7f199
-- title:
--   owner2 mode2 word mass row6
-- statement:
--   For owner 2, mode 2, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode2_word_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7895368432944900801117825533256665295010680000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 244366057407737194816435746916566669409978640000000000000, 0, 0, 0, 0, 0, 280110341513958246593703236668810000000000000000000000000, 0, 280110341577352330174703236668810000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7895368436366158816117825533256665295010680000000000000, 0, 0, 0, 0, 0, 280110341681735605178703236668810000000000000000000000000, 0, 280110341591444061023703236668810000000000000000000000000, 0, 0, 0, 7895368430775285271336801000821532606856520000000000000, 0, 244365860611938159566842053340036934786286960000000000000, 0, 7895368315748057757336801000821532606856520000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 6 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
