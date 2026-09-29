-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode2_word_mass_row2
-- name    : mme_released_global_owner2_mode2_word_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:39:38.795729+00:00
-- url     : https://prove2.me/theorems/24ba6851-74fb-4197-a9ac-1bb440264c27
-- title:
--   owner2 mode2 word mass row2
-- statement:
--   For owner 2, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. These are the masses used by the word entropy certificate.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode2_word_mass_row2 : ∀ w : Word,
    ((([0, 0, 1617209199013346578106357510990668374957512288000000000000, 0, 50116014455081333079756750446759613250084975424000000000000, 0, 1617209199001673707633357510990668374957512288000000000000, 0, 0, 0, 45790073417185542738865845960945422500000000000000000000000, 0, 45790073417199299573959845960945422500000000000000000000000, 0, 0, 0, 0, 0, 1617209103846342349628479423509234538430725189000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45790073417169449566894845960945422500000000000000000000000, 0, 45790073417557417081914845960945422500000000000000000000000, 0, 0, 0, 0, 0, 50116016855919134834931191840458890923138549622000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1617209104026460488308479423509234538430725189000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if (shape s).val 2 = 2 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
