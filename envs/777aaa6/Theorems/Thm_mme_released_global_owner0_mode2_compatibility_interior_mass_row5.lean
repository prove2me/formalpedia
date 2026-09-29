-- Prove2me | Theorems.Thm_mme_released_global_owner0_mode2_compatibility_interior_mass_row5
-- name    : mme_released_global_owner0_mode2_compatibility_interior_mass_row5
-- status  : Disproved
-- author  : @Robertboy18
-- created : 2026-09-24T00:22:08.577106+00:00
-- url     : https://prove2.me/theorems/83d65e87-d01b-4c71-aa16-01c4485b45bc
-- title:
--   owner0 mode2 compatibility interior mass row5
-- statement:
--   This unproved helper was generated with an incorrect boundary predicate: mode 2 requires coordinate 0 = 0 OR coordinate 1 = 0. It is superseded by mme_released_global_owner0_mode2_compatibility_yz_interior_mass_row5. No proof of this incorrect statement was submitted. The original compatibility entropy theorem is unchanged.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner0_mode2_compatibility_interior_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63806495620777510706422216097224000000000000000000000000, 0, 0, 0, 0, 0, 79227442203988734133622069329054399254666133000000000000, 0, 79227442203988734133622069329054399254666133000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63806495620777510706422216097224000000000000000000000000, 0, 0, 0, 0, 0, 4608678843960676890111943750237065201490667734000000000000, 0, 4608678843960676890111943750237065201490667734000000000000, 0, 0, 0, 79227418856883398983270075265793892321203606000000000000, 0, 4608677399742663082945423475056003215357592788000000000000, 0, 79227418856883398983270075265793892321203606000000000000, 0, 0, 0, 0, 0, 0, 0, 79227442203988734133622069329054399254666133000000000000, 0, 79227442203988734133622069329054399254666133000000000000, 0, 0, 0, 79227418856883398983270075265793892321203606000000000000, 0, 4608677399742663082945423475056003215357592788000000000000, 0, 79227418856883398983270075265793892321203606000000000000, 0, 0, 0, 63807411054138250002426269420011000000000000000000000000, 0, 63807411054138250002426269420011000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ ((shape s).val 1).val = 0 ∧ (shape s).val 2 = 5 then ((alpha 0 s * ((jointRows 0 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
