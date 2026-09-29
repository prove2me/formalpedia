-- Prove2me | Theorems.Thm_mme_released_global_owner2_mode2_compatibility_interior_mass_row5
-- name    : mme_released_global_owner2_mode2_compatibility_interior_mass_row5
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:43:42.881263+00:00
-- url     : https://prove2.me/theorems/5361ce4a-cf70-4e9f-a210-38434f3fb9a3
-- title:
--   owner2 mode2 compatibility interior mass row5
-- statement:
--   For owner 2, mode 2, and coordinate pool 5, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner2_mode2_compatibility_interior_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63841623218334436434478609288041000000000000000000000000, 0, 0, 0, 0, 0, 79225095695780147973964521419422088802116412000000000000, 0, 79225095695780147973964521419422088802116412000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63841623218334436434478609288041000000000000000000000000, 0, 0, 0, 0, 0, 4608625710060574211943657158968587822395767176000000000000, 0, 4608625710060574211943657158968587822395767176000000000000, 0, 0, 0, 79225068306833783835167947146234960509710179000000000000, 0, 4608623687824086780200362153112721078980579642000000000000, 0, 79225068306833783835167947146234960509710179000000000000, 0, 0, 0, 0, 0, 0, 0, 79225095695780147973964521419422088802116412000000000000, 0, 79225095695780147973964521419422088802116412000000000000, 0, 0, 0, 79225068306833783835167947146234960509710179000000000000, 0, 4608623687824086780200362153112721078980579642000000000000, 0, 79225068306833783835167947146234960509710179000000000000, 0, 0, 0, 63842534391776707803237141499336000000000000000000000000, 0, 63842534391776707803237141499336000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 5 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
