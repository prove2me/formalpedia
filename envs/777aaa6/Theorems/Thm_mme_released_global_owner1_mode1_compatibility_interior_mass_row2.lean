-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode1_compatibility_interior_mass_row2
-- name    : mme_released_global_owner1_mode1_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:08:16.53928+00:00
-- url     : https://prove2.me/theorems/ff4516a7-d297-4692-b69a-527a4fb79e3c
-- title:
--   owner1 mode1 compatibility interior mass row2
-- statement:
--   For owner 1, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode1_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1729090746218829963065782533138162627455489280000000000000, 0, 49753391105555242365588460551991309745089021440000000000000, 0, 1729090746195119352089782533138162627455489280000000000000, 0, 0, 0, 45668208025694161402840999751066515250000000000000000000000, 0, 45668208027115810119276999751066515250000000000000000000000, 0, 0, 0, 0, 0, 1729090536405350912884198739706126807016130545000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45668208026830788816502999751066515250000000000000000000000, 0, 45668208026808066147650999751066515250000000000000000000000, 0, 0, 0, 0, 0, 49753482018855255087755577898054050385967738910000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1729090536321375832344198739706126807016130545000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 2 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
