-- Prove2me | Theorems.Thm_mme_released_global_owner4_mode1_compatibility_interior_mass_row2
-- name    : mme_released_global_owner4_mode1_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:55:29.179982+00:00
-- url     : https://prove2.me/theorems/c09667a6-ceeb-4081-b67f-ac10c851070d
-- title:
--   owner4 mode1 compatibility interior mass row2
-- statement:
--   For owner 4, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_mode1_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1726850939633455749523504141764261459762202400000000000000, 0, 49757426175155600501114546657393516080475595200000000000000, 0, 1726850939717906322523504141764261459762202400000000000000, 0, 0, 0, 45668595857373627993923727825301639000000000000000000000000, 0, 45668595857106941973923727825301639000000000000000000000000, 0, 0, 0, 0, 0, 1726851221041703619013368574732504761970680308000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45668595857160279177923727825301639000000000000000000000000, 0, 45668595857632906068923727825301639000000000000000000000000, 0, 0, 0, 0, 0, 49757511470099329112116796608406395476058639384000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1726851221078249481013368574732504761970680308000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 2 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
