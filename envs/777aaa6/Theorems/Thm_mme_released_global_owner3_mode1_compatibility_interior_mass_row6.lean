-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode1_compatibility_interior_mass_row6
-- name    : mme_released_global_owner3_mode1_compatibility_interior_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:20:57.866306+00:00
-- url     : https://prove2.me/theorems/c2f052ce-8488-402b-b3d1-28352839819b
-- title:
--   owner3 mode1 compatibility interior mass row6
-- statement:
--   For owner 3, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode1_compatibility_interior_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4350624786646108497815359706874373087389030000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146299164363674570105524004483243253825221940000000000000, 0, 0, 0, 0, 0, 213104098114166053504790237399692000000000000000000000000, 0, 213104098435232834344790237399692000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4350624769642571817815359706874373087389030000000000000, 0, 0, 0, 0, 0, 213104098143172086664790237399692000000000000000000000000, 0, 213104098173678431884790237399692000000000000000000000000, 0, 0, 0, 4351530592087130351793317390823510874549936000000000000, 0, 146340842968100288016097691722592978250900128000000000000, 0, 4351530653599924811793317390823510874549936000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 6 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
