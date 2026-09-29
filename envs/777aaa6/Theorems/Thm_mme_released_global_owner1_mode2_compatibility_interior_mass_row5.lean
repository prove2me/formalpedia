-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode2_compatibility_interior_mass_row5
-- name    : mme_released_global_owner1_mode2_compatibility_interior_mass_row5
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:11:56.794653+00:00
-- url     : https://prove2.me/theorems/79bb005c-be27-4127-b7bd-39dbdef4644b
-- title:
--   owner1 mode2 compatibility interior mass row5
-- statement:
--   For owner 1, mode 2, and coordinate pool 5, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode2_compatibility_interior_mass_row5 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63856717070797258681349768836201000000000000000000000000, 0, 0, 0, 0, 0, 79225130803925297916483151095865513585797538000000000000, 0, 79225130803925297916483151095865513585797538000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63856717070797258681349768836201000000000000000000000000, 0, 0, 0, 0, 0, 4608734718860138838722826079918973972828404924000000000000, 0, 4608734718860138838722826079918973972828404924000000000000, 0, 0, 0, 79225129561595079235613310938260192731306374000000000000, 0, 4608734675080391247847867133637239614537387252000000000000, 0, 79225129561595079235613310938260192731306374000000000000, 0, 0, 0, 0, 0, 0, 0, 79225130803925297916483151095865513585797538000000000000, 0, 79225130803925297916483151095865513585797538000000000000, 0, 0, 0, 79225129561595079235613310938260192731306374000000000000, 0, 4608734675080391247847867133637239614537387252000000000000, 0, 79225129561595079235613310938260192731306374000000000000, 0, 0, 0, 63856839757631900443764093539334000000000000000000000000, 0, 63856839757631900443764093539334000000000000000000000000, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 5 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
