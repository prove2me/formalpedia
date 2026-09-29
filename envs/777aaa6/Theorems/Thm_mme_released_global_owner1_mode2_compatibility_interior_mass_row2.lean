-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode2_compatibility_interior_mass_row2
-- name    : mme_released_global_owner1_mode2_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:11:01.766519+00:00
-- url     : https://prove2.me/theorems/9e588da3-5948-4428-9fe5-66eb06f00c12
-- title:
--   owner1 mode2 compatibility interior mass row2
-- statement:
--   For owner 1, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode2_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1610294628607218766189709290710097969999204400000000000000, 0, 49968517636619449577900804450957180060001591200000000000000, 0, 1610294628607218766189709290710097969999204400000000000000, 0, 0, 0, 45618231445831669821199793825936122500000000000000000000000, 0, 45618231445831669821199793825936122500000000000000000000000, 0, 0, 0, 0, 0, 1610294446066665741451539166063664068321683664000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45618231445831669821199793825936122500000000000000000000000, 0, 45618231445831669821199793825936122500000000000000000000000, 0, 0, 0, 0, 0, 49968518449706102122017523331750805863356632672000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1610294446066665741451539166063664068321683664000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 2 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
