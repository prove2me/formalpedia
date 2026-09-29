-- Prove2me | Theorems.Thm_mme_released_global_owner3_mode1_compatibility_interior_mass_row2
-- name    : mme_released_global_owner3_mode1_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T02:18:42.826453+00:00
-- url     : https://prove2.me/theorems/6dca5e3a-4d8a-4eae-909b-79e1ea12a9a8
-- title:
--   owner3 mode1 compatibility interior mass row2
-- statement:
--   For owner 3, mode 1, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner3_mode1_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1729206353498571338410896972423236431105109627000000000000, 0, 49750768973320694804126072258408819137789780746000000000000, 0, 1729206353499559208250896972423236431105109627000000000000, 0, 0, 0, 45669169960288157657442347465501188000000000000000000000000, 0, 45669169959838182945322347465501188000000000000000000000000, 0, 0, 0, 0, 0, 1729206153421566124280395730048606443595973564000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45669169960192828217882347465501188000000000000000000000000, 0, 45669169959902394484922347465501188000000000000000000000000, 0, 0, 0, 0, 0, 49750773191807137974201952474642743112808052872000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1729206153230907245160395730048606443595973564000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 2 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
