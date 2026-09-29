-- Prove2me | Theorems.Thm_mme_released_global_owner5_mode2_compatibility_interior_mass_row2
-- name    : mme_released_global_owner5_mode2_compatibility_interior_mass_row2
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T03:27:49.660139+00:00
-- url     : https://prove2.me/theorems/e2436e00-6675-4cb0-86d4-215260751a15
-- title:
--   owner5 mode2 compatibility interior mass row2
-- statement:
--   For owner 5, mode 2, and coordinate pool 2, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_mode2_compatibility_interior_mass_row2 : ∀ w : Word,
    ((([0, 0, 1610782493675636327792707121468465917928857311000000000000, 0, 49965779782334846527189981405413447164142285378000000000000, 0, 1610782493675636327792707121468465917928857311000000000000, 0, 0, 0, 45619458612791747380669723529449118250000000000000000000000, 0, 45619458612791747380669723529449118250000000000000000000000, 0, 0, 0, 0, 0, 1610783757799921803127506798688765653799024032000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45619458612791747380669723529449118250000000000000000000000, 0, 45619458612791747380669723529449118250000000000000000000000, 0, 0, 0, 0, 0, 49965814766547047688290696636475616692401951936000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1610783757799921803127506798688765653799024032000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 2 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
