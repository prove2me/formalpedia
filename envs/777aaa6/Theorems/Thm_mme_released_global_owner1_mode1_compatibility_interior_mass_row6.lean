-- Prove2me | Theorems.Thm_mme_released_global_owner1_mode1_compatibility_interior_mass_row6
-- name    : mme_released_global_owner1_mode1_compatibility_interior_mass_row6
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T01:10:01.658663+00:00
-- url     : https://prove2.me/theorems/08f058c7-87fd-4aab-9438-d9119a169726
-- title:
--   owner1 mode1 compatibility interior mass row6
-- statement:
--   For owner 1, mode 1, and coordinate pool 6, the stated integer table divided by 10^60 equals the sum of the released joint atom masses of each word in the indicated cells. Compatibility interior rows exclude the exact boundary predicate displayed in the statement.
-- source:
--   Exact released rational CW profile and joint atom counts.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner1_mode1_compatibility_interior_mass_row6 : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4360760937131265640686242278045805038633300000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146314781175346275355181113168908389922733400000000000000, 0, 0, 0, 0, 0, 213173521743817170175867407097100000000000000000000000000, 0, 213173521798861936985867407097100000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4360760934128823814686242278045805038633300000000000000, 0, 0, 0, 0, 0, 213173521898943331185867407097100000000000000000000000000, 0, 213173521798361530014867407097100000000000000000000000000, 0, 0, 0, 4360555968395587078321133744916576124923900000000000000, 0, 146305368756602213830334506396766847750152200000000000000, 0, 4360555988411865918321133744916576124923900000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 6 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by sorry
