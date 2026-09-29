-- Prove2me | solution 1 for mme_released_global_owner1_mode1_compatibility_interior_mass_row6
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T01:16:11.349795+00:00
-- url     : https://prove2.me/submissions/0186d928-5776-4dce-ae5b-0695ba086b13

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4360760937131265640686242278045805038633300000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146314781175346275355181113168908389922733400000000000000, 0, 0, 0, 0, 0, 213173521743817170175867407097100000000000000000000000000, 0, 213173521798861936985867407097100000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4360760934128823814686242278045805038633300000000000000, 0, 0, 0, 0, 0, 213173521898943331185867407097100000000000000000000000000, 0, 213173521798361530014867407097100000000000000000000000000, 0, 0, 0, 4360555968395587078321133744916576124923900000000000000, 0, 146305368756602213830334506396766847750152200000000000000, 0, 4360555988411865918321133744916576124923900000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 6 then ((alpha 1 s * ((jointRows 1 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
