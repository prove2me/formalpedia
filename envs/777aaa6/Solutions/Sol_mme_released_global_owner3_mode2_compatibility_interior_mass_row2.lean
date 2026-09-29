-- Prove2me | solution 1 for mme_released_global_owner3_mode2_compatibility_interior_mass_row2
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T02:33:02.318338+00:00
-- url     : https://prove2.me/submissions/2b921193-2a97-466d-a077-86f8fc3a6b09

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 1613178942914795024968910149129944975438504504000000000000, 0, 49961402837786031109676279755872920049122990992000000000000, 0, 1613178942914795024968910149129944975438504504000000000000, 0, 0, 0, 45618886353341509609068735568484452250000000000000000000000, 0, 45618886353341509609068735568484452250000000000000000000000, 0, 0, 0, 0, 0, 1613179403814663172599459339213102058490639908000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45618886353341509609068735568484452250000000000000000000000, 0, 45618886353341509609068735568484452250000000000000000000000, 0, 0, 0, 0, 0, 49961396539389014058912038993503176883018720184000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1613179403814663172599459339213102058490639908000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 2 then ((alpha 3 s * ((jointRows 3 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
