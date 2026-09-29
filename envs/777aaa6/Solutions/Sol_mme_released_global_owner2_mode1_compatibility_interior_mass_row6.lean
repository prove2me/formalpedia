-- Prove2me | solution 1 for mme_released_global_owner2_mode1_compatibility_interior_mass_row6
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T01:51:20.147101+00:00
-- url     : https://prove2.me/submissions/36f0fd77-e6c7-40f8-8197-94514d051b3e

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4358116006365695909887342102772828442113000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146250275341363765640075403646198343115774000000000000000, 0, 0, 0, 0, 0, 213139952700513006202817409209807000000000000000000000000, 0, 213139952295747522335817409209807000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4358115826247557229887342102772828442113000000000000000, 0, 0, 0, 0, 0, 213139952306254413758817409209807000000000000000000000000, 0, 213139952336274103538817409209807000000000000000000000000, 0, 0, 0, 4358114900314671382043926061430965707331004000000000000, 0, 146250244384603279967792423186166068585337992000000000000, 0, 4358114902315984034043926061430965707331004000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 6 then ((alpha 2 s * ((jointRows 2 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
