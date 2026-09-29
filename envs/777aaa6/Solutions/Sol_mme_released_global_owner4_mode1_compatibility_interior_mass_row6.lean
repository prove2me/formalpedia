-- Prove2me | solution 1 for mme_released_global_owner4_mode1_compatibility_interior_mass_row6
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T03:03:34.819321+00:00
-- url     : https://prove2.me/submissions/2b21bcbe-67c5-400f-90b8-443c16e00423

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4359992709295373324732149251037045209570336000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146213953264555396092113155691877909580859328000000000000, 0, 0, 0, 0, 0, 213159900700770152877900103268676000000000000000000000000, 0, 213159900902895727389900103268676000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4359992673773304536732149251037045209570336000000000000, 0, 0, 0, 0, 0, 213159900686261138865900103268676000000000000000000000000, 0, 213159900677255543961900103268676000000000000000000000000, 0, 0, 0, 4359992508088525030057184188786573142526528000000000000, 0, 146213949369516623718707764353770853714946944000000000000, 0, 4359992507588214202057184188786573142526528000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 2).val = 0) ∧ (shape s).val 1 = 6 then ((alpha 4 s * ((jointRows 4 s).map (fun a => if atom a.1 1 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
