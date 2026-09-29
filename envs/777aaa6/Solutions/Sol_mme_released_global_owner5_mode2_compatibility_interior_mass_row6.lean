-- Prove2me | solution 1 for mme_released_global_owner5_mode2_compatibility_interior_mass_row6
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T03:38:31.388174+00:00
-- url     : https://prove2.me/submissions/0ad9e5db-db04-4e9c-b3ee-e91a769966fa

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

/-- The released rational table agrees with the joint atom masses. -/
theorem solution : ∀ w : Word,
    ((([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 309532742359929968527589969464096013569000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75284539270974885052614011053837071807972862000000000000, 0, 0, 0, 0, 0, 126815582123756006844479657428947250000000000000000000000, 0, 126815582123756006844479657428947250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 309532742359929968527589969464096013569000000000000, 0, 0, 0, 0, 0, 126815582123756006844479657428947250000000000000000000000, 0, 126815582123756006844479657428947250000000000000000000000, 0, 0, 0, 309364075425058099319644288439707525708000000000000, 0, 75244301440365517593331664761858120584948584000000000000, 0, 309364075425058099319644288439707525708000000000000, 0, 0] : List ℕ).getD (27 * (w 0).val + 9 * (w 1).val + 3 * (w 2).val + (w 3).val) 0 : ℕ) : ℚ) / 1000000000000000000000000000000000000000000000000000000000000 =
    ∑ s : Fin 45, if ¬ (((shape s).val 0).val = 0 ∨ ((shape s).val 1).val = 0) ∧ (shape s).val 2 = 6 then ((alpha 5 s * ((jointRows 5 s).map (fun a => if atom a.1 2 = w then a.2 else 0)).sum : ℕ) : ℚ) / (denominator : ℚ) ^ 5 else 0 := by
  decide +kernel

#print axioms solution
