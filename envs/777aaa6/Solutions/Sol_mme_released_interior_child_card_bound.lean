-- Prove2me | solution 1 for mme_released_interior_child_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:14:44.215993+00:00
-- url     : https://prove2.me/submissions/2a19f990-9cb5-4eca-acb7-2f9f7c8c0e9e

import Definitions.Def_mme_released_interior_integer_profiles

open MME MME.ReleasedInterior MME.RecursiveYZ

/-- Each released parent has at most ninety region-labeled child cells, so a
uniform per-child error gives a bounded total error under any partition. -/
theorem solution (s : Fin 45) :
    Fintype.card (Cell 4 6 (parent s)) ≤ 90 := by
  revert s
  decide +kernel


#print axioms solution
