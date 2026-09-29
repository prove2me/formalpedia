-- Prove2me | solution 1 for mme_released_global_rate_floor
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:17:23.024748+00:00
-- url     : https://prove2.me/submissions/642e938b-477d-422d-963d-d9c6e7681e17

import Definitions.Def_mme_released_global_yz_certificate
import Theorems.Thm_mme_released_global_x_rate_floor
import Theorems.Thm_mme_released_global_yz_rate_floor
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.GlobalCW MME.RecursiveYZ
set_option autoImplicit false
set_option maxRecDepth 3000
attribute [local irreducible] profile rateFloor

theorem solution (o : Fin 6) :
    (rateFloor o : ℝ) ≤ (profile o).rate (fun _ ↦ 1) := by
  unfold EntropyProfile.rate
  simp only [Fin.sum_univ_one,one_mul]
  exact le_min (mme_released_global_x_rate_floor o)
    (le_min (mme_released_global_yz_rate_floor o 0) (mme_released_global_yz_rate_floor o 1))
