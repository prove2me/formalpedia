-- Prove2me | Theorems.Thm_mme_released_global_rate_floor
-- name    : mme_released_global_rate_floor
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:41:03.022098+00:00
-- url     : https://prove2.me/theorems/42e3e93c-54ae-4463-afb4-62389864aa1f
-- title:
--   Full numerical global rate for all six exact released orientations
-- statement:
--   The full three-way minimum defining the global entropy rate of every exact released orientation is at least its rational rateFloor. The floors are 1.490665312, 1.490664887, 1.490666224, 1.490666463, 1.490663625 and 1.490666061 per original block.
-- source:
--   Numerical global rate of the exact published More Asymmetry candidate. This closes the Y/Z branches and full global rate; whole-interface recursive continuation and the final finite witness remain separate.

import Definitions.Def_mme_released_global_yz_certificate
import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.ReleasedGlobalYZ MME.MoreAsymmetryExactSeed MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
universe u

theorem mme_released_global_rate_floor (o : Fin 6) :
    (rateFloor o : ℝ) ≤ (profile o).rate (fun _ ↦ 1) := by
  sorry
