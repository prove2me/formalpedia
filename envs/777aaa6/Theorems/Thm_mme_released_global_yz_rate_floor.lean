-- Prove2me | Theorems.Thm_mme_released_global_yz_rate_floor
-- name    : mme_released_global_yz_rate_floor
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:40:44.41284+00:00
-- url     : https://prove2.me/theorems/7ac1321a-8547-4903-9e3c-c689aa1a9f8a
-- title:
--   Numerical global Y/Z-rate floors for all six exact released orientations
-- statement:
--   Each Y/Z branch of the exact published ReleasedGlobal.profile is at least its existing rational rateFloor, with no additional numerical hypotheses.
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

theorem mme_released_global_yz_rate_floor (o : Fin 6) (i : Fin 2) :
    (rateFloor o : ℝ) ≤ (profile o).coarse (yzMode i) 0 +
      (profile o).words (yzMode i) 0 - (profile o).compat i 0 := by
  sorry
