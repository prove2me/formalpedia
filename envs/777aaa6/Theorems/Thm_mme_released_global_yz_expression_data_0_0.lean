-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_0_0
-- name    : mme_released_global_yz_expression_data_0_0
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:40:03.414055+00:00
-- url     : https://prove2.me/theorems/4be98ff3-f79a-4edd-944e-264b7c191067
-- title:
--   Exact Y entropy arithmetic in orientation 0
-- statement:
--   The exact signed-log expression and rational floor inequality for branch 0 in orientation 0.
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

theorem mme_released_global_yz_expression_data_0_0 :
    ((entries (0 : Fin 6) (0 : Fin 2)).map Prod.fst = prune (rawTerms (0 : Fin 6) (0 : Fin 2))) ∧
    (rateFloor (0 : Fin 6) ≤ totalBound (0 : Fin 6) (0 : Fin 2)) := by
  sorry
