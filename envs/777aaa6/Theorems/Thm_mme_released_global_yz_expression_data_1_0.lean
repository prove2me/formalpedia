-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_1_0
-- name    : mme_released_global_yz_expression_data_1_0
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:39:36.763501+00:00
-- url     : https://prove2.me/theorems/874d15b4-d7a3-4257-81cf-0e3ad8f320d5
-- title:
--   Exact Y entropy arithmetic in orientation 1
-- statement:
--   The exact signed-log expression and rational floor inequality for branch 0 in orientation 1.
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

theorem mme_released_global_yz_expression_data_1_0 :
    ((entries (1 : Fin 6) (0 : Fin 2)).map Prod.fst = prune (rawTerms (1 : Fin 6) (0 : Fin 2))) ∧
    (rateFloor (1 : Fin 6) ≤ totalBound (1 : Fin 6) (0 : Fin 2)) := by
  sorry
