-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_5_1
-- name    : mme_released_global_yz_expression_data_5_1
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:40:45.183416+00:00
-- url     : https://prove2.me/theorems/83e4a5d6-090a-4eb0-985d-d79e8d482426
-- title:
--   Exact Z entropy arithmetic in orientation 5
-- statement:
--   The exact signed-log expression and rational floor inequality for branch 1 in orientation 5.
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

theorem mme_released_global_yz_expression_data_5_1 :
    ((entries (5 : Fin 6) (1 : Fin 2)).map Prod.fst = prune (rawTerms (5 : Fin 6) (1 : Fin 2))) ∧
    (rateFloor (5 : Fin 6) ≤ totalBound (5 : Fin 6) (1 : Fin 2)) := by
  sorry
