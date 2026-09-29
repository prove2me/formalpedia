-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_1_1
-- name    : mme_released_global_yz_expression_data_1_1
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:40:15.769864+00:00
-- url     : https://prove2.me/theorems/e5d922f3-b126-451e-89c0-c23fe036448b
-- title:
--   Exact Z entropy arithmetic in orientation 1
-- statement:
--   The exact signed-log expression and rational floor inequality for branch 1 in orientation 1.
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

theorem mme_released_global_yz_expression_data_1_1 :
    ((entries (1 : Fin 6) (1 : Fin 2)).map Prod.fst = prune (rawTerms (1 : Fin 6) (1 : Fin 2))) ∧
    (rateFloor (1 : Fin 6) ≤ totalBound (1 : Fin 6) (1 : Fin 2)) := by
  sorry
