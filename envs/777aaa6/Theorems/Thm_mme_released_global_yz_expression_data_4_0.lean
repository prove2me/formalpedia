-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_4_0
-- name    : mme_released_global_yz_expression_data_4_0
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:41:27.43816+00:00
-- url     : https://prove2.me/theorems/e822891c-c104-4135-9e41-cfc562cc943e
-- title:
--   Exact Y entropy arithmetic in orientation 4
-- statement:
--   The exact signed-log expression and rational floor inequality for branch 0 in orientation 4.
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

theorem mme_released_global_yz_expression_data_4_0 :
    ((entries (4 : Fin 6) (0 : Fin 2)).map Prod.fst = prune (rawTerms (4 : Fin 6) (0 : Fin 2))) ∧
    (rateFloor (4 : Fin 6) ≤ totalBound (4 : Fin 6) (0 : Fin 2)) := by
  sorry
