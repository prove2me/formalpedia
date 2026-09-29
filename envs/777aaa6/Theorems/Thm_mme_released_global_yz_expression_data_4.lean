-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_4
-- name    : mme_released_global_yz_expression_data_4
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:22:14.714986+00:00
-- url     : https://prove2.me/theorems/9aa82373-989b-474c-82c9-c23a95cadec3
-- title:
--   Exact Y/Z entropy expression data in orientation 4
-- statement:
--   For orientation 4, the certificate terms equal the actual rational mass-entropy expressions and their rational bounds exceed the existing numerical floor.
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

theorem mme_released_global_yz_expression_data_4 :
    (∀ i, (entries (4 : Fin 6) i).map Prod.fst = prune (rawTerms (4 : Fin 6) i)) ∧
    (∀ i, rateFloor (4 : Fin 6) ≤ totalBound (4 : Fin 6) i) := by
  sorry
