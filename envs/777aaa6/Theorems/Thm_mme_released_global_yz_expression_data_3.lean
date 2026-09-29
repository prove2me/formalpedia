-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_3
-- name    : mme_released_global_yz_expression_data_3
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:22:59.842612+00:00
-- url     : https://prove2.me/theorems/7cd30882-bd6b-4f8a-8cae-e4dcffa666fe
-- title:
--   Exact Y/Z entropy expression data in orientation 3
-- statement:
--   For orientation 3, the certificate terms equal the actual rational mass-entropy expressions and their rational bounds exceed the existing numerical floor.
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

theorem mme_released_global_yz_expression_data_3 :
    (∀ i, (entries (3 : Fin 6) i).map Prod.fst = prune (rawTerms (3 : Fin 6) i)) ∧
    (∀ i, rateFloor (3 : Fin 6) ≤ totalBound (3 : Fin 6) i) := by
  sorry
