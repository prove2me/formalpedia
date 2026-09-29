-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_5
-- name    : mme_released_global_yz_expression_data_5
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:23:10.967985+00:00
-- url     : https://prove2.me/theorems/ec914497-0c75-454b-aacc-8188f1d9fbb9
-- title:
--   Exact Y/Z entropy expression data in orientation 5
-- statement:
--   For orientation 5, the certificate terms equal the actual rational mass-entropy expressions and their rational bounds exceed the existing numerical floor.
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

theorem mme_released_global_yz_expression_data_5 :
    (∀ i, (entries (5 : Fin 6) i).map Prod.fst = prune (rawTerms (5 : Fin 6) i)) ∧
    (∀ i, rateFloor (5 : Fin 6) ≤ totalBound (5 : Fin 6) i) := by
  sorry
