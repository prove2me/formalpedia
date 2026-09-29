-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_data_2
-- name    : mme_released_global_yz_expression_data_2
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:23:09.78483+00:00
-- url     : https://prove2.me/theorems/30e92e9d-a331-4aa3-b3e7-1337186c04f5
-- title:
--   Exact Y/Z entropy expression data in orientation 2
-- statement:
--   For orientation 2, the certificate terms equal the actual rational mass-entropy expressions and their rational bounds exceed the existing numerical floor.
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

theorem mme_released_global_yz_expression_data_2 :
    (∀ i, (entries (2 : Fin 6) i).map Prod.fst = prune (rawTerms (2 : Fin 6) i)) ∧
    (∀ i, rateFloor (2 : Fin 6) ≤ totalBound (2 : Fin 6) i) := by
  sorry
