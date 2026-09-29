-- Prove2me | Theorems.Thm_mme_released_global_yz_expression_terms_2_0
-- name    : mme_released_global_yz_expression_terms_2_0
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T14:02:20.234688+00:00
-- url     : https://prove2.me/theorems/59dbedfa-4f09-4808-9965-428d8e7569d2
-- title:
--   Exact terms certificate for orientation 2, branch 0
-- statement:
--   The stored signed logarithm terms equal the pruned exact rational entropy expression.
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

theorem mme_released_global_yz_expression_terms_2_0 :
    (entries (2 : Fin 6) (0 : Fin 2)).map Prod.fst =
      prune (rawTerms (2 : Fin 6) (0 : Fin 2)) := by
  sorry
