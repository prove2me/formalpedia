-- Prove2me | solution 1 for mme_released_global_yz_expression_floor_0_0
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:03:45.214583+00:00
-- url     : https://prove2.me/submissions/d019aecd-c04a-4a83-b9d4-d3240856b008

import Definitions.Def_mme_released_global_yz_certificate
open BigOperators MME MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem solution :
    rateFloor (0 : Fin 6) ≤ totalBound (0 : Fin 6) (0 : Fin 2) := by
  decide +kernel
