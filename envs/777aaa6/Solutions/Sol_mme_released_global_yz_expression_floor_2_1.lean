-- Prove2me | solution 1 for mme_released_global_yz_expression_floor_2_1
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:03:12.619073+00:00
-- url     : https://prove2.me/submissions/2f139414-41f0-4275-aedd-431f35b0dc3e

import Definitions.Def_mme_released_global_yz_certificate
open BigOperators MME MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem solution :
    rateFloor (2 : Fin 6) ≤ totalBound (2 : Fin 6) (1 : Fin 2) := by
  decide +kernel
