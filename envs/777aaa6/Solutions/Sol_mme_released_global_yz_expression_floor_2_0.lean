-- Prove2me | solution 1 for mme_released_global_yz_expression_floor_2_0
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:02:44.398523+00:00
-- url     : https://prove2.me/submissions/8e036103-ed82-487f-9ee0-18bc3ce74ed5

import Definitions.Def_mme_released_global_yz_certificate
open BigOperators MME MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem solution :
    rateFloor (2 : Fin 6) ≤ totalBound (2 : Fin 6) (0 : Fin 2) := by
  decide +kernel
