-- Prove2me | solution 1 for mme_released_global_yz_expression_data_0_0
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:08:29.142606+00:00
-- url     : https://prove2.me/submissions/d75dcdca-695b-4a4c-bddf-35623e1466d0

import Theorems.Thm_mme_released_global_yz_expression_terms_0_0
import Theorems.Thm_mme_released_global_yz_expression_floor_0_0
open BigOperators MME MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    ((entries (0 : Fin 6) (0 : Fin 2)).map Prod.fst = prune (rawTerms (0 : Fin 6) (0 : Fin 2))) ∧
    (rateFloor (0 : Fin 6) ≤ totalBound (0 : Fin 6) (0 : Fin 2)) := by
  exact ⟨mme_released_global_yz_expression_terms_0_0,
    mme_released_global_yz_expression_floor_0_0⟩
