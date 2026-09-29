-- Prove2me | solution 1 for mme_released_global_yz_expression_data_2_0
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:07:33.816568+00:00
-- url     : https://prove2.me/submissions/e0e50a47-b3b6-4c22-8579-d8c08d90fac8

import Theorems.Thm_mme_released_global_yz_expression_terms_2_0
import Theorems.Thm_mme_released_global_yz_expression_floor_2_0
open BigOperators MME MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    ((entries (2 : Fin 6) (0 : Fin 2)).map Prod.fst = prune (rawTerms (2 : Fin 6) (0 : Fin 2))) ∧
    (rateFloor (2 : Fin 6) ≤ totalBound (2 : Fin 6) (0 : Fin 2)) := by
  exact ⟨mme_released_global_yz_expression_terms_2_0,
    mme_released_global_yz_expression_floor_2_0⟩
