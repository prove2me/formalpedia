-- Prove2me | solution 1 for mme_released_global_yz_expression_data_2_1
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:08:30.908043+00:00
-- url     : https://prove2.me/submissions/3ad92c72-adc0-4d89-bf74-df789ad16be4

import Theorems.Thm_mme_released_global_yz_expression_terms_2_1
import Theorems.Thm_mme_released_global_yz_expression_floor_2_1
open BigOperators MME MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    ((entries (2 : Fin 6) (1 : Fin 2)).map Prod.fst = prune (rawTerms (2 : Fin 6) (1 : Fin 2))) ∧
    (rateFloor (2 : Fin 6) ≤ totalBound (2 : Fin 6) (1 : Fin 2)) := by
  exact ⟨mme_released_global_yz_expression_terms_2_1,
    mme_released_global_yz_expression_floor_2_1⟩
