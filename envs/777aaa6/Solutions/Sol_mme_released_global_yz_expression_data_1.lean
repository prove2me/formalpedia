-- Prove2me | solution 1 for mme_released_global_yz_expression_data_1
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T13:49:51.164059+00:00
-- url     : https://prove2.me/submissions/2962a63b-74ad-43d9-ac40-d151d614db5c

import Theorems.Thm_mme_released_global_yz_expression_data_1_0
import Theorems.Thm_mme_released_global_yz_expression_data_1_1
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    (∀ i, (entries (1 : Fin 6) i).map Prod.fst = prune (rawTerms (1 : Fin 6) i)) ∧
    (∀ i, rateFloor (1 : Fin 6) ≤ totalBound (1 : Fin 6) i) := by
  constructor
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_1_0.1
    · exact mme_released_global_yz_expression_data_1_1.1
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_1_0.2
    · exact mme_released_global_yz_expression_data_1_1.2
