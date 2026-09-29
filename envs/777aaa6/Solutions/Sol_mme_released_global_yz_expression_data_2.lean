-- Prove2me | solution 1 for mme_released_global_yz_expression_data_2
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:10:58.848302+00:00
-- url     : https://prove2.me/submissions/b7c01d73-eb3f-49d2-8e5f-63b717c14ff7

import Theorems.Thm_mme_released_global_yz_expression_data_2_0
import Theorems.Thm_mme_released_global_yz_expression_data_2_1
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    (∀ i, (entries (2 : Fin 6) i).map Prod.fst = prune (rawTerms (2 : Fin 6) i)) ∧
    (∀ i, rateFloor (2 : Fin 6) ≤ totalBound (2 : Fin 6) i) := by
  constructor
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_2_0.1
    · exact mme_released_global_yz_expression_data_2_1.1
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_2_0.2
    · exact mme_released_global_yz_expression_data_2_1.2
