-- Prove2me | solution 1 for mme_released_global_yz_expression_data_5
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T13:56:40.243246+00:00
-- url     : https://prove2.me/submissions/61339f65-2b1a-4379-8e11-cf86166c1211

import Theorems.Thm_mme_released_global_yz_expression_data_5_0
import Theorems.Thm_mme_released_global_yz_expression_data_5_1
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    (∀ i, (entries (5 : Fin 6) i).map Prod.fst = prune (rawTerms (5 : Fin 6) i)) ∧
    (∀ i, rateFloor (5 : Fin 6) ≤ totalBound (5 : Fin 6) i) := by
  constructor
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_5_0.1
    · exact mme_released_global_yz_expression_data_5_1.1
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_5_0.2
    · exact mme_released_global_yz_expression_data_5_1.2
