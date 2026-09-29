-- Prove2me | solution 1 for mme_released_global_yz_expression_data_4
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T13:52:46.11467+00:00
-- url     : https://prove2.me/submissions/c74028fb-b3d0-4de6-8a6a-8eb371ad0ea9

import Theorems.Thm_mme_released_global_yz_expression_data_4_0
import Theorems.Thm_mme_released_global_yz_expression_data_4_1
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    (∀ i, (entries (4 : Fin 6) i).map Prod.fst = prune (rawTerms (4 : Fin 6) i)) ∧
    (∀ i, rateFloor (4 : Fin 6) ≤ totalBound (4 : Fin 6) i) := by
  constructor
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_4_0.1
    · exact mme_released_global_yz_expression_data_4_1.1
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_4_0.2
    · exact mme_released_global_yz_expression_data_4_1.2
