-- Prove2me | solution 1 for mme_released_global_yz_expression_data_0
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:11:32.123161+00:00
-- url     : https://prove2.me/submissions/14054f96-b994-4931-a10a-a8e35f3cb365

import Theorems.Thm_mme_released_global_yz_expression_data_0_0
import Theorems.Thm_mme_released_global_yz_expression_data_0_1
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    (∀ i, (entries (0 : Fin 6) i).map Prod.fst = prune (rawTerms (0 : Fin 6) i)) ∧
    (∀ i, rateFloor (0 : Fin 6) ≤ totalBound (0 : Fin 6) i) := by
  constructor
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_0_0.1
    · exact mme_released_global_yz_expression_data_0_1.1
  · intro i
    fin_cases i
    · exact mme_released_global_yz_expression_data_0_0.2
    · exact mme_released_global_yz_expression_data_0_1.2
