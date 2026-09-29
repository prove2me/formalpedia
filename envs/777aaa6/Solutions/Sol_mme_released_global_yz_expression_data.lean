-- Prove2me | solution 1 for mme_released_global_yz_expression_data
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:14:15.654984+00:00
-- url     : https://prove2.me/submissions/b9bdbcce-8ad2-45f1-afe8-fd7efdc43dd3

import Theorems.Thm_mme_released_global_yz_expression_data_0
import Theorems.Thm_mme_released_global_yz_expression_data_1
import Theorems.Thm_mme_released_global_yz_expression_data_2
import Theorems.Thm_mme_released_global_yz_expression_data_3
import Theorems.Thm_mme_released_global_yz_expression_data_4
import Theorems.Thm_mme_released_global_yz_expression_data_5
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    (∀ o i, (entries o i).map Prod.fst = prune (rawTerms o i)) ∧
    (∀ o i, rateFloor o ≤ totalBound o i) := by
  constructor
  · intro o i
    fin_cases o
    · exact mme_released_global_yz_expression_data_0.1 i
    · exact mme_released_global_yz_expression_data_1.1 i
    · exact mme_released_global_yz_expression_data_2.1 i
    · exact mme_released_global_yz_expression_data_3.1 i
    · exact mme_released_global_yz_expression_data_4.1 i
    · exact mme_released_global_yz_expression_data_5.1 i
  · intro o i
    fin_cases o
    · exact mme_released_global_yz_expression_data_0.2 i
    · exact mme_released_global_yz_expression_data_1.2 i
    · exact mme_released_global_yz_expression_data_2.2 i
    · exact mme_released_global_yz_expression_data_3.2 i
    · exact mme_released_global_yz_expression_data_4.2 i
    · exact mme_released_global_yz_expression_data_5.2 i
