-- Prove2me | solution 1 for mme_omega_strassen_lt_2375477
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:20:05.858304+00:00
-- url     : https://prove2.me/submissions/34623100-cdb0-4cc4-9dc5-6173a72f645e

import Theorems.Thm_mme_CW_auxiliary_inequality_2376_profile
import Theorems.Thm_mme_CW_auxiliary_numeric_2375477
import Theorems.Thm_mme_CW_endpoint_of_numeric_certificate

open MME

universe u

theorem solution {K : Type u} [Field K] :
    matMulExp_strassen K < 2375477 / 1000000 := by
  by_cases hsmall : matMulExp_strassen K < 2
  · exact lt_trans hsmall (by norm_num)
  · have homega : 2 ≤ matMulExp_strassen K := le_of_not_gt hsmall
    apply mme_CW_endpoint_of_numeric_certificate
        (2375477 / 1000000) (matMulExp_strassen K)
    · norm_num
      exact mme_CW_auxiliary_numeric_2375477
    · exact mme_CW_auxiliary_inequality_2376_profile homega
