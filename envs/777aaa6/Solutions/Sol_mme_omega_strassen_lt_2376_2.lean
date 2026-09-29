-- Prove2me | solution 2 for mme_omega_strassen_lt_2376
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:52:54.05205+00:00
-- url     : https://prove2.me/submissions/d40c38d9-c582-46ab-a5df-87823c75fd50

import Theorems.Thm_mme_CW_auxiliary_inequality_2376_profile
import Theorems.Thm_mme_CW_endpoint_2376

open MME

universe u

theorem solution {K : Type u} [Field K] :
    matMulExp_strassen K < 297 / 125 := by
  by_cases hsmall : matMulExp_strassen K < 2
  · exact lt_trans hsmall (by norm_num)
  · have homega : 2 ≤ matMulExp_strassen K := le_of_not_gt hsmall
    exact mme_CW_endpoint_2376 _
      (mme_CW_auxiliary_inequality_2376_profile (K := K) homega)
