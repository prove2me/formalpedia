-- Prove2me | solution 1 for mme_omega_strassen_lt_2376
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:02:47.376175+00:00
-- url     : https://prove2.me/submissions/305212d1-8ca8-412c-b92d-b742adada390

import Theorems.Thm_mme_CW_auxiliary_inequality
import Theorems.Thm_mme_CW_endpoint_2376

open MME

universe u

theorem solution {K : Type u} [Field K] :
    matMulExp_strassen K < 297 / 125 := by
  by_cases hsmall : matMulExp_strassen K < 2
  · exact lt_trans hsmall (by norm_num)
  · have homega : 2 ≤ matMulExp_strassen K := le_of_not_gt hsmall
    apply mme_CW_endpoint_2376
    have haux := mme_CW_auxiliary_inequality
      (K := K) 6 (by norm_num) homega
      cw2376_a cw2376_b cw2376_c cw2376_d
      (by norm_num [cw2376_a])
      (by norm_num [cw2376_b])
      (by norm_num [cw2376_c])
      (by norm_num [cw2376_d])
      (by
        norm_num [cw2376_a, cw2376_b, cw2376_c, cw2376_d]
        rfl)
    norm_num at haux
    exact haux
