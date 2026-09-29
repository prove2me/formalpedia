-- Prove2me | solution 1 for mme_stothers_fourth_block_zero_of_grade_sum_ne_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:05:59.600933+00:00
-- url     : https://prove2.me/submissions/3e83aff3-978a-4db1-81bc-3e61a5820b85

import Theorems.Thm_mme_CW_fourth_block_zero_of_grade_sum_ne_eight

open BigOperators

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) ≠ 8) :
    (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma = 0 := by
  exact mme_CW_fourth_block_zero_of_grade_sum_ne_eight 6 sigma hsum
