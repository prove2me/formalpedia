-- Prove2me | solution 1 for mme_stothers_fourth_block_support_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:24:14.091673+00:00
-- url     : https://prove2.me/submissions/0f499a4e-1d2c-4941-ac0c-e28fb08c9f13

import Theorems.Thm_mme_stothers_fourth_block_zero_of_grade_sum_ne_eight
import Theorems.Thm_mme_stothers_fourth_block_nonzero_of_grade_sum_eight

open MME BigOperators

universe u


set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] :
    ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma = 0 ↔
        (∑ s, (sigma s).val) ≠ 8 := by
  intro sigma
  constructor
  · intro hzero hsum
    exact mme_stothers_fourth_block_nonzero_of_grade_sum_eight
      sigma hsum hzero
  · exact mme_stothers_fourth_block_zero_of_grade_sum_ne_eight sigma
