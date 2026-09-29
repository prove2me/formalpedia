-- Prove2me | Theorems.Thm_mme_stothers_fourth_block_zero_of_grade_sum_ne_eight
-- name    : mme_stothers_fourth_block_zero_of_grade_sum_ne_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:16:12.863099+00:00
-- url     : https://prove2.me/theorems/0015e307-e922-4c8a-9ec9-e06168c4f98f
-- title:
--   Unsupported canonical fourth-power blocks vanish
-- statement:
--   Let $K$ be any field and give the literal tensor $CW_6^{\otimes4}$ its canonical nine-grading. If an ordered grade triple $\sigma=(i,j,k)$ does not satisfy $i+j+k=8$, then the corresponding graded block is zero. Each monomial of one Coppersmith--Winograd tensor has total grade two, so each monomial of the fourth power has total grade eight; a projection onto any other total grade kills every source monomial.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, paragraph preceding Lemma 5.1, printed p. 363, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fourth_block_zero_of_grade_sum_ne_eight
    {K : Type u} [Field K]
    (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) ≠ 8) :
    (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma = 0 := by
  sorry
