-- Prove2me | Theorems.Thm_mme_stothers_fourth_block_nonzero_of_grade_sum_eight
-- name    : mme_stothers_fourth_block_nonzero_of_grade_sum_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:16:18.752733+00:00
-- url     : https://prove2.me/theorems/59b670fd-ea71-4ba9-993c-0884e904bf3a
-- title:
--   Every sum-eight canonical fourth-power block is nonzero
-- statement:
--   Let $K$ be any field and give the literal tensor $CW_6^{\otimes4}$ its canonical nine-grading. Every ordered grade triple $\sigma=(i,j,k)$ satisfying $i+j+k=8$ is realized by a fourth-power source monomial, and the corresponding graded block is nonzero. The assertion is literal nonvanishing over an arbitrary field, not just a combinatorial enumeration of possible grade triples.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, paragraph preceding Lemma 5.1, printed p. 363, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_fourth_block_nonzero_of_grade_sum_eight
    {K : Type u} [Field K]
    (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) = 8) :
    (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 := by
  sorry
