-- Prove2me | Theorems.Thm_mme_CW_fourth_block_nonzero_of_literal_terms
-- name    : mme_CW_fourth_block_nonzero_of_literal_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:05:07.794484+00:00
-- url     : https://prove2.me/theorems/7708c662-5c83-4de4-9f5d-3876bbae63a2
-- title:
--   A realized literal address gives a nonzero fourth-power block
-- statement:
--   Let four literal monomials of $CW_q$ have fourth-power grade address $\sigma$. Then the $\sigma$-graded block of the literal tensor $CW_q^{\otimes 4}$ is nonzero over every field. A coordinate functional isolates the selected fourfold monomial in the exact literal source expansion; uniqueness of literal term addresses ensures that all other monomials vanish. The theorem is uniform in $q$ and is the source-realization bridge from support combinatorics to actual tensor blocks.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173.

import Definitions.Def_mme_CW_fourth_literal_support_words

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_CW_fourth_block_nonzero_of_literal_terms
    {K : Type u} [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (w₁ w₂ w₃ w₄ : MME.StothersFourth.CWLiteralTerm q)
    (hselected : ∀ s,
      MME.StothersFourth.cwFourthPairGrade q
        (MME.StothersFourth.cwFourthIndexOfLiteralTerms q
          w₁ w₂ w₃ w₄ s) = sigma s) :
    (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma ≠ 0 := by
  sorry
