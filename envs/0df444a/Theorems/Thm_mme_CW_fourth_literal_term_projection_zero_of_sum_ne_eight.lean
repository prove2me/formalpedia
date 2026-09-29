-- Prove2me | Theorems.Thm_mme_CW_fourth_literal_term_projection_zero_of_sum_ne_eight
-- name    : mme_CW_fourth_literal_term_projection_zero_of_sum_ne_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:02:58.057616+00:00
-- url     : https://prove2.me/theorems/4a1e8c98-6e04-4108-a669-40cd66bb5a1b
-- title:
--   Unsupported fourth-power grades kill every literal CW word
-- statement:
--   Every literal monomial of $CW_q$ has total coordinate grade two, hence every literal word in $CW_q^{\otimes 4}$ has total grade eight. For any requested three-mode grade address whose entries do not sum to eight, at least one coordinate block projection therefore kills the word, so its full graded projection is zero. The result is uniform in the field and the CW parameter.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173.

import Definitions.Def_mme_CW_fourth_literal_support_words
import Definitions.Def_mme_TypeGrading_kron

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_CW_fourth_literal_term_projection_zero_of_sum_ne_eight
    {K : Type u} [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) ≠ 8)
    (t₁ t₂ t₃ t₄ : MME.StothersFourth.CWLiteralTerm q) :
    PiTensorProduct.map
        (fun s => (MME.StothersFourth.cwFourthCanonicalGrading K q).blockProj
          s (sigma s))
        (MME.interchange
          (MME.interchange
            (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
            (MME.StothersFourth.cwLiteralTermMonomial K q t₂))
          (MME.interchange
            (MME.StothersFourth.cwLiteralTermMonomial K q t₃)
            (MME.StothersFourth.cwLiteralTermMonomial K q t₄))) = 0 := by
  sorry
