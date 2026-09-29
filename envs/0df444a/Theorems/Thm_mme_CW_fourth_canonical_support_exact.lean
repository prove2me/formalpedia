-- Prove2me | Theorems.Thm_mme_CW_fourth_canonical_support_exact
-- name    : mme_CW_fourth_canonical_support_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:05:46.074617+00:00
-- url     : https://prove2.me/theorems/14642135-dc33-45dd-94bc-66ebf7e941ff
-- title:
--   Exact support of the canonical fourth CW power
-- statement:
--   Let $K$ be any field and let $q>0$, witnessed by a chosen middle coordinate of $CW_q$. In the canonical nine-grading of the literal fourth power $CW_q^{\otimes 4}$, a block at address $(a,b,c)$ vanishes exactly when $a+b+c\ne8$. Thus the support consists precisely of the 45 ordered nonnegative triples of total degree eight. The statement is uniform in $q$ and supplies the common exact-support theorem for the q=6 Davie--Stothers and q=5 DWZ sources.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173.

import Definitions.Def_mme_CW_fourth_literal_support_words

open BigOperators

universe u

set_option autoImplicit false

theorem mme_CW_fourth_canonical_support_exact
    {K : Type u} [Field K] (q : ℕ) (i : Fin q) :
    ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma = 0 ↔
        (∑ s, (sigma s).val) ≠ 8 := by
  sorry
