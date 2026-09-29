-- Prove2me | Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms
-- name    : mme_CW_fourth_tensor_eq_sum_literal_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:01:36.391298+00:00
-- url     : https://prove2.me/theorems/64b4ec4e-96e5-4ca5-b2ec-a46ff9146e07
-- title:
--   Literal fourfold expansion of the fourth CW power
-- statement:
--   For every field $K$ and parameter $q$, the literal parenthesized tensor $CW_q^{\otimes 4}$ equals the fourfold finite sum obtained by choosing one literal CW monomial in each factor and applying the mode-wise interchange maps. This equality fixes the exact source realization and parenthesization used by the fourth-power grading. It is parameter-uniform and therefore shared by the Davie--Stothers and DWZ fourth-power analyses.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173.

import Theorems.Thm_mme_CWTensor_eq_sum_literal_terms
import Definitions.Def_mme_CW_fourth_literal_support_words

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_CW_fourth_tensor_eq_sum_literal_terms
    (K : Type u) [Field K] (q : ℕ) :
    (MME.StothersFourth.cwFourthObj K q).t =
      ∑ t₄ : MME.StothersFourth.CWLiteralTerm q,
      ∑ t₃ : MME.StothersFourth.CWLiteralTerm q,
      ∑ t₂ : MME.StothersFourth.CWLiteralTerm q,
      ∑ t₁ : MME.StothersFourth.CWLiteralTerm q,
        MME.interchange
          (MME.interchange
            (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
            (MME.StothersFourth.cwLiteralTermMonomial K q t₂))
          (MME.interchange
            (MME.StothersFourth.cwLiteralTermMonomial K q t₃)
            (MME.StothersFourth.cwLiteralTermMonomial K q t₄)) := by
  sorry
