-- Prove2me | Theorems.Thm_mme_CW_square_tensor_eq_sum_literal_terms
-- name    : mme_CW_square_tensor_eq_sum_literal_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:11:24.257307+00:00
-- url     : https://prove2.me/theorems/5248c5a4-984a-4854-b5a3-5a0443872bcb
-- title:
--   Literal double-sum expansion of the CW square
-- statement:
--   For every field $K$ and parameter $q$, the literal Kronecker square of the Coppersmith--Winograd tensor is the double finite sum of all ordered pairs of literal CW monomials, combined by the mode-wise interchange map. This parameter-uniform identity caches the first source-expansion step used in fourth-power arguments.
-- source:
--   D. Coppersmith and S. Winograd, Matrix multiplication via arithmetic progressions, J. Symbolic Computation 9 (1990); A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5.

import Definitions.Def_mme_CW_fourth_literal_support_words

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_CW_square_tensor_eq_sum_literal_terms
    (K : Type u) [Field K] (q : ℕ) :
    MME.interchange (MME.CWTensor K q) (MME.CWTensor K q) =
      ∑ t₂ : MME.StothersFourth.CWLiteralTerm q,
      ∑ t₁ : MME.StothersFourth.CWLiteralTerm q,
        MME.interchange
          (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
          (MME.StothersFourth.cwLiteralTermMonomial K q t₂) := by
  sorry
