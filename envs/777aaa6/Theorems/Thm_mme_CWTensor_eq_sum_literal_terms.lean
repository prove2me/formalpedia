-- Prove2me | Theorems.Thm_mme_CWTensor_eq_sum_literal_terms
-- name    : mme_CWTensor_eq_sum_literal_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:40:24.980304+00:00
-- url     : https://prove2.me/theorems/5b66c8c1-0b73-43c4-b32e-4c376135cb9f
-- title:
--   Literal finite-sum expansion of the Coppersmith--Winograd tensor
-- statement:
--   For every field $K$ and parameter $q$, the Coppersmith--Winograd tensor is the finite sum of its $3q+3$ literal monomials: three ordinary terms for each middle coordinate and three exceptional terms containing a top coordinate. This parameter-uniform expansion is the source-level starting point for literal square and fourth-power grading arguments.
-- source:
--   D. Coppersmith and S. Winograd, Matrix multiplication via arithmetic progressions, J. Symbolic Computation 9 (1990); A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 2.

import Definitions.Def_mme_CW_fourth_literal_support_words

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_CWTensor_eq_sum_literal_terms
    (K : Type u) [Field K] (q : ℕ) :
    MME.CWTensor K q =
      ∑ t : MME.StothersFourth.CWLiteralTerm q,
        MME.StothersFourth.cwLiteralTermMonomial K q t := by
  sorry
