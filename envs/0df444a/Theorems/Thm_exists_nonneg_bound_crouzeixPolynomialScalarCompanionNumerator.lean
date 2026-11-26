-- Prove2me | Theorems.Thm_exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator
-- name    : exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:12.345644+00:00
-- url     : https://prove2.me/theorems/ce6755ae-84fa-5b3a-8c6c-b1fa1a20f7db
-- title:
--   exists nonneg bound crouzeix Polynomial Scalar Companion Numerator: exists nonneg bound crouzeix Polynomial Scalar Companion Numerator
-- statement:
--   The numerator of the parameterized scalar Cauchy companion is uniformly
--   bounded on the compact interval `[0, 2 * pi]`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L60-L87
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L60-L87

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real

theorem exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C := by sorry
