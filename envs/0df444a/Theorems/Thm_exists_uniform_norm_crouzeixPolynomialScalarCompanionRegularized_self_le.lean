-- Prove2me | Theorems.Thm_exists_uniform_norm_crouzeixPolynomialScalarCompanionRegularized_self_le
-- name    : exists_uniform_norm_crouzeixPolynomialScalarCompanionRegularized_self_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:43:28.455081+00:00
-- url     : https://prove2.me/theorems/ac71eb11-8607-44cb-b6cf-611ac045a3fe
-- title:
--   exists uniform norm crouzeix Polynomial Scalar Companion Regularized self le: exists uniform norm crouzeix Polynomial Scalar Companion Regularized self le
-- statement:
--   One nonnegative constant depending only on the smooth Jordan domain
--   controls every regularized self-value.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L442-L455
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L442-L455

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem exists_uniform_norm_crouzeixPolynomialScalarCompanionRegularized_self_le
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (xi : ℂ),
      ‖crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm
              (p /ₘ (Polynomial.X - Polynomial.C xi))
              (frontier Omega.carrier))) := by sorry
