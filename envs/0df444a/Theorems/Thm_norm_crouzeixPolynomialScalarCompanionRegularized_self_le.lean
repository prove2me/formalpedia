-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanionRegularized_self_le
-- name    : norm_crouzeixPolynomialScalarCompanionRegularized_self_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:49.995798+00:00
-- url     : https://prove2.me/theorems/3cdebc3a-21cb-4a1c-ad5e-d18235270d25
-- title:
--   norm crouzeix Polynomial Scalar Companion Regularized self le: norm crouzeix Polynomial Scalar Companion Regularized self le
-- statement:
--   A boundary-speed bound controls the regularized self-value by the
--   frontier sup norm of the divided-difference polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L348-L416
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L348-L416

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanionRegularized_self_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialScalarCompanionRegularized Omega p xi xi‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (D * polynomialSupNorm
            (p /ₘ (Polynomial.X - Polynomial.C xi))
            (frontier Omega.carrier))) := by sorry
