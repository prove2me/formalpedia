-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
-- name    : norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:59:11.063897+00:00
-- url     : https://prove2.me/theorems/2c27e0dd-4923-48ef-a521-eca8c225fe41
-- title:
--   norm crouzeix Polynomial Scalar Companion Boundary Value le: norm crouzeix Polynomial Scalar Companion Boundary Value le
-- statement:
--   At a frontier point, the explicit Plemelj value is bounded by the
--   polynomial frontier sup norm plus the divided-difference remainder bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L473-L505
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L473-L505

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanionBoundaryValue_le
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ frontier Omega.carrier) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) +
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            (D * polynomialSupNorm
              (p /ₘ (Polynomial.X - Polynomial.C xi))
              (frontier Omega.carrier))) := by sorry
