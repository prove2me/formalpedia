-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_infDist_mul_polynomialSupNorm
-- name    : norm_crouzeixPolynomialScalarCompanion_le_infDist_mul_polynomialSupNorm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:57:52.364798+00:00
-- url     : https://prove2.me/theorems/0208e90f-c1ce-57b1-acbe-438cd45c06f8
-- title:
--   norm crouzeix Polynomial Scalar Companion le inf Dist mul polynomial Sup Norm: norm crouzeix Polynomial Scalar Companion le inf Dist mul polynomial Sup Norm
-- statement:
--   A domain-only boundary-speed bound and the canonical frontier polynomial
--   sup norm give a fully uniform inverse-distance estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L153-L172
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L153-L172

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_le_infDist_mul_polynomialSupNorm
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D)
    (hz : z ∉ frontier Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          ((D * polynomialSupNorm p (frontier Omega.carrier)) *
            (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by sorry
