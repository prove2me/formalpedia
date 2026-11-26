-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_infDist
-- name    : norm_crouzeixPolynomialScalarCompanion_le_infDist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:54:11.687225+00:00
-- url     : https://prove2.me/theorems/44599595-59c5-5fc0-af11-d1fbacc7fd57
-- title:
--   norm crouzeix Polynomial Scalar Companion le inf Dist: norm crouzeix Polynomial Scalar Companion le inf Dist
-- statement:
--   Away from the frontier, the preceding estimate specializes to the
--   minimal distance from `z` to that frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L123-L149
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L123-L149

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_le_infDist
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C)
    (hz : z ∉ frontier Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (C * (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by sorry
