-- Prove2me | Theorems.Thm_exists_uniform_norm_crouzeixPolynomialScalarCompanion_le_infDist
-- name    : exists_uniform_norm_crouzeixPolynomialScalarCompanion_le_infDist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:42:08.834794+00:00
-- url     : https://prove2.me/theorems/25c8768b-3d0b-5d85-8d38-92439703d141
-- title:
--   exists uniform norm crouzeix Polynomial Scalar Companion le inf Dist: exists uniform norm crouzeix Polynomial Scalar Companion le inf Dist
-- statement:
--   One nonnegative constant depending only on the smooth Jordan domain
--   controls the scalar companions of every polynomial away from the frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L176-L188
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L176-L188

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real

theorem exists_uniform_norm_crouzeixPolynomialScalarCompanion_le_infDist
    (Omega : SmoothJordanDomain) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (p : Polynomial ℂ) (z : ℂ),
      z ∉ frontier Omega.carrier →
      ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (2 * Real.pi *
            ((D * polynomialSupNorm p (frontier Omega.carrier)) *
              (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by sorry
