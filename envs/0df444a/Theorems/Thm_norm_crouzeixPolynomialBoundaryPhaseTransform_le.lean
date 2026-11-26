-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialBoundaryPhaseTransform_le
-- name    : norm_crouzeixPolynomialBoundaryPhaseTransform_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:58:48.061631+00:00
-- url     : https://prove2.me/theorems/df70c880-74b7-5ed0-9f52-4a976d655b0d
-- title:
--   norm crouzeix Polynomial Boundary Phase Transform le: norm crouzeix Polynomial Boundary Phase Transform le
-- statement:
--   A boundary-speed bound controls the named phase transform directly by
--   the frontier sup norm of its polynomial argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L420-L438
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L420-L438

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem norm_crouzeixPolynomialBoundaryPhaseTransform_le
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D) :
    ‖crouzeixPolynomialBoundaryPhaseTransform Omega xi q‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (D * polynomialSupNorm q (frontier Omega.carrier))) := by sorry
