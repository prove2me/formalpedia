-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation
-- name    : norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:13.328298+00:00
-- url     : https://prove2.me/theorems/2ba68b86-c202-50e0-849d-b30dadc55584
-- title:
--   norm crouzeix Polynomial Scalar Companion le of boundary separation: norm crouzeix Polynomial Scalar Companion le of boundary separation
-- statement:
--   If every point on the parametrized frontier is at least `delta` away
--   from `z`, a numerator bound `C` gives the expected `C / delta` estimate for
--   the normalized scalar Cauchy companion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L92-L119
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L92-L119

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {delta C : ℝ}
    (hdelta : 0 < delta) (hC_nonneg : 0 ≤ C)
    (hC : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C)
    (hsep : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      delta ≤ ‖Omega.boundaryParam t - z‖) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi * (C * delta⁻¹)) := by sorry
