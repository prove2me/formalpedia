-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform_radial
-- name    : norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform_radial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:47:42.878298+00:00
-- url     : https://prove2.me/theorems/7f95a0ef-f4ec-4fdf-9333-1ad1092829f8
-- title:
--   norm crouzeix Polynomial Scalar Companion le of boundary Phase Transform radial: norm crouzeix Polynomial Scalar Companion le of boundary Phase Transform radial
-- statement:
--   On a bounded normalized carrier, the sharp boundary-phase inequality
--   immediately controls the scalar companion in the interior.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1823-L1845
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1823-L1845

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform_radial
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
