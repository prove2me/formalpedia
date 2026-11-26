-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
-- name    : norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:17.113652+00:00
-- url     : https://prove2.me/theorems/0f319708-dc98-569c-af04-dad269541de2
-- title:
--   norm crouzeix Polynomial Scalar Companion Closed Extension le of boundary Phase Transform radial: norm crouzeix Polynomial Scalar Companion Closed Extension le of boundary Phase Transform radial
-- statement:
--   The same sharp boundary-phase inequality controls the canonical closed
--   extension on the entire closure of a bounded normalized carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1849-L1872
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1849-L1872

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform_radial
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
