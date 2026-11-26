-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform
-- name    : norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:53.297917+00:00
-- url     : https://prove2.me/theorems/bc3fe796-a501-4a89-a242-ba8ed7b051d8
-- title:
--   norm crouzeix Polynomial Scalar Companion le of boundary Phase Transform: norm crouzeix Polynomial Scalar Companion le of boundary Phase Transform
-- statement:
--   The exact remaining sharp frontier inequality for the lower-degree phase
--   transform implies the sharp scalar-companion contraction in the carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L282-L308
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L282-L308

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_le_of_boundaryPhaseTransform
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Filter.Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
