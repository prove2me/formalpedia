-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
-- name    : norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:58:46.700188+00:00
-- url     : https://prove2.me/theorems/8b8fb364-d22c-44ad-ac5b-4b08481c60ef
-- title:
--   norm crouzeix Polynomial Scalar Companion Closed Extension le of boundary Phase Transform: norm crouzeix Polynomial Scalar Companion Closed Extension le of boundary Phase Transform
-- statement:
--   Under the same sharp phase inequality, the canonical Plemelj extension
--   is contractive on the entire closed domain.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L312-L344
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L312-L344

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
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
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by sorry
