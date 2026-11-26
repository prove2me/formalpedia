-- Prove2me | Theorems.Thm_contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
-- name    : contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:58:21.393409+00:00
-- url     : https://prove2.me/theorems/1fc77f70-d83b-5b4c-b802-8004418d997a
-- title:
--   contour Integrable crouzeix Polynomial Boundary Phase Transform: contour Integrable crouzeix Polynomial Boundary Phase Transform
-- statement:
--   The phase-weighted contour is genuinely integrable, including at its
--   base point on the trace.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L170-L195
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemeljBound.lean#L170-L195

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) :
    ContourIntegrable
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma q) *
          (sigma - xi)⁻¹)
      Omega.boundaryParam := by sorry
