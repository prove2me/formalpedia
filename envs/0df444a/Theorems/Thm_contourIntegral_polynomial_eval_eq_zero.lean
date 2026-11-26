-- Prove2me | Theorems.Thm_contourIntegral_polynomial_eval_eq_zero
-- name    : contourIntegral_polynomial_eval_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:06.513077+00:00
-- url     : https://prove2.me/theorems/28b7b12d-3d88-42bc-90ca-a5b74da4e234
-- title:
--   contour Integral polynomial eval eq zero: contour Integral polynomial eval eq zero
-- statement:
--   The contour integral of a complex polynomial vanishes on every smooth
--   closed boundary.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L177-L191
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasure.lean#L177-L191

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real

theorem contourIntegral_polynomial_eval_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    contourIntegral (fun z => Polynomial.eval z p) Omega.boundaryParam = 0 := by sorry
