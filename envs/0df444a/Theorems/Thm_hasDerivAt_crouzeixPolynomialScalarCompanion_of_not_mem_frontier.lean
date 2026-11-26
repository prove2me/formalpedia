-- Prove2me | Theorems.Thm_hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
-- name    : hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:01.76957+00:00
-- url     : https://prove2.me/theorems/af9ead90-85ee-5cca-8751-c0f97c13b2d3
-- title:
--   has Deriv At crouzeix Polynomial Scalar Companion of not mem frontier: has Deriv At crouzeix Polynomial Scalar Companion of not mem frontier
-- statement:
--   At every point away from the smooth Jordan frontier, the scalar companion
--   has the expected inverse-square Cauchy-kernel derivative.  This simultaneously
--   constructs its interior and exterior holomorphic branches.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L297-L448
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L297-L448

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    HasDerivAt (crouzeixPolynomialScalarCompanion Omega p)
      (crouzeixPolynomialScalarCompanionDeriv Omega p z) z := by sorry
