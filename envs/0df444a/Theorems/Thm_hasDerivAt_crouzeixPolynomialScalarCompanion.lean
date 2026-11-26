-- Prove2me | Theorems.Thm_hasDerivAt_crouzeixPolynomialScalarCompanion
-- name    : hasDerivAt_crouzeixPolynomialScalarCompanion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:35:39.112633+00:00
-- url     : https://prove2.me/theorems/e399f3ce-00ff-4e1e-aaa9-9160014dbbfe
-- title:
--   has Deriv At crouzeix Polynomial Scalar Companion: has Deriv At crouzeix Polynomial Scalar Companion
-- statement:
--   At every point in the smooth Jordan carrier, the scalar companion has the
--   expected inverse-square Cauchy-kernel derivative.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L452-L462
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L452-L462

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem hasDerivAt_crouzeixPolynomialScalarCompanion
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    HasDerivAt (crouzeixPolynomialScalarCompanion Omega p)
      (crouzeixPolynomialScalarCompanionDeriv Omega p z) z := by sorry
