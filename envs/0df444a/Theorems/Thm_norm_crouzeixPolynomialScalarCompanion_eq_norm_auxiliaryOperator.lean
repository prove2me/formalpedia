-- Prove2me | Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_eq_norm_auxiliaryOperator
-- name    : norm_crouzeixPolynomialScalarCompanion_eq_norm_auxiliaryOperator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:03:29.202498+00:00
-- url     : https://prove2.me/theorems/07bd612e-d5a5-5dba-8386-4ec892e64540
-- title:
--   norm crouzeix Polynomial Scalar Companion eq norm auxiliary Operator: norm crouzeix Polynomial Scalar Companion eq norm auxiliary Operator
-- statement:
--   Scalarization is isometric: the norm of the scalar companion at an
--   interior point equals the operator norm of the corresponding one-dimensional
--   polynomial auxiliary operator.  Hence an auxiliary-operator estimate in the
--   scalar model transfers to the analytic companion with no loss.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L284-L292
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L284-L292

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem norm_crouzeixPolynomialScalarCompanion_eq_norm_auxiliaryOperator
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ =
      ‖crouzeixPolynomialAuxiliaryOperator
        (ContinuousLinearMap.toSpanSingleton ℂ z) Omega p‖ := by sorry
