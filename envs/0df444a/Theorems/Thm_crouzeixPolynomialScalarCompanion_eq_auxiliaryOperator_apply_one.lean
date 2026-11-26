-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
-- name    : crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:36:07.30394+00:00
-- url     : https://prove2.me/theorems/93202a8e-e1d8-4a88-b026-dcf041758f57
-- title:
--   crouzeix Polynomial Scalar Companion eq auxiliary Operator apply one: crouzeix Polynomial Scalar Companion eq auxiliary Operator apply one
-- statement:
--   At any interior point, the scalar Crouzeix companion is the value at `1`
--   of the polynomial auxiliary operator for one-dimensional multiplication by
--   that point.  Thus the scalar analytic construction is exactly the
--   one-dimensional scalarization of the operator contour construction, for an
--   arbitrary smooth Jordan domain.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L189-L264
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L189-L264

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega p z =
      crouzeixPolynomialAuxiliaryOperator
        (ContinuousLinearMap.toSpanSingleton ℂ z) Omega p 1 := by sorry
