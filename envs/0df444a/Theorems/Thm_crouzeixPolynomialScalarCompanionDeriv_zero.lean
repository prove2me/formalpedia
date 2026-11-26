-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
-- name    : crouzeixPolynomialScalarCompanionDeriv_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:35:05.761044+00:00
-- url     : https://prove2.me/theorems/801cd391-e7c3-4374-b752-25ff8e89bb5e
-- title:
--   crouzeix Polynomial Scalar Companion Deriv zero: crouzeix Polynomial Scalar Companion Deriv zero
-- statement:
--   The derivative integral for the zero polynomial vanishes identically.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L109-L114
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L109-L114

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionDeriv_zero
    (Omega : SmoothJordanDomain) (z : ℂ) :
    crouzeixPolynomialScalarCompanionDeriv Omega 0 z = 0 := by sorry
