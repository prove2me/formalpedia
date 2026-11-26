-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
-- name    : crouzeixPolynomialScalarCompanion_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:58.201268+00:00
-- url     : https://prove2.me/theorems/ff603866-25af-5fe1-9bd2-7f17f8e891fc
-- title:
--   crouzeix Polynomial Scalar Companion zero: crouzeix Polynomial Scalar Companion zero
-- statement:
--   The scalar companion of the zero polynomial vanishes identically.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L80-L84
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L80-L84

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanion_zero
    (Omega : SmoothJordanDomain) (z : ℂ) :
    crouzeixPolynomialScalarCompanion Omega 0 z = 0 := by sorry
