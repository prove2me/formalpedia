-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_smul
-- name    : crouzeixPolynomialScalarCompanionDeriv_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:54.574798+00:00
-- url     : https://prove2.me/theorems/85b5aea0-070f-5f2a-8f1b-ad96210e4a74
-- title:
--   crouzeix Polynomial Scalar Companion Deriv smul: crouzeix Polynomial Scalar Companion Deriv smul
-- statement:
--   The derivative integral of the scalar companion is likewise
--   conjugate-homogeneous in the polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L88-L106
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L88-L106

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionDeriv_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (z : ℂ) :
    crouzeixPolynomialScalarCompanionDeriv Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionDeriv Omega p z := by sorry
