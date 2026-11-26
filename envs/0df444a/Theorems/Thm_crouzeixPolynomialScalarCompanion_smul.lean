-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanion_smul
-- name    : crouzeixPolynomialScalarCompanion_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:08.545368+00:00
-- url     : https://prove2.me/theorems/f444ac03-47b5-465e-a809-f42c77543b89
-- title:
--   crouzeix Polynomial Scalar Companion smul: crouzeix Polynomial Scalar Companion smul
-- statement:
--   The scalar companion is conjugate-homogeneous in its polynomial
--   argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L63-L77
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanion.lean#L63-L77

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanion_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (z : ℂ) :
    crouzeixPolynomialScalarCompanion Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanion Omega p z := by sorry
