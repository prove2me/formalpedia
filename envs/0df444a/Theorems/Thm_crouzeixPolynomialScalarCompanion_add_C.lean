-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanion_add_C
-- name    : crouzeixPolynomialScalarCompanion_add_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:53.814795+00:00
-- url     : https://prove2.me/theorems/36803018-47c5-4a43-a980-92acc71d8000
-- title:
--   crouzeix Polynomial Scalar Companion add C: crouzeix Polynomial Scalar Companion add C
-- statement:
--   Away from the frontier, adding a constant polynomial shifts the full
--   companion by the conjugate constant times the normalized winding kernel.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L527-L539
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPlemelj.lean#L527-L539

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanion_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega (p + Polynomial.C a) z =
      star a * crouzeixScalarCauchyKernel Omega z +
        crouzeixPolynomialScalarCompanion Omega p z := by sorry
