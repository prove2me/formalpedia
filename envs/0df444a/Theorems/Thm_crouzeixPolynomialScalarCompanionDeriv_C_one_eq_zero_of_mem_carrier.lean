-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier
-- name    : crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:16.32459+00:00
-- url     : https://prove2.me/theorems/b2bfcf1a-2d90-52bb-905f-99eecbd2e090
-- title:
--   crouzeix Polynomial Scalar Companion Deriv C one eq zero of mem carrier: crouzeix Polynomial Scalar Companion Deriv C one eq zero of mem carrier
-- statement:
--   The constant-data scalar companion has zero derivative at every carrier
--   point.  Its inverse-square derivative kernel has the explicit primitive
--   `-(sigma - z)⁻¹` as a function of the contour variable.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L38-L79
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L38-L79

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionDeriv_C_one_eq_zero_of_mem_carrier
    (Omega : SmoothJordanDomain) {z : ℂ} (hz : z ∈ Omega.carrier) :
    crouzeixPolynomialScalarCompanionDeriv Omega (Polynomial.C 1) z = 0 := by sorry
