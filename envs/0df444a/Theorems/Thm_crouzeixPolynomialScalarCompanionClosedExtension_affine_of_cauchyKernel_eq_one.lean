-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:47:49.126609+00:00
-- url     : https://prove2.me/theorems/2cf854fc-0d88-4ccc-b452-7194189285fc
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension affine of cauchy Kernel eq one: crouzeix Polynomial Scalar Companion Closed Extension affine of cauchy Kernel eq one
-- statement:
--   The canonical closed companion obeys the full conjugate-affine law under
--   winding normalization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1927-L1942
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1927-L1942

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_affine_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (a b : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (a • p + Polynomial.C b) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        star b := by sorry
