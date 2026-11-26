-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:23.572826+00:00
-- url     : https://prove2.me/theorems/5ffe214a-030f-41cd-bdcf-429d77f2937d
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension C of cauchy Kernel eq one: crouzeix Polynomial Scalar Companion Closed Extension C of cauchy Kernel eq one
-- statement:
--   Winding normalization alone makes the canonical closed companion of a
--   constant polynomial equal to the conjugate constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2119-L2130
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2119-L2130

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (Polynomial.C a) z = star a := by sorry
