-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_of_cauchyKernel_eq_one
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_add_of_cauchyKernel_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:45:16.416722+00:00
-- url     : https://prove2.me/theorems/85d14794-2ee3-4299-81af-0e87d300fd1b
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension add of cauchy Kernel eq one: crouzeix Polynomial Scalar Companion Closed Extension add of cauchy Kernel eq one
-- statement:
--   Winding normalization alone makes the canonical closed companion
--   additive on the closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1775-L1787
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1775-L1787

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_add_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by sorry
