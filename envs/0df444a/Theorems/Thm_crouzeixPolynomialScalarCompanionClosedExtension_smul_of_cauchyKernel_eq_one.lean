-- Prove2me | Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
-- name    : crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:16.391685+00:00
-- url     : https://prove2.me/theorems/39c47674-9e21-4def-b76f-33c1b4ae775b
-- title:
--   crouzeix Polynomial Scalar Companion Closed Extension smul of cauchy Kernel eq one: crouzeix Polynomial Scalar Companion Closed Extension smul of cauchy Kernel eq one
-- statement:
--   Winding normalization alone makes the canonical closed companion
--   conjugate-homogeneous on the closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1791-L1802
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1791-L1802

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by sorry
