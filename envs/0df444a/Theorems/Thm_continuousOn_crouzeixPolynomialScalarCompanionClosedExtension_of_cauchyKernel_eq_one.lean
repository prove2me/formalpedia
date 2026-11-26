-- Prove2me | Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one
-- name    : continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:39.443855+00:00
-- url     : https://prove2.me/theorems/fa40541f-d61d-42f2-b257-97e1a5867a29
-- title:
--   continuous On crouzeix Polynomial Scalar Companion Closed Extension of cauchy Kernel eq one: continuous On crouzeix Polynomial Scalar Companion Closed Extension of cauchy Kernel eq one
-- statement:
--   Winding normalization alone makes the canonical scalar-companion
--   extension continuous on the closure.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1632-L1646
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1632-L1646

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by sorry
