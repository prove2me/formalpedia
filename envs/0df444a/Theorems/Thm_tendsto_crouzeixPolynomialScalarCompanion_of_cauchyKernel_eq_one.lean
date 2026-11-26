-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_cauchyKernel_eq_one
-- name    : tendsto_crouzeixPolynomialScalarCompanion_of_cauchyKernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:23.228202+00:00
-- url     : https://prove2.me/theorems/8fc61dfd-15ea-4fd7-9abb-317945eb75f3
-- title:
--   tendsto crouzeix Polynomial Scalar Companion of cauchy Kernel eq one: tendsto crouzeix Polynomial Scalar Companion of cauchy Kernel eq one
-- statement:
--   Winding normalization alone gives the unrestricted full Plemelj limit
--   from the carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1616-L1628
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1616-L1628

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanion_of_cauchyKernel_eq_one
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by sorry
