-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_inward
-- name    : tendsto_crouzeixPolynomialScalarCompanion_inward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:43.442279+00:00
-- url     : https://prove2.me/theorems/6289bf55-39cb-5f53-9a4b-5f8dc88205c8
-- title:
--   tendsto crouzeix Polynomial Scalar Companion inward: tendsto crouzeix Polynomial Scalar Companion inward
-- statement:
--   When the scalar winding kernel is normalized to one in the carrier, the
--   full scalar companion converges along every inward chord to the explicit
--   Plemelj boundary value.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L901-L937
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L901-L937

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanion_inward
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun r : ℝ ↦ crouzeixPolynomialScalarCompanion Omega p
        (smoothJordanInwardPoint c xi r))
      (nhdsWithin 0 (Ioc (0 : ℝ) 1))
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by sorry
