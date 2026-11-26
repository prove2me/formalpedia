-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_inward_joint
-- name    : tendsto_crouzeixPolynomialScalarCompanion_inward_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:13.660452+00:00
-- url     : https://prove2.me/theorems/cce6891b-9aaa-4d3a-b4a6-82639baf8e51
-- title:
--   tendsto crouzeix Polynomial Scalar Companion inward joint: tendsto crouzeix Polynomial Scalar Companion inward joint
-- statement:
--   With normalized winding kernel, the full companion has the corresponding
--   joint radial limit while its frontier endpoint moves.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1313-L1355
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1313-L1355

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanion_inward_joint
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {c xi : ℂ} (hc : c ∈ Omega.carrier)
    (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanion Omega p
          (smoothJordanInwardPoint c x.2 x.1))
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by sorry
