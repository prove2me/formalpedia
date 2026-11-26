-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_inward
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_inward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:37.187429+00:00
-- url     : https://prove2.me/theorems/9ea69cab-4573-5af7-83a7-811cdf7a7cf4
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized inward: tendsto crouzeix Polynomial Scalar Companion Regularized inward
-- statement:
--   The regularized scalar companion converges to its self-integral along
--   every inward chord from a frontier point to an interior center.  The proof is
--   an ordinary dominated-convergence argument using the preceding geometric
--   majorant; unlike full unrestricted Plemelj continuity, it requires no local
--   chart or curvature estimate.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L694-L896
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L694-L896

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_inward
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun r : ℝ ↦ crouzeixPolynomialScalarCompanionRegularized
        Omega p xi (smoothJordanInwardPoint c xi r))
      (nhdsWithin 0 (Ioc (0 : ℝ) 1))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by sorry
