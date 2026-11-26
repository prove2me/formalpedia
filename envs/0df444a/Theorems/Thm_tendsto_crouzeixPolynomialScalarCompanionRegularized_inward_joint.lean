-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_joint
-- name    : tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:55.635396+00:00
-- url     : https://prove2.me/theorems/251a9cae-29a8-5f17-8db9-2496461d80fa
-- title:
--   tendsto crouzeix Polynomial Scalar Companion Regularized inward joint: tendsto crouzeix Polynomial Scalar Companion Regularized inward joint
-- statement:
--   Combining joint decay of the radial error with continuity of the moving
--   self-value gives the full joint radial Plemelj limit.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1273-L1309
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1273-L1309

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanionRegularized_inward_joint
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (fun x : ℝ × ℂ =>
        crouzeixPolynomialScalarCompanionRegularized Omega p x.2
          (smoothJordanInwardPoint c x.2 x.1))
      (nhdsWithin (0, xi)
        (Ioc (0 : ℝ) 1 ×ˢ frontier Omega.carrier))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by sorry
